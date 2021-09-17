//===- COFFImportFile.cpp - COFF short import file implementation ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the writeImportLibrary function.
//
//===----------------------------------------------------------------------===//

#include "llvm/Object/COFFImportFile.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Object/Archive.h"
#include "llvm/Object/ArchiveWriter.h"
#include "llvm/Object/COFF.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/StringSaver.h"

#include <cstdint>
#include <string>
#include <vector>

using namespace llvm::COFF;
using namespace llvm::object;
using namespace llvm;

namespace llvm {
namespace object {

static bool is32bit(MachineTypes Machine) {
  switch (Machine) {
  default:
    llvm_unreachable("unsupported machine");
  case IMAGE_FILE_MACHINE_ARM64:
  case IMAGE_FILE_MACHINE_AMD64:
    return false;
  case IMAGE_FILE_MACHINE_ARMNT:
  case IMAGE_FILE_MACHINE_I386:
    return true;
  }
}

static uint16_t getImgRelRelocation(MachineTypes Machine) {
  switch (Machine) {
  default:
    llvm_unreachable("unsupported machine");
  case IMAGE_FILE_MACHINE_AMD64:
    return IMAGE_REL_AMD64_ADDR32NB;
  case IMAGE_FILE_MACHINE_ARMNT:
    return IMAGE_REL_ARM_ADDR32NB;
  case IMAGE_FILE_MACHINE_ARM64:
    return IMAGE_REL_ARM64_ADDR32NB;
  case IMAGE_FILE_MACHINE_I386:
    return IMAGE_REL_I386_DIR32NB;
  }
}

static const uint8_t ImportThunkX86[] = {
    0xff, 0x25, 0x00, 0x00, 0x00, 0x00, 0x90, 0x90, // JMP *0x0, nop, nop
};

static const uint8_t ImportThunkARM[] = {
    0x40, 0xf2, 0x00, 0x0c, // mov.w ip, #0
    0xc0, 0xf2, 0x00, 0x0c, // mov.t ip, #0
    0xdc, 0xf8, 0x00, 0xf0, // ldr.w pc, [ip]
};

static const uint8_t ImportThunkARM64[] = {
    0x10, 0x00, 0x00, 0x90, // adrp x16, #0
    0x10, 0x02, 0x40, 0xf9, // ldr  x16, [x16]
    0x00, 0x02, 0x1f, 0xd6, // br   x16
};

static ArrayRef<uint8_t> getThunk(MachineTypes Machine) {
  switch (Machine) {
  default:
    llvm_unreachable("unsupported machine");
  case IMAGE_FILE_MACHINE_AMD64:
  case IMAGE_FILE_MACHINE_I386:
    return ArrayRef<uint8_t>(ImportThunkX86, sizeof(ImportThunkX86));
  case IMAGE_FILE_MACHINE_ARMNT:
    return ArrayRef<uint8_t>(ImportThunkARM, sizeof(ImportThunkARM));
  case IMAGE_FILE_MACHINE_ARM64:
    return ArrayRef<uint8_t>(ImportThunkARM64, sizeof(ImportThunkARM64));
  }
}

static int getThunkRelocations(MachineTypes Machine, uint16_t *Relocs,
                               size_t *Offsets) {
  switch (Machine) {
  default:
    llvm_unreachable("unsupported machine");
  case IMAGE_FILE_MACHINE_I386:
    Relocs[0] = IMAGE_REL_I386_DIR32;
    Offsets[0] = 2;
    return 1;
  case IMAGE_FILE_MACHINE_AMD64:
    Relocs[0] = IMAGE_REL_AMD64_REL32;
    Offsets[0] = 2;
    return 1;
  case IMAGE_FILE_MACHINE_ARMNT:
    Relocs[0] = IMAGE_REL_ARM_MOV32T;
    Offsets[0] = 0;
    return 1;
  case IMAGE_FILE_MACHINE_ARM64:
    Relocs[0] = IMAGE_REL_ARM64_PAGEBASE_REL21;
    Offsets[0] = 0;
    Relocs[1] = IMAGE_REL_ARM64_PAGEOFFSET_12L;
    Offsets[1] = 4;
    return 2;
  }
}

template <class T> static void append(std::vector<uint8_t> &B, const T &Data) {
  size_t S = B.size();
  B.resize(S + sizeof(T));
  memcpy(&B[S], &Data, sizeof(T));
}

static void writeStringTable(std::vector<uint8_t> &B,
                             ArrayRef<std::string> Strings) {
  // The COFF string table consists of a 4-byte value which is the size of the
  // table, including the length field itself.  This value is followed by the
  // string content itself, which is an array of null-terminated C-style
  // strings.  The termination is important as they are referenced to by offset
  // by the symbol entity in the file format.

  size_t Pos = B.size();
  size_t Offset = B.size();

  // Skip over the length field, we will fill it in later as we will have
  // computed the length while emitting the string content itself.
  Pos += sizeof(uint32_t);

  for (const auto &S : Strings) {
    B.resize(Pos + S.length() + 1);
    strcpy(reinterpret_cast<char *>(&B[Pos]), S.c_str());
    Pos += S.length() + 1;
  }

  // Backfill the length of the table now that it has been computed.
  support::ulittle32_t Length(B.size() - Offset);
  support::endian::write32le(&B[Offset], Length);
}

static ImportNameType getNameType(StringRef Sym, StringRef ExtName,
                                  MachineTypes Machine, bool MinGW) {
  // A decorated stdcall function in MSVC is exported with the
  // type IMPORT_NAME, and the exported function name includes the
  // the leading underscore. In MinGW on the other hand, a decorated
  // stdcall function still omits the underscore (IMPORT_NAME_NOPREFIX).
  // See the comment in isDecorated in COFFModuleDefinition.cpp for more
  // details.
  if (ExtName.startswith("_") && ExtName.contains('@') && !MinGW)
    return IMPORT_NAME;
  if (Sym != ExtName)
    return IMPORT_NAME_UNDECORATE;
  if (Machine == IMAGE_FILE_MACHINE_I386 && Sym.startswith("_"))
    return IMPORT_NAME_NOPREFIX;
  return IMPORT_NAME;
}

static Expected<std::string> replace(StringRef S, StringRef From,
                                     StringRef To) {
  size_t Pos = S.find(From);

  // From and To may be mangled, but substrings in S may not.
  if (Pos == StringRef::npos && From.startswith("_") && To.startswith("_")) {
    From = From.substr(1);
    To = To.substr(1);
    Pos = S.find(From);
  }

  if (Pos == StringRef::npos) {
    return make_error<StringError>(
      StringRef(Twine(S + ": replacing '" + From +
        "' with '" + To + "' failed").str()), object_error::parse_failed);
  }

  return (Twine(S.substr(0, Pos)) + To + S.substr(Pos + From.size())).str();
}

static const std::string NullImportDescriptorSymbolName =
    "__NULL_IMPORT_DESCRIPTOR";

namespace {
// This class constructs various small object files necessary to support linking
// symbols imported from a DLL.  The contents are pretty strictly defined and
// nearly entirely static.  The details of the structures files are defined in
// WINNT.h and the PE/COFF specification.
class ObjectFactory {
  using u16 = support::ulittle16_t;
  using u32 = support::ulittle32_t;
  using u64 = support::ulittle64_t;
  MachineTypes Machine;
  BumpPtrAllocator Alloc;
  StringRef ImportName;
  StringRef Library;
  std::string ImportDescriptorSymbolName;
  std::string NullThunkSymbolName;

  std::string GnuPrefix;
  std::string TailSymbol;
  int NumFiles = 0;
  StringSaver MemberFileNames;

public:
  ObjectFactory(StringRef S, MachineTypes M)
      : Machine(M), ImportName(S), Library(S.drop_back(4)),
        ImportDescriptorSymbolName(("__IMPORT_DESCRIPTOR_" + Library).str()),
        NullThunkSymbolName(("\x7f" + Library + "_NULL_THUNK_DATA").str()),
        GnuPrefix(("d" + Library + "_").str()),
        TailSymbol(("__" + Library + "_iname").str()), MemberFileNames(Alloc) {}

  void setGnuSymbolNames() {
    ImportDescriptorSymbolName = ("_head_" + Library).str();
  }

  // Creates an Import Descriptor.  This is a small object file which contains a
  // reference to the terminators and contains the library name (entry) for the
  // import name table.  It will force the linker to construct the necessary
  // structure to import symbols from the DLL.
  NewArchiveMember createImportDescriptor(std::vector<uint8_t> &Buffer);

  NewArchiveMember createGnuHead(std::vector<uint8_t> &Buffer);

  // Creates a NULL import descriptor.  This is a small object file whcih
  // contains a NULL import descriptor.  It is used to terminate the imports
  // from a specific DLL.
  NewArchiveMember createNullImportDescriptor(std::vector<uint8_t> &Buffer);

  // Create a NULL Thunk Entry.  This is a small object file which contains a
  // NULL Import Address Table entry and a NULL Import Lookup Table Entry.  It
  // is used to terminate the IAT and ILT.
  NewArchiveMember createNullThunk(std::vector<uint8_t> &Buffer);

  NewArchiveMember createGnuTail(std::vector<uint8_t> &Buffer);

  // Create a short import file which is described in PE/COFF spec 7. Import
  // Library Format.
  NewArchiveMember createShortImport(StringRef Sym, uint16_t Ordinal,
                                     ImportType Type, ImportNameType NameType);

  NewArchiveMember createGnuIdata(StringRef Sym, StringRef ImportName,
                                  bool Data, bool Noname, uint16_t Ordinal);

  // Create a weak external file which is described in PE/COFF Aux Format 3.
  NewArchiveMember createWeakExternal(StringRef Sym, StringRef Weak, bool Imp);
};
} // namespace

NewArchiveMember
ObjectFactory::createImportDescriptor(std::vector<uint8_t> &Buffer) {
  const uint32_t NumberOfSections = 2;
  const uint32_t NumberOfSymbols = 7;
  const uint32_t NumberOfRelocations = 3;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section)) +
          // .idata$2
          sizeof(coff_import_directory_table_entry) +
          NumberOfRelocations * sizeof(coff_relocation) +
          // .idata$4
          (ImportName.size() + 1)),
      u32(NumberOfSymbols),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '2'},
       u32(0),
       u32(0),
       u32(sizeof(coff_import_directory_table_entry)),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section)),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           sizeof(coff_import_directory_table_entry)),
       u32(0),
       u16(NumberOfRelocations),
       u16(0),
       u32(IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_CNT_INITIALIZED_DATA |
           IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '6'},
       u32(0),
       u32(0),
       u32(ImportName.size() + 1),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           sizeof(coff_import_directory_table_entry) +
           NumberOfRelocations * sizeof(coff_relocation)),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(IMAGE_SCN_ALIGN_2BYTES | IMAGE_SCN_CNT_INITIALIZED_DATA |
           IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
  };
  append(Buffer, SectionTable);

  // .idata$2
  const coff_import_directory_table_entry ImportDescriptor{
      u32(0), u32(0), u32(0), u32(0), u32(0),
  };
  append(Buffer, ImportDescriptor);

  const coff_relocation RelocationTable[NumberOfRelocations] = {
      {u32(offsetof(coff_import_directory_table_entry, NameRVA)), u32(2),
       u16(getImgRelRelocation(Machine))},
      {u32(offsetof(coff_import_directory_table_entry, ImportLookupTableRVA)),
       u32(3), u16(getImgRelRelocation(Machine))},
      {u32(offsetof(coff_import_directory_table_entry, ImportAddressTableRVA)),
       u32(4), u16(getImgRelRelocation(Machine))},
  };
  append(Buffer, RelocationTable);

  // .idata$6
  auto S = Buffer.size();
  Buffer.resize(S + ImportName.size() + 1);
  memcpy(&Buffer[S], ImportName.data(), ImportName.size());
  Buffer[S + ImportName.size()] = '\0';

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(1),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '2'}},
       u32(0),
       u16(1),
       u16(0),
       IMAGE_SYM_CLASS_SECTION,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '6'}},
       u32(0),
       u16(2),
       u16(0),
       IMAGE_SYM_CLASS_STATIC,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '4'}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_SECTION,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '5'}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_SECTION,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  // TODO: Name.Offset.Offset here and in the all similar places below
  // suggests a names refactoring. Maybe StringTableOffset.Value?
  SymbolTable[0].Name.Offset.Offset =
      sizeof(uint32_t);
  SymbolTable[5].Name.Offset.Offset =
      sizeof(uint32_t) + ImportDescriptorSymbolName.length() + 1;
  SymbolTable[6].Name.Offset.Offset =
      sizeof(uint32_t) + ImportDescriptorSymbolName.length() + 1 +
      NullImportDescriptorSymbolName.length() + 1;
  append(Buffer, SymbolTable);

  // String Table
  writeStringTable(Buffer,
                   {ImportDescriptorSymbolName, NullImportDescriptorSymbolName,
                    NullThunkSymbolName});

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  return {MemoryBufferRef(F, ImportName)};
}

NewArchiveMember ObjectFactory::createGnuHead(std::vector<uint8_t> &Buffer) {
  const uint32_t NumberOfSections = 3;
  const uint32_t NumberOfSymbols = 4;
  const uint32_t NumberOfRelocations = 3;

  uint32_t VAAlign =
      is32bit(Machine) ? IMAGE_SCN_ALIGN_4BYTES : IMAGE_SCN_ALIGN_8BYTES;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section)) +
          // .idata$2
          sizeof(coff_import_directory_table_entry) +
          NumberOfRelocations * sizeof(coff_relocation)),
      u32(NumberOfSymbols),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '2'},
       u32(0),
       u32(0),
       u32(sizeof(coff_import_directory_table_entry)),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section)),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           sizeof(coff_import_directory_table_entry)),
       u32(0),
       u16(NumberOfRelocations),
       u16(0),
       u32(IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_CNT_INITIALIZED_DATA |
           IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '4'},
       u32(0),
       u32(0),
       u32(0),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           sizeof(coff_import_directory_table_entry) +
           NumberOfRelocations * sizeof(coff_relocation)),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(VAAlign | IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '5'},
       u32(0),
       u32(0),
       u32(0),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           sizeof(coff_import_directory_table_entry) +
           NumberOfRelocations * sizeof(coff_relocation)),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(VAAlign | IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
  };
  append(Buffer, SectionTable);

  // .idata$2
  const coff_import_directory_table_entry ImportDescriptor{
      u32(0), u32(0), u32(0), u32(0), u32(0),
  };
  append(Buffer, ImportDescriptor);

  const coff_relocation RelocationTable[NumberOfRelocations] = {
      {u32(offsetof(coff_import_directory_table_entry, NameRVA)), u32(3),
       u16(getImgRelRelocation(Machine))},
      {u32(offsetof(coff_import_directory_table_entry, ImportLookupTableRVA)),
       u32(1), u16(getImgRelRelocation(Machine))},
      {u32(offsetof(coff_import_directory_table_entry, ImportAddressTableRVA)),
       u32(2), u16(getImgRelRelocation(Machine))},
  };
  append(Buffer, RelocationTable);

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(1),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '4'}},
       u32(0),
       u16(2),
       u16(0),
       IMAGE_SYM_CLASS_SECTION,
       0},
      {{{'.', 'i', 'd', 'a', 't', 'a', '$', '5'}},
       u32(0),
       u16(3),
       u16(0),
       IMAGE_SYM_CLASS_SECTION,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  SymbolTable[0].Name.Offset.Offset = sizeof(uint32_t);
  SymbolTable[3].Name.Offset.Offset =
      sizeof(uint32_t) + ImportDescriptorSymbolName.length() + 1;
  append(Buffer, SymbolTable);

  // String Table
  writeStringTable(Buffer, {ImportDescriptorSymbolName, TailSymbol});

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  return {MemoryBufferRef(F, MemberFileNames.save(GnuPrefix + "h.o"))};
}

NewArchiveMember
ObjectFactory::createNullImportDescriptor(std::vector<uint8_t> &Buffer) {
  const uint32_t NumberOfSections = 1;
  const uint32_t NumberOfSymbols = 1;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section)) +
          // .idata$3
          sizeof(coff_import_directory_table_entry)),
      u32(NumberOfSymbols),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '3'},
       u32(0),
       u32(0),
       u32(sizeof(coff_import_directory_table_entry)),
       u32(sizeof(coff_file_header) +
           (NumberOfSections * sizeof(coff_section))),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_CNT_INITIALIZED_DATA |
           IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
  };
  append(Buffer, SectionTable);

  // .idata$3
  const coff_import_directory_table_entry ImportDescriptor{
      u32(0), u32(0), u32(0), u32(0), u32(0),
  };
  append(Buffer, ImportDescriptor);

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(1),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  SymbolTable[0].Name.Offset.Offset = sizeof(uint32_t);
  append(Buffer, SymbolTable);

  // String Table
  writeStringTable(Buffer, {NullImportDescriptorSymbolName});

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  return {MemoryBufferRef(F, ImportName)};
}

NewArchiveMember ObjectFactory::createNullThunk(std::vector<uint8_t> &Buffer) {
  const uint32_t NumberOfSections = 2;
  const uint32_t NumberOfSymbols = 1;
  uint32_t VASize = is32bit(Machine) ? 4 : 8;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section)) +
          // .idata$5
          VASize +
          // .idata$4
          VASize),
      u32(NumberOfSymbols),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '5'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section)),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32((is32bit(Machine) ? IMAGE_SCN_ALIGN_4BYTES
                             : IMAGE_SCN_ALIGN_8BYTES) |
           IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '4'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           VASize),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32((is32bit(Machine) ? IMAGE_SCN_ALIGN_4BYTES
                             : IMAGE_SCN_ALIGN_8BYTES) |
           IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
  };
  append(Buffer, SectionTable);

  // .idata$5, ILT
  append(Buffer, u32(0));
  if (!is32bit(Machine))
    append(Buffer, u32(0));

  // .idata$4, IAT
  append(Buffer, u32(0));
  if (!is32bit(Machine))
    append(Buffer, u32(0));

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(1),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  SymbolTable[0].Name.Offset.Offset = sizeof(uint32_t);
  append(Buffer, SymbolTable);

  // String Table
  writeStringTable(Buffer, {NullThunkSymbolName});

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  return {MemoryBufferRef{F, ImportName}};
}

NewArchiveMember ObjectFactory::createGnuTail(std::vector<uint8_t> &Buffer) {
  const uint32_t NumberOfSections = 3;
  const uint32_t NumberOfSymbols = 1;
  uint32_t VASize = is32bit(Machine) ? 4 : 8;
  uint32_t VAAlign =
      is32bit(Machine) ? IMAGE_SCN_ALIGN_4BYTES : IMAGE_SCN_ALIGN_8BYTES;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section)) +
          // .idata$5
          VASize +
          // .idata$4
          VASize +
          // .idata$7
          ImportName.size() + 1),
      u32(NumberOfSymbols),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '4'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section)),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(VAAlign | IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '5'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           VASize),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(VAAlign | IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ |
           IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '7'},
       u32(0),
       u32(0),
       u32(ImportName.size() + 1),
       u32(sizeof(coff_file_header) + NumberOfSections * sizeof(coff_section) +
           2 * VASize),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(IMAGE_SCN_ALIGN_2BYTES | IMAGE_SCN_CNT_INITIALIZED_DATA |
           IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
  };
  append(Buffer, SectionTable);

  // .idata$4, IAT
  append(Buffer, u32(0));
  if (!is32bit(Machine))
    append(Buffer, u32(0));

  // .idata$5, ILT
  append(Buffer, u32(0));
  if (!is32bit(Machine))
    append(Buffer, u32(0));

  // .idata$7
  auto S = Buffer.size();
  Buffer.resize(S + ImportName.size() + 1);
  memcpy(&Buffer[S], ImportName.data(), ImportName.size());
  Buffer[S + ImportName.size()] = '\0';

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(3),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  SymbolTable[0].Name.Offset.Offset = sizeof(uint32_t);
  append(Buffer, SymbolTable);

  // String Table
  writeStringTable(Buffer, {TailSymbol});

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  return {MemoryBufferRef{F, MemberFileNames.save(GnuPrefix + "t.o")}};
}

NewArchiveMember ObjectFactory::createShortImport(StringRef Sym,
                                                  uint16_t Ordinal,
                                                  ImportType ImportType,
                                                  ImportNameType NameType) {
  size_t ImpSize = ImportName.size() + Sym.size() + 2; // +2 for NULs
  size_t Size = sizeof(coff_import_header) + ImpSize;
  char *Buf = Alloc.Allocate<char>(Size);
  memset(Buf, 0, Size);
  char *P = Buf;

  // Write short import library.
  auto *Imp = reinterpret_cast<coff_import_header *>(P);
  P += sizeof(*Imp);
  Imp->Sig2 = 0xFFFF;
  Imp->Machine = Machine;
  Imp->SizeOfData = ImpSize;
  if (Ordinal > 0)
    Imp->OrdinalHint = Ordinal;
  Imp->TypeInfo = (NameType << 2) | ImportType;

  // Write symbol name and DLL name.
  memcpy(P, Sym.data(), Sym.size());
  P += Sym.size() + 1;
  memcpy(P, ImportName.data(), ImportName.size());

  return {MemoryBufferRef(StringRef(Buf, Size), ImportName)};
}

NewArchiveMember ObjectFactory::createGnuIdata(StringRef Sym,
                                               StringRef ImportName, bool Data,
                                               bool Noname, uint16_t Ordinal) {
  uint32_t VASize = is32bit(Machine) ? 4 : 8;
  uint32_t VAAlign =
      is32bit(Machine) ? IMAGE_SCN_ALIGN_4BYTES : IMAGE_SCN_ALIGN_8BYTES;

  ArrayRef<uint8_t> Thunk = getThunk(Machine);
  uint16_t ThunkRelocationTypes[2];
  size_t ThunkRelocationOffsets[2];
  int NumThunkRelocations = getThunkRelocations(Machine, ThunkRelocationTypes,
                                                ThunkRelocationOffsets);

  std::vector<uint8_t> Buffer;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(0),
      u32(0),
      u32(0),
      u32(0),
      u16(0),
      u16(is32bit(Machine) ? IMAGE_FILE_32BIT_MACHINE : C_Invalid),
  };

  // Section Header Table
  const uint32_t MaxNumberOfSections = 5;
  coff_section SectionTable[MaxNumberOfSections] = {
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '4'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(0), // PointerToRawData
       u32(0), // PointerToRelocations
       u32(0),
       u16(Noname ? 0 : 1), // NumberOfRelocations
       u16(0),
       u32(VAAlign | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '5'},
       u32(0),
       u32(0),
       u32(VASize),
       u32(0),
       u32(0),
       u32(0),
       u16(Noname ? 0 : 1), // NumberOfRelocations
       u16(0),
       u32(VAAlign | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
      {{'.', 'i', 'd', 'a', 't', 'a', '$', '7'},
       u32(0),
       u32(0),
       u32(4),
       u32(0),
       u32(0),
       u32(0),
       u16(1),
       u16(0),
       u32(IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)},
  };
  uint32_t NumberOfSections = 3;
  uint32_t ThunkSection, NameSection;
  if (!Data) {
    ThunkSection = NumberOfSections + 1;
    SectionTable[NumberOfSections++] =
        coff_section{{'.', 't', 'e', 'x', 't'},
                     u32(0),
                     u32(0),
                     u32(Thunk.size()),
                     u32(0),
                     u32(0),
                     u32(0),
                     u16(NumThunkRelocations),
                     u16(0),
                     u32(IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_CNT_CODE |
                         IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_EXECUTE)};
  }
  if (!Noname) {
    NameSection = NumberOfSections + 1;
    SectionTable[NumberOfSections++] = coff_section{
        {'.', 'i', 'd', 'a', 't', 'a', '$', '6'},
        u32(0),
        u32(0),
        u32(2 + alignTo(ImportName.size() + 1, 2)),
        u32(0),
        u32(0),
        u32(0),
        u16(0),
        u16(0),
        u32(IMAGE_SCN_ALIGN_2BYTES | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE)};
  }
  Header.NumberOfSections = NumberOfSections;

  // Symbol Table
  const uint32_t MaxNumberOfSymbols = 4;
  coff_symbol16 SymbolTable[MaxNumberOfSymbols] = {
      {{{0, 0, 0, 0, 0, 0, 0, 0}}, // __imp_<symbol>
       u32(0),
       u16(2),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}}, // _head_<libname>
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
  };
  uint32_t NumberOfSymbols = 2;
  if (!Data) {
    SymbolTable[NumberOfSymbols++] =
        coff_symbol16{{{0, 0, 0, 0, 0, 0, 0, 0}}, // <symbol>
                      u32(0),
                      u16(ThunkSection),
                      u16(0),
                      IMAGE_SYM_CLASS_EXTERNAL,
                      0};
  }
  uint32_t NameSymbol;
  if (!Noname) {
    NameSymbol = NumberOfSymbols;
    SymbolTable[NumberOfSymbols++] =
        coff_symbol16{{{'.', 'i', 'd', 'a', 't', 'a', '$', '6'}},
                      u32(0),
                      u16(NameSection),
                      u16(0),
                      IMAGE_SYM_CLASS_SECTION,
                      0};
  };
  Header.NumberOfSymbols = NumberOfSymbols;

  const uint32_t MaxNumberOfStrings = 3;
  const std::string StringTable[MaxNumberOfStrings] = {
      ("__imp_" + Sym).str(),
      ImportDescriptorSymbolName,
      std::string(Sym),
  };
  uint32_t NumberOfStrings = 2 + (!Data ? 1 : 0);
  uint32_t StringTableOffsets[MaxNumberOfStrings];
  uint32_t StringTablePos = sizeof(uint32_t);
  for (uint32_t I = 0; I < NumberOfStrings; I++) {
    StringTableOffsets[I] = StringTablePos;
    StringTablePos += StringTable[I].size() + 1;
  }

  size_t Pos = 0;
  Pos += sizeof(Header);
  Pos += NumberOfSections * sizeof(coff_section);

  for (uint32_t I = 0; I < NumberOfSections; I++) {
    SectionTable[I].PointerToRawData = Pos;
    Pos += SectionTable[I].SizeOfRawData;
    if (SectionTable[I].NumberOfRelocations > 0)
      SectionTable[I].PointerToRelocations = Pos;
    Pos += SectionTable[I].NumberOfRelocations * sizeof(coff_relocation);
  }

  Header.PointerToSymbolTable = Pos;
  Pos += NumberOfSymbols * sizeof(coff_symbol16);
  Pos += StringTablePos;

  SymbolTable[0].Name.Offset.Offset = StringTableOffsets[0];
  SymbolTable[1].Name.Offset.Offset = StringTableOffsets[1];
  if (!Data)
    SymbolTable[2].Name.Offset.Offset = StringTableOffsets[2];

  coff_relocation NameHintReloc = {u32(0), u32(NameSymbol),
                                   u16(getImgRelRelocation(Machine))};

  coff_relocation ThunkRelocs[2] = {
      {u32(ThunkRelocationOffsets[0]), u32(0), u16(ThunkRelocationTypes[0])},
      {u32(ThunkRelocationOffsets[1]), u32(0), u16(ThunkRelocationTypes[1])},
  };

  coff_relocation HeadReferenceReloc = {u32(0), u32(1),
                                        u16(getImgRelRelocation(Machine))};

  append(Buffer, Header);
  for (uint32_t I = 0; I < NumberOfSections; I++)
    append(Buffer, SectionTable[I]);

  // .idata$4, IAT
  if (Noname) {
    if (is32bit(Machine))
      append(Buffer, u32((1U << 31) | Ordinal));
    else
      append(Buffer, u64((1ULL << 63) | Ordinal));
  } else {
    append(Buffer, u32(0));
    if (!is32bit(Machine))
      append(Buffer, u32(0));
    append(Buffer, NameHintReloc);
  }

  // .idata$5, ILT
  if (Noname) {
    if (is32bit(Machine))
      append(Buffer, u32((1U << 31) | Ordinal));
    else
      append(Buffer, u64((1ULL << 63) | Ordinal));
  } else {
    append(Buffer, u32(0));
    if (!is32bit(Machine))
      append(Buffer, u32(0));
    append(Buffer, NameHintReloc);
  }

  // .idata$7
  append(Buffer, u32(0));
  append(Buffer, HeadReferenceReloc);

  if (!Data) {
    // .text
    auto S = Buffer.size();
    Buffer.resize(S + Thunk.size());
    memcpy(&Buffer[S], Thunk.data(), Thunk.size());
    for (int I = 0; I < NumThunkRelocations; I++)
      append(Buffer, ThunkRelocs[I]);
  }

  // .idata$6
  if (!Noname) {
    append(Buffer, u16(Ordinal));
    auto S = Buffer.size();
    Buffer.resize(S + alignTo(ImportName.size() + 1, 2));
    memcpy(&Buffer[S], ImportName.data(), ImportName.size());
    for (uint32_t I = ImportName.size(); I < alignTo(ImportName.size() + 1, 2);
         I++)
      Buffer[S + I] = '\0';
  }

  for (uint32_t I = 0; I < NumberOfSymbols; I++)
    append(Buffer, SymbolTable[I]);

  // String Table
  writeStringTable(Buffer, ArrayRef<std::string>(StringTable, NumberOfStrings));

  StringRef F{reinterpret_cast<const char *>(Buffer.data()), Buffer.size()};
  char FileNumberStr[10];
  snprintf(FileNumberStr, sizeof(FileNumberStr), "%05d", NumFiles++);
  char *Buf = Alloc.Allocate<char>(Buffer.size());
  memcpy(Buf, Buffer.data(), Buffer.size());
  return NewArchiveMember{
      MemoryBufferRef(StringRef(Buf, Buffer.size()),
                      MemberFileNames.save(GnuPrefix + "s" +
                                           std::string(FileNumberStr) + ".o"))};
}

NewArchiveMember ObjectFactory::createWeakExternal(StringRef Sym,
                                                   StringRef Weak, bool Imp) {
  std::vector<uint8_t> Buffer;
  const uint32_t NumberOfSections = 1;
  const uint32_t NumberOfSymbols = 5;

  // COFF Header
  coff_file_header Header{
      u16(Machine),
      u16(NumberOfSections),
      u32(0),
      u32(sizeof(Header) + (NumberOfSections * sizeof(coff_section))),
      u32(NumberOfSymbols),
      u16(0),
      u16(0),
  };
  append(Buffer, Header);

  // Section Header Table
  const coff_section SectionTable[NumberOfSections] = {
      {{'.', 'd', 'r', 'e', 'c', 't', 'v', 'e'},
       u32(0),
       u32(0),
       u32(0),
       u32(0),
       u32(0),
       u32(0),
       u16(0),
       u16(0),
       u32(IMAGE_SCN_LNK_INFO | IMAGE_SCN_LNK_REMOVE)}};
  append(Buffer, SectionTable);

  // Symbol Table
  coff_symbol16 SymbolTable[NumberOfSymbols] = {
      {{{'@', 'c', 'o', 'm', 'p', '.', 'i', 'd'}},
       u32(0),
       u16(0xFFFF),
       u16(0),
       IMAGE_SYM_CLASS_STATIC,
       0},
      {{{'@', 'f', 'e', 'a', 't', '.', '0', '0'}},
       u32(0),
       u16(0xFFFF),
       u16(0),
       IMAGE_SYM_CLASS_STATIC,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_EXTERNAL,
       0},
      {{{0, 0, 0, 0, 0, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_WEAK_EXTERNAL,
       1},
      {{{2, 0, 0, 0, IMAGE_WEAK_EXTERN_SEARCH_ALIAS, 0, 0, 0}},
       u32(0),
       u16(0),
       u16(0),
       IMAGE_SYM_CLASS_NULL,
       0},
  };
  SymbolTable[2].Name.Offset.Offset = sizeof(uint32_t);

  //__imp_ String Table
  StringRef Prefix = Imp ? "__imp_" : "";
  SymbolTable[3].Name.Offset.Offset =
      sizeof(uint32_t) + Sym.size() + Prefix.size() + 1;
  append(Buffer, SymbolTable);
  writeStringTable(Buffer, {(Prefix + Sym).str(),
                            (Prefix + Weak).str()});

  // Copied here so we can still use writeStringTable
  char *Buf = Alloc.Allocate<char>(Buffer.size());
  memcpy(Buf, Buffer.data(), Buffer.size());
  return {MemoryBufferRef(StringRef(Buf, Buffer.size()), ImportName)};
}

Error writeImportLibrary(StringRef ImportName, StringRef Path,
                         ArrayRef<COFFShortExport> Exports,
                         MachineTypes Machine, bool MinGW) {

  if (MinGW)
    return writeGnuImportLibrary(ImportName, Path, Exports, Machine);

  std::vector<NewArchiveMember> Members;
  ObjectFactory OF(llvm::sys::path::filename(ImportName), Machine);

  std::vector<uint8_t> ImportDescriptor;
  Members.push_back(OF.createImportDescriptor(ImportDescriptor));

  std::vector<uint8_t> NullImportDescriptor;
  Members.push_back(OF.createNullImportDescriptor(NullImportDescriptor));

  std::vector<uint8_t> NullThunk;
  Members.push_back(OF.createNullThunk(NullThunk));

  for (COFFShortExport E : Exports) {
    if (E.Private)
      continue;

    ImportType ImportType = IMPORT_CODE;
    if (E.Data)
      ImportType = IMPORT_DATA;
    if (E.Constant)
      ImportType = IMPORT_CONST;

    StringRef SymbolName = E.SymbolName.empty() ? E.Name : E.SymbolName;
    ImportNameType NameType = E.Noname
                                  ? IMPORT_ORDINAL
                                  : getNameType(SymbolName, E.Name,
                                                Machine, MinGW);
    Expected<std::string> Name = E.ExtName.empty()
                                     ? std::string(SymbolName)
                                     : replace(SymbolName, E.Name, E.ExtName);

    if (!Name)
      return Name.takeError();

    if (!E.AliasTarget.empty() && *Name != E.AliasTarget) {
      Members.push_back(OF.createWeakExternal(E.AliasTarget, *Name, false));
      Members.push_back(OF.createWeakExternal(E.AliasTarget, *Name, true));
      continue;
    }

    Members.push_back(
        OF.createShortImport(*Name, E.Ordinal, ImportType, NameType));
  }

  return writeArchive(Path, Members, /*WriteSymtab*/ true,
                      object::Archive::K_GNU,
                      /*Deterministic*/ true, /*Thin*/ false);
}

static StringRef ltrim1(StringRef S, const char *Chars) {
  if (!S.empty() && strchr(Chars, S[0]))
    return S.substr(1);
  return S;
}

Error writeGnuImportLibrary(StringRef ImportName, StringRef Path,
                            ArrayRef<COFFShortExport> Exports,
                            MachineTypes Machine) {

  std::vector<NewArchiveMember> Members;
  ObjectFactory OF(llvm::sys::path::filename(ImportName), Machine);
  OF.setGnuSymbolNames();

  std::vector<uint8_t> Head;
  Members.push_back(OF.createGnuHead(Head));

  std::vector<uint8_t> Tail;
  Members.push_back(OF.createGnuTail(Tail));

  for (COFFShortExport E : Exports) {
    if (E.Private)
      continue;

    StringRef SymbolName = E.SymbolName.empty() ? E.Name : E.SymbolName;
    ImportNameType NameType = getNameType(SymbolName, E.Name, Machine, true);
    Expected<std::string> Name = E.ExtName.empty()
                                     ? std::string(SymbolName)
                                     : replace(SymbolName, E.Name, E.ExtName);

    if (!Name)
      return Name.takeError();

    StringRef DllName = *Name;

    if (!E.AliasTarget.empty())
      DllName = E.AliasTarget;

    switch (NameType) {
    case IMPORT_NAME:
    default:
      // Do nothing.
      break;
    case IMPORT_NAME_NOPREFIX:
      DllName = ltrim1(DllName, "?@_");
      break;
    case IMPORT_NAME_UNDECORATE:
      DllName = ltrim1(DllName, "?@_");
      DllName = DllName.substr(0, DllName.find('@'));
      break;
    }

    Members.push_back(
        OF.createGnuIdata(*Name, DllName, E.Data, E.Noname, E.Ordinal));
  }

  return writeArchive(Path, Members, /*WriteSymtab*/ true,
                      object::Archive::K_GNU,
                      /*Deterministic*/ true, /*Thin*/ false);
}

} // namespace object
} // namespace llvm
