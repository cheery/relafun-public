module Wasm.CoreWriter where

import Data.List (group)
import Data.Word (Word8)
import Wasm.Core
import Wasm.CommonWriting
import Prelude hiding (EQ)

instance Writable Core where
  write sections = magic <> version <> layer <> concat (map write sections)

instance Writable Section where
  write s = [sectionId s] <> u32 (length sec) <> sec
    where sec = section s

section :: Section -> [Word8]
section (CustomSection name bytes) = utf8 name <> bytes
section (TypeSection types) = vec types
section (ImportSection imports) = vec imports
section (FunctionSection f) = vec' u32 f
section (TableSection tables) = vec tables
section (MemorySection memTypes) = vec memTypes
section (GlobalSection globals) = vec globals
section (ExportSection exports) = vec exports
section (StartSection idx) = u32 idx
section (ElementSection elements) = vec elements
section (CodeSection codes) = vec codes
section (DataSection datas) = vec datas
section (DataCountSection i) = u32 i
 
-- Type section contents
instance Writable NumType where
  write I32 = [0x7F]
  write I64 = [0x7E]
  write F32 = [0x7D]
  write F64 = [0x7C]

instance Writable VecType where
  write V128 = [0x7B]

instance Writable (HeapType Int) where
  write NOFUNC = [0x73]
  write NOEXTERN = [0x72]
  write NONE   = [0x71]
  write FUNC   = [0x70]
  write EXTERN = [0x6F]
  write ANY    = [0x6E]
  write EQ     = [0x6D]
  write I31    = [0x6C]
  write STRUCT = [0x6B]
  write ARRAY  = [0x6A]
  write (HT i) = leb128 (fromIntegral i)

instance Writable (RefType Int) where
  write (Ref False ht) = [0x64] <> write ht
  write (Ref True (HT ht)) = [0x63] <> write (HT ht)
  write (Ref True ht) = write ht

instance Writable (ValType Int) where
  write (N n) = write n
  write (V v) = write v
  write (R r) = write r

instance Writable [ValType Int] where
  write = vec

instance Writable (StorageType Int, Mut) where
  write (t,m) = write t <> write m

instance Writable [(StorageType Int, Mut)] where
  write = vec

instance Writable (StorageType Int) where
  write (U u) = write u
  write (P p) = write p

instance Writable PackedType where
  write I8 = [0x78]
  write I16 = [0x77]

instance Writable (CompType Int) where
  write (Array a) = [0x5E] <> write a
  write (Struct s) = [0x5F] <> write s
  write (Func i o) = [0x60] <> write i <> write o

instance Writable (RecType Int) where
  write [a] = write a
  write as = [0x4E] <> vec as

instance Writable (SubType Int) where
  write (Sub True [] ct) = write ct
  write (Sub False xs ct) = [0x50] <> vec' u32 xs <> write ct
  write (Sub True xs ct) = [0x4F] <> vec' u32 xs <> write ct

instance Writable Limits where
  write (x, Nothing) = [0x00] <> u32 x
  write (x, Just y) = [0x01] <> u32 x <> u32 y

instance Writable (RefType Int, Limits) where
  write (r, l) = write r <> write l

instance Writable (ValType Int, Mut) where
  write (v, m) = write v <> write m

instance Writable Mut where
  write Imm = [0x00]
  write Mut = [0x01]

instance Writable (String, String, ImportDesc Int) where
  write (n,m,id) = utf8 n <> utf8 m <> write id

instance Writable (ImportDesc Int) where
  write (FuncImport i) = [0x00] <> u32 i
  write (TableImport tt) = [0x01] <> write tt
  write (MemImport mt) = [0x02] <> write mt
  write (GlobalImport gt) = [0x03] <> write gt

-- Table section contents
instance Writable ((RefType Int, Limits), Maybe (Expr Int)) where
  write (tt, Nothing) = write tt
  write (tt, Just e) = [0x40, 0x00] <> write tt <> write e

-- Global section contents
instance Writable ((ValType Int, Mut), Expr Int) where
  write (gt, e) = write gt <> write e

-- Export section contents
instance Writable (String, ExportDesc) where
  write (n, ed) = utf8 n <> write ed

instance Writable ExportDesc where
  write (FuncExport i) = [0x00] <> u32 i
  write (TableExport i) = [0x01] <> u32 i
  write (MemExport i) = [0x02] <> u32 i
  write (GlobalExport i) = [0x03] <> u32 i

-- Element section contents
instance Writable Elem where
  write (Elem0 e ii) = [0x00] <> write e <> vec' u32 ii
  write (Elem1 k ii) = [0x01] <> write k <> vec' u32 ii
  write (Elem2 i e k ii) = [0x02] <> u32 i <> write e <> write k <> vec' u32 ii
  write (Elem3 k ii) = [0x03] <> write k <> vec' u32 ii
  write (Elem4 e es) = [0x04] <> write e <> vec es
  write (Elem5 rt es) = [0x05] <> write rt <> vec es
  write (Elem6 i e rt es) = [0x06] <> u32 i <> write e <> write rt <> vec es
  write (Elem7 rt es) = [0x07] <> write rt <> vec es

instance Writable ElemKind where
  write ElemKindRefFunc = [0x00]

-- code section
instance Writable ([ValType Int], Expr Int) where
  write fd = u32 (length code) <> code
    where code = funcData fd

funcData :: ([ValType Int], Expr Int) -> [Word8]
funcData (vts, e) = vec' locals (group vts) <> write e

locals :: [ValType Int] -> [Word8]
locals xs@(x:_) = u32 (length xs) <> write x

instance Writable ([Word8], DataMode) where
  write (b, Active 0 e) = [0x00] <> write e <> vec b
  write (b, Passive) = [0x01] <> vec b
  write (b, Active x e) = [0x02] <> u32 x <> write e <> vec b

-- Instructions
instance Writable (BlockType Int) where
  write BNone = [0x40]
  write (BVal vt) = write vt
  write (BType i) = sleb128 (fromIntegral i)

instance Writable (Expr Int) where
  write is = concat (map write is) <> [0x0B]

instance Writable (Instruction Int) where
  write I_Unreachable = [0x00]
  write I_Nop = [0x01]
  write (I_Block bt is) = [0x02] <> write bt <> concat (map write is) <> [0x0B]
  write (I_Loop bt is) = [0x03] <> write bt <> concat (map write is) <> [0x0B]
  write (I_If bt is) = [0x04] <> write bt <> concat (map write is) <> [0x0B]
  write (I_IfElse bt is1 is2) = [0x04] <> write bt <> concat (map write is1) <> [0x05]
                                                   <> concat (map write is2) <> [0x0B]
  write (I_Br i) = [0x0C] <> u32 i
  write (I_BrIf i) = [0x0D] <> u32 i
  write (I_BrTable ii i) = [0x0E] <> vec' u32 ii <> u32 i
  write I_Return = [0x0F]
  write (I_Call i) = [0x10] <> u32 i
  write (I_CallIndirect i j) = [0x11] <> u32 i <> u32 j
  write (I_ReturnCall i) = [0x12] <> u32 i
  write (I_ReturnCallIndirect i j) = [0x13] <> u32 i <> u32 j
  write (I_CallRef i) = [0x14] <> u32 i
  write (I_ReturnCallRef i) = [0x15] <> u32 i
  write (I_BrOnNull i) = [0xD5] <> u32 i
  write (I_BrOnNonNull i) = [0xD6] <> u32 i
  write (I_BrOnCast cf i x y) = [0xFB] <> u32 24 <> write cf <> u32 i <> write x <> write y
  write (I_BrOnCastFail cf i x y) = [0xFB] <> u32 25 <> write cf <> u32 i <> write x <> write y
  write (I_RefNull ht) = [0xD0] <> write ht
  write I_RefIsNull = [0xD1]
  write (I_RefFunc i) = [0xD2] <> u32 i
  write I_RefEq = [0xD3]
  write I_RefAsNonNull = [0xD4]
  write (I_StructNew i) = [0x0FB] <> u32 0 <> u32 i
  write (I_StructNewDefault i) = [0xFB] <> u32 1 <> u32 i 
  write (I_StructGet i j) = [0xFB] <> u32 2 <> u32 i <> u32 j
  write (I_StructGetS i j) = [0xFB] <> u32 3 <> u32 i <> u32 j
  write (I_StructGetU i j) = [0xFB] <> u32 4 <> u32 i <> u32 j
  write (I_StructSet i j) = [0xFB] <> u32 5 <> u32 i <> u32 j
  write (I_ArrayNew i) = [0xFB] <> u32 6 <> u32 i
  write (I_ArrayNewDefault i) = [0xFB] <> u32 7 <> u32 i 
  write (I_ArrayNewFixed i j) = [0xFB] <> u32 8 <> u32 i <> u32 j
  write (I_ArrayNewData i j) = [0xFB] <> u32 9 <> u32 i <> u32 j
  write (I_ArrayNewElem i j) = [0xFB] <> u32 10 <> u32 i <> u32 j
  write (I_ArrayGet i) = [0xFB] <> u32 11 <> u32 i
  write (I_ArrayGetS i) = [0xFB] <> u32 12 <> u32 i
  write (I_ArrayGetU i) = [0xFB] <> u32 13 <> u32 i
  write (I_ArraySet i) = [0xFB] <> u32 14 <> u32 i
  write I_ArrayLen = [0xFB] <> u32 15
  write (I_ArrayFill i) = [0xFB] <> u32 16 <> u32 i
  write (I_ArrayCopy i j) = [0xFB] <> u32 17 <> u32 i <> u32 j
  write (I_ArrayInitData i j) = [0xFB] <> u32 18 <> u32 i <> u32 j
  write (I_ArrayInitElem i j) = [0xFB] <> u32 19 <> u32 i <> u32 j
  write (I_RefTest False ht) = [0xFB] <> u32 20 <> write ht
  write (I_RefTest True ht) = [0xFB] <> u32 21 <> write ht
  write (I_RefCast False ht) = [0xFB] <> u32 22 <> write ht
  write (I_RefCast True ht) = [0xFB] <> u32 23 <> write ht
  write I_AnyConvertExtern = [0xFB] <> u32 26
  write I_ExternConvertAny = [0xFB] <> u32 27
  write I_RefI31           = [0xFB] <> u32 28
  write I_I31GetS          = [0xFB] <> u32 29
  write I_I31GetU          = [0xFB] <> u32 30
  write I_Drop = [0x1A]
  write I_Select = [0x1B]
  write (I_SelectT vt) = [0x1C] <> vec vt
  write (I_LocalGet i) = [0x20] <> u32 i
  write (I_LocalSet i) = [0x21] <> u32 i
  write (I_LocalTee i) = [0x22] <> u32 i
  write (I_GlobalGet i) = [0x23] <> u32 i
  write (I_GlobalSet i) = [0x24] <> u32 i
  write (I_TableGet i) = [0x25] <> u32 i
  write (I_TableSet i) = [0x26] <> u32 i
  write (I_TableInit i j) = [0xFC] <> u32 12 <> u32 i <> u32 j
  write (I_ElemDrop i) = [0xFC] <> u32 13 <> u32 i
  write (I_TableCopy i j) = [0xFC] <> u32 14 <> u32 i <> u32 j
  write (I_TableGrow i) = [0xFC] <> u32 15 <> u32 i
  write (I_TableSize i) = [0xFC] <> u32 16 <> u32 i
  write (I_TableFill i) = [0xFC] <> u32 17 <> u32 i
  write (I_I32Load    ma) = [0x28] <> write ma
  write (I_I64Load    ma) = [0x29] <> write ma
  write (I_F32Load    ma) = [0x2A] <> write ma
  write (I_F64Load    ma) = [0x2B] <> write ma
  write (I_I32Load8S  ma) = [0x2C] <> write ma
  write (I_I32Load8U  ma) = [0x2D] <> write ma
  write (I_I32Load16S ma) = [0x2E] <> write ma
  write (I_I32Load16U ma) = [0x2F] <> write ma
  write (I_I64Load8S  ma) = [0x30] <> write ma
  write (I_I64Load8U  ma) = [0x31] <> write ma
  write (I_I64Load16S ma) = [0x32] <> write ma
  write (I_I64Load16U ma) = [0x33] <> write ma
  write (I_I64Load32S ma) = [0x34] <> write ma
  write (I_I64Load32U ma) = [0x35] <> write ma
  write (I_I32Store   ma) = [0x36] <> write ma
  write (I_I64Store   ma) = [0x37] <> write ma
  write (I_F32Store   ma) = [0x38] <> write ma
  write (I_F64Store   ma) = [0x39] <> write ma
  write (I_I32Store8  ma) = [0x3A] <> write ma
  write (I_I32Store16 ma) = [0x3B] <> write ma
  write (I_I64Store8  ma) = [0x3C] <> write ma
  write (I_I64Store16 ma) = [0x3D] <> write ma
  write (I_I64Store32 ma) = [0x3E] <> write ma
  write I_MemorySize = [0x3F, 0x00]
  write I_MemoryGrow = [0x40, 0x00]
  write (I_MemoryInit i) = [0xFC] <> u32 8 <> u32 i <> [0x00]
  write (I_DataDrop i) = [0xFC] <> u32 9 <> u32 i
  write I_MemoryCopy = [0xFC] <> u32 10 <> [0x00, 0x00]
  write I_MemoryFill = [0xFC] <> u32 11 <> [0x00]
  write (I_I32Const i) = [0x41] <> sleb128 i
  write (I_I64Const i) = [0x42] <> sleb128 i
  write (I_F32Const f) = [0x43] <> f
  write (I_F64Const f) = [0x44] <> f
  write I_I32Eqz           = [0x45]
  write I_I32Eq            = [0x46]
  write I_I32Ne            = [0x47]
  write I_I32LtS           = [0x48]
  write I_I32LtU           = [0x49]
  write I_I32GtS           = [0x4A]
  write I_I32GtU           = [0x4B]
  write I_I32LeS           = [0x4C]
  write I_I32LeU           = [0x4D]
  write I_I32GeS           = [0x4E]
  write I_I32GeU           = [0x4F]
  write I_I64Eqz           = [0x50]
  write I_I64Eq            = [0x51]
  write I_I64Ne            = [0x52]
  write I_I64LtS           = [0x53]
  write I_I64LtU           = [0x54]
  write I_I64GtS           = [0x55]
  write I_I64GtU           = [0x56]
  write I_I64LeS           = [0x57]
  write I_I64LeU           = [0x58]
  write I_I64GeS           = [0x59]
  write I_I64GeU           = [0x5A]
  write I_F32Eq            = [0x5B]
  write I_F32Ne            = [0x5C]
  write I_F32Lt            = [0x5D]
  write I_F32Gt            = [0x5E]
  write I_F32Le            = [0x5F]
  write I_F32Ge            = [0x60]
  write I_F64Eq            = [0x61]
  write I_F64Ne            = [0x62]
  write I_F64Lt            = [0x63]
  write I_F64Gt            = [0x64]
  write I_F64Le            = [0x65]
  write I_F64Ge            = [0x66]
  write I_I32Clz           = [0x67]
  write I_I32Ctz           = [0x68]
  write I_I32Popcnt        = [0x69]
  write I_I32Add           = [0x6A]
  write I_I32Sub           = [0x6B]
  write I_I32Mul           = [0x6C]
  write I_I32DivS          = [0x6D]
  write I_I32DivU          = [0x6E]
  write I_I32RemS          = [0x6F]
  write I_I32RemU          = [0x70]
  write I_I32And           = [0x71]
  write I_I32Or            = [0x72]
  write I_I32Xor           = [0x73]
  write I_I32Shl           = [0x74]
  write I_I32ShrS          = [0x75]
  write I_I32ShrU          = [0x76]
  write I_I32Rotl          = [0x77]
  write I_I32Rotr          = [0x78]
  write I_I64Clz           = [0x79]
  write I_I64Ctz           = [0x7A]
  write I_I64Popcnt        = [0x7B]
  write I_I64Add           = [0x7C]
  write I_I64Sub           = [0x7D]
  write I_I64Mul           = [0x7E]
  write I_I64DivS          = [0x7F]
  write I_I64DivU          = [0x80]
  write I_I64RemS          = [0x81]
  write I_I64RemU          = [0x82]
  write I_I64And           = [0x83]
  write I_I64Or            = [0x84]
  write I_I64Xor           = [0x85]
  write I_I64Shl           = [0x86]
  write I_I64ShrS          = [0x87]
  write I_I64ShrU          = [0x88]
  write I_I64Rotl          = [0x89]
  write I_I64Rotr          = [0x8A]
  write I_F32Abs           = [0x8B]
  write I_F32Neg           = [0x8C]
  write I_F32Ceil          = [0x8D]
  write I_F32Floor         = [0x8E]
  write I_F32Trunc         = [0x8F]
  write I_F32Nearest       = [0x90]
  write I_F32Sqrt          = [0x91]
  write I_F32Add           = [0x92]
  write I_F32Sub           = [0x93]
  write I_F32Mul           = [0x94]
  write I_F32Div           = [0x95]
  write I_F32Min           = [0x96]
  write I_F32Max           = [0x97]
  write I_F32CopySign      = [0x98]
  write I_F64Abs           = [0x99]
  write I_F64Neg           = [0x9A]
  write I_F64Ceil          = [0x9B]
  write I_F64Floor         = [0x9C]
  write I_F64Trunc         = [0x9D]
  write I_F64Nearest       = [0x9E]
  write I_F64Sqrt          = [0x9F]
  write I_F64Add           = [0xA0]
  write I_F64Sub           = [0xA1]
  write I_F64Mul           = [0xA2]
  write I_F64Div           = [0xA3]
  write I_F64Min           = [0xA4]
  write I_F64Max           = [0xA5]
  write I_F64CopySign      = [0xA6]
  write I_I32WrapI64       = [0xA7]
  write I_I32TruncF32S     = [0xA8]
  write I_I32TruncF32U     = [0xA9]
  write I_I32TruncF64S     = [0xAA]
  write I_I32TruncF64U     = [0xAB]
  write I_I64ExtendI32S    = [0xAC]
  write I_I64ExtendI32U    = [0xAD]
  write I_I64TruncF32S     = [0xAE]
  write I_I64TruncF32U     = [0xAF]
  write I_I64TruncF64S     = [0xB0]
  write I_I64TruncF64U     = [0xB1]
  write I_F32ConvertI32S   = [0xB2]
  write I_F32ConvertI32U   = [0xB3]
  write I_F32ConvertI64S   = [0xB4]
  write I_F32ConvertI64U   = [0xB5]
  write I_F32DemoteF64     = [0xB6]
  write I_F64ConvertI32S   = [0xB7]
  write I_F64ConvertI32U   = [0xB8]
  write I_F64ConvertI64S   = [0xB9]
  write I_F64ConvertI64U   = [0xBA]
  write I_F64PromoteF32    = [0xBB]
  write I_I32ReinterpretF32= [0xBC]
  write I_I64ReinterpretF64= [0xBD]
  write I_F32ReinterpretI32= [0xBE]
  write I_F64ReinterpretI64= [0xBF]
  write I_I32Extend8S      = [0xC0]
  write I_I32Extend16S     = [0xC1]
  write I_I64Extend8S      = [0xC2]
  write I_I64Extend16S     = [0xC3]
  write I_I64Extend32S     = [0xC4]
  write I_I32TruncSatF32S = [0xFC] <> u32 0
  write I_I32TruncSatF32U = [0xFC] <> u32 1
  write I_I32TruncSatF64S = [0xFC] <> u32 2
  write I_I32TruncSatF64U = [0xFC] <> u32 3
  write I_I64TruncSatF32S = [0xFC] <> u32 4
  write I_I64TruncSatF32U = [0xFC] <> u32 5
  write I_I64TruncSatF64S = [0xFC] <> u32 6
  write I_I64TruncSatF64U = [0xFC] <> u32 7
  write (I_V128Load        ma) = [0xFD] <> u32 0  <> write ma
  write (I_V128Load8x8S    ma) = [0xFD] <> u32 1  <> write ma
  write (I_V128Load8x8U    ma) = [0xFD] <> u32 2  <> write ma
  write (I_V128Load16x4S   ma) = [0xFD] <> u32 3  <> write ma
  write (I_V128Load16x4U   ma) = [0xFD] <> u32 4  <> write ma
  write (I_V128Load32x2S   ma) = [0xFD] <> u32 5  <> write ma
  write (I_V128Load32x2U   ma) = [0xFD] <> u32 6  <> write ma
  write (I_V128Load8Splat  ma) = [0xFD] <> u32 7  <> write ma
  write (I_V128Load16Splat ma) = [0xFD] <> u32 8  <> write ma
  write (I_V128Load32Splat ma) = [0xFD] <> u32 9  <> write ma
  write (I_V128Load64Splat ma) = [0xFD] <> u32 10 <> write ma
  write (I_V128Load32Zero  ma) = [0xFD] <> u32 92 <> write ma
  write (I_V128Load64Zero  ma) = [0xFD] <> u32 93 <> write ma
  write (I_V128Store       ma) = [0xFD] <> u32 11 <> write ma
  write (I_V128Load8Lane   ma i) = [0xFD] <> u32 84 <> write ma <> u32 i
  write (I_V128Load16Lane  ma i) = [0xFD] <> u32 85 <> write ma <> u32 i
  write (I_V128Load32Lane  ma i) = [0xFD] <> u32 86 <> write ma <> u32 i
  write (I_V128Load64Lane  ma i) = [0xFD] <> u32 87 <> write ma <> u32 i
  write (I_V128Store8Lane  ma i) = [0xFD] <> u32 88 <> write ma <> u32 i
  write (I_V128Store16Lane ma i) = [0xFD] <> u32 89 <> write ma <> u32 i
  write (I_V128Store32Lane ma i) = [0xFD] <> u32 90 <> write ma <> u32 i
  write (I_V128Store64Lane ma i) = [0xFD] <> u32 91 <> write ma <> u32 i
  write (I_V128Const s) = [0xFD] <> u32 12 <> s
  write (I_I8x16Shuffle s) = [0xFD] <> u32 13 <> concat (map u32 s)
  write (I_I8x16ExtractLaneS i) = [0xFD] <> u32 21 <> u32 i
  write (I_I8x16ExtractLaneU i) = [0xFD] <> u32 22 <> u32 i
  write (I_I8x16ReplaceLane  i) = [0xFD] <> u32 23 <> u32 i
  write (I_I16x8ExtractLaneS i) = [0xFD] <> u32 24 <> u32 i
  write (I_I16x8ExtractLaneU i) = [0xFD] <> u32 25 <> u32 i
  write (I_I16x8ReplaceLane  i) = [0xFD] <> u32 26 <> u32 i
  write (I_I32x4ExtractLane  i) = [0xFD] <> u32 27 <> u32 i
  write (I_I32x4ReplaceLane  i) = [0xFD] <> u32 28 <> u32 i
  write (I_I64x2ExtractLane  i) = [0xFD] <> u32 29 <> u32 i
  write (I_I64x2ReplaceLane  i) = [0xFD] <> u32 30 <> u32 i
  write (I_F32x4ExtractLane  i) = [0xFD] <> u32 31 <> u32 i
  write (I_F32x4ReplaceLane  i) = [0xFD] <> u32 32 <> u32 i
  write (I_F64x2ExtractLane  i) = [0xFD] <> u32 33 <> u32 i
  write (I_F64x2ReplaceLane  i) = [0xFD] <> u32 34 <> u32 i
  write I_I8x16Swizzle              = [0xFD] <> u32 14 
  write I_I8x16Splat                = [0xFD] <> u32 15 
  write I_I16x8Splat                = [0xFD] <> u32 16 
  write I_I32x4Splat                = [0xFD] <> u32 17 
  write I_I64x2Splat                = [0xFD] <> u32 18 
  write I_F32x4Splat                = [0xFD] <> u32 19 
  write I_F64x2Splat                = [0xFD] <> u32 20 
  write I_I8x16Eq                   = [0xFD] <> u32 35 
  write I_I8x16Ne                   = [0xFD] <> u32 36 
  write I_I8x16LtS                  = [0xFD] <> u32 37 
  write I_I8x16LtU                  = [0xFD] <> u32 38 
  write I_I8x16GtS                  = [0xFD] <> u32 39 
  write I_I8x16GtU                  = [0xFD] <> u32 40 
  write I_I8x16LeS                  = [0xFD] <> u32 41 
  write I_I8x16LeU                  = [0xFD] <> u32 42 
  write I_I8x16GeS                  = [0xFD] <> u32 43 
  write I_I8x16GeU                  = [0xFD] <> u32 44 
  write I_I16x8Eq                   = [0xFD] <> u32 45 
  write I_I16x8Ne                   = [0xFD] <> u32 46 
  write I_I16x8LtS                  = [0xFD] <> u32 47 
  write I_I16x8LtU                  = [0xFD] <> u32 48 
  write I_I16x8GtS                  = [0xFD] <> u32 49 
  write I_I16x8GtU                  = [0xFD] <> u32 50 
  write I_I16x8LeS                  = [0xFD] <> u32 51 
  write I_I16x8LeU                  = [0xFD] <> u32 52 
  write I_I16x8GeS                  = [0xFD] <> u32 53 
  write I_I16x8GeU                  = [0xFD] <> u32 54 
  write I_I32x4Eq                   = [0xFD] <> u32 55 
  write I_I32x4Ne                   = [0xFD] <> u32 56 
  write I_I32x4LtS                  = [0xFD] <> u32 57 
  write I_I32x4LtU                  = [0xFD] <> u32 58 
  write I_I32x4GtS                  = [0xFD] <> u32 59 
  write I_I32x4GtU                  = [0xFD] <> u32 60 
  write I_I32x4LeS                  = [0xFD] <> u32 61 
  write I_I32x4LeU                  = [0xFD] <> u32 62 
  write I_I32x4GeS                  = [0xFD] <> u32 63 
  write I_I32x4GeU                  = [0xFD] <> u32 64 
  write I_I64x2Eq                   = [0xFD] <> u32 214
  write I_I64x2Ne                   = [0xFD] <> u32 215
  write I_I64x2LtS                  = [0xFD] <> u32 216
  write I_I64x2GtS                  = [0xFD] <> u32 217
  write I_I64x2LeS                  = [0xFD] <> u32 218
  write I_I64x2GeS                  = [0xFD] <> u32 219
  write I_F32x4Eq                   = [0xFD] <> u32 65 
  write I_F32x4Ne                   = [0xFD] <> u32 66 
  write I_F32x4Lt                   = [0xFD] <> u32 67 
  write I_F32x4Gt                   = [0xFD] <> u32 68 
  write I_F32x4Le                   = [0xFD] <> u32 69 
  write I_F32x4Ge                   = [0xFD] <> u32 70 
  write I_F64x2Eq                   = [0xFD] <> u32 71 
  write I_F64x2Ne                   = [0xFD] <> u32 72 
  write I_F64x2Lt                   = [0xFD] <> u32 73 
  write I_F64x2Gt                   = [0xFD] <> u32 74 
  write I_F64x2Le                   = [0xFD] <> u32 75 
  write I_F64x2Ge                   = [0xFD] <> u32 76 
  write I_V128Not                   = [0xFD] <> u32 77 
  write I_V128And                   = [0xFD] <> u32 78 
  write I_V128AndNot                = [0xFD] <> u32 79 
  write I_V128Or                    = [0xFD] <> u32 80 
  write I_V128Xor                   = [0xFD] <> u32 81 
  write I_V128Bitselect             = [0xFD] <> u32 82 
  write I_V128AnyTrue               = [0xFD] <> u32 83 
  write I_I8x16Abs                  = [0xFD] <> u32 96 
  write I_I8x16Neg                  = [0xFD] <> u32 97 
  write I_I8x16Popcnt               = [0xFD] <> u32 98 
  write I_I8x16AllTrue              = [0xFD] <> u32 99 
  write I_I8x16Bitmask              = [0xFD] <> u32 100
  write I_I8x16NarrowI16x8S         = [0xFD] <> u32 101
  write I_I8x16NarrowI16x8U         = [0xFD] <> u32 102
  write I_I8x16Shl                  = [0xFD] <> u32 107
  write I_I8x16ShrS                 = [0xFD] <> u32 108
  write I_I8x16ShrU                 = [0xFD] <> u32 109
  write I_I8x16Add                  = [0xFD] <> u32 110
  write I_I8x16AddSatS              = [0xFD] <> u32 111
  write I_I8x16AddSatU              = [0xFD] <> u32 112
  write I_I8x16Sub                  = [0xFD] <> u32 113
  write I_I8x16SubSatS              = [0xFD] <> u32 114
  write I_I8x16SubSatU              = [0xFD] <> u32 115
  write I_I8x16MinS                 = [0xFD] <> u32 118
  write I_I8x16MinU                 = [0xFD] <> u32 119
  write I_I8x16MaxS                 = [0xFD] <> u32 120
  write I_I8x16MaxU                 = [0xFD] <> u32 121
  write I_I8x16AvgrU                = [0xFD] <> u32 123
  write I_I16x8ExtaddPairwiseI8x16S = [0xFD] <> u32 124
  write I_I16x8ExtaddPairwiseI8x16U = [0xFD] <> u32 125
  write I_I16x8Abs                  = [0xFD] <> u32 128
  write I_I16x8Neg                  = [0xFD] <> u32 129
  write I_I16x8Q15mulrSatS          = [0xFD] <> u32 130
  write I_I16x8AllTrue              = [0xFD] <> u32 131
  write I_I16x8Bitmask              = [0xFD] <> u32 132
  write I_I16x8NarrowI32x4S         = [0xFD] <> u32 133
  write I_I16x8NarrowI32x4U         = [0xFD] <> u32 134
  write I_I16x8ExtendLowI8x16S      = [0xFD] <> u32 135
  write I_I16x8ExtendHighI8x16S     = [0xFD] <> u32 136
  write I_I16x8ExtendLowI8x16U      = [0xFD] <> u32 137
  write I_I16x8ExtendHighI8x16U     = [0xFD] <> u32 138
  write I_I16x8Shl                  = [0xFD] <> u32 139
  write I_I16x8ShrS                 = [0xFD] <> u32 140
  write I_I16x8ShrU                 = [0xFD] <> u32 141
  write I_I16x8Add                  = [0xFD] <> u32 142
  write I_I16x8AddSatS              = [0xFD] <> u32 143
  write I_I16x8AddSatU              = [0xFD] <> u32 144
  write I_I16x8Sub                  = [0xFD] <> u32 145
  write I_I16x8SubSatS              = [0xFD] <> u32 146
  write I_I16x8SubSatU              = [0xFD] <> u32 147
  write I_I16x8Mul                  = [0xFD] <> u32 148
  write I_I16x8MinS                 = [0xFD] <> u32 149
  write I_I16x8MinU                 = [0xFD] <> u32 150
  write I_I16x8MaxS                 = [0xFD] <> u32 151
  write I_I16x8MaxU                 = [0xFD] <> u32 152
  write I_I16x8AvgrU                = [0xFD] <> u32 155
  write I_I16x8ExtmulLowI8x16S      = [0xFD] <> u32 156
  write I_I16x8ExtmulHighI8x16S     = [0xFD] <> u32 157
  write I_I16x8ExtmulLowI8x16U      = [0xFD] <> u32 158
  write I_I16x8ExtmulHighI8x16U     = [0xFD] <> u32 159
  write I_I32x4ExtaddPairwiseI16x8S = [0xFD] <> u32 126
  write I_I32x4ExtaddPairwiseI16x8U = [0xFD] <> u32 127
  write I_I32x4Abs                  = [0xFD] <> u32 160
  write I_I32x4Neg                  = [0xFD] <> u32 161
  write I_I32x4AllTrue              = [0xFD] <> u32 163
  write I_I32x4Bitmask              = [0xFD] <> u32 164
  write I_I32x4ExtendLowI16x8S      = [0xFD] <> u32 167
  write I_I32x4ExtendHighI16x8S     = [0xFD] <> u32 168
  write I_I32x4ExtendLowI16x8U      = [0xFD] <> u32 169
  write I_I32x4ExtendHighI16x8U     = [0xFD] <> u32 170
  write I_I32x4Shl                  = [0xFD] <> u32 171
  write I_I32x4ShrS                 = [0xFD] <> u32 172
  write I_I32x4ShrU                 = [0xFD] <> u32 173
  write I_I32x4Add                  = [0xFD] <> u32 174
  write I_I32x4Sub                  = [0xFD] <> u32 177
  write I_I32x4Mul                  = [0xFD] <> u32 181
  write I_I32x4MinS                 = [0xFD] <> u32 182
  write I_I32x4MinU                 = [0xFD] <> u32 183
  write I_I32x4MaxS                 = [0xFD] <> u32 184
  write I_I32x4MaxU                 = [0xFD] <> u32 185
  write I_I32x4DotI16x8S            = [0xFD] <> u32 186
  write I_I32x4ExtmulLowI16x8S      = [0xFD] <> u32 187
  write I_I32x4ExtmulHighI16x8S     = [0xFD] <> u32 188
  write I_I32x4ExtmulLowI16x8U      = [0xFD] <> u32 189
  write I_I32x4ExtmulHighI16x8U     = [0xFD] <> u32 190
  write I_I64x2Abs                  = [0xFD] <> u32 191
  write I_I64x2Neg                  = [0xFD] <> u32 192
  write I_I64x2AllTrue              = [0xFD] <> u32 195
  write I_I64x2Bitmask              = [0xFD] <> u32 196
  write I_I64x2ExtendLowI32x4S      = [0xFD] <> u32 199
  write I_I64x2ExtendHighI32x4S     = [0xFD] <> u32 200
  write I_I64x2ExtendLowI32x4U      = [0xFD] <> u32 201
  write I_I64x2ExtendHighI32x4U     = [0xFD] <> u32 202
  write I_I64x2Shl                  = [0xFD] <> u32 203
  write I_I64x2ShrS                 = [0xFD] <> u32 204
  write I_I64x2ShrU                 = [0xFD] <> u32 205
  write I_I64x2Add                  = [0xFD] <> u32 206
  write I_I64x2Sub                  = [0xFD] <> u32 209
  write I_I64x2Mul                  = [0xFD] <> u32 213
  write I_I64x2ExtmulLowI32x4S      = [0xFD] <> u32 220
  write I_I64x2ExtmulHighI32x4S     = [0xFD] <> u32 221
  write I_I64x2ExtmulLowI32x4U      = [0xFD] <> u32 222
  write I_I64x2ExtmulHighI32x4U     = [0xFD] <> u32 223
  write I_F32x4Ceil                 = [0xFD] <> u32 103
  write I_F32x4Floor                = [0xFD] <> u32 104
  write I_F32x4Trunc                = [0xFD] <> u32 105
  write I_F32x4Nearest              = [0xFD] <> u32 106
  write I_F32x4Abs                  = [0xFD] <> u32 224
  write I_F32x4Neg                  = [0xFD] <> u32 225
  write I_F32x4Sqrt                 = [0xFD] <> u32 227
  write I_F32x4Add                  = [0xFD] <> u32 228
  write I_F32x4Sub                  = [0xFD] <> u32 229
  write I_F32x4Mul                  = [0xFD] <> u32 230
  write I_F32x4Div                  = [0xFD] <> u32 231
  write I_F32x4Min                  = [0xFD] <> u32 232
  write I_F32x4Max                  = [0xFD] <> u32 233
  write I_F32x4Pmin                 = [0xFD] <> u32 234
  write I_F32x4Pmax                 = [0xFD] <> u32 235
  write I_F64x2Ceil                 = [0xFD] <> u32 116
  write I_F64x2Floor                = [0xFD] <> u32 117
  write I_F64x2Trunc                = [0xFD] <> u32 122
  write I_F64x2Nearest              = [0xFD] <> u32 148
  write I_F64x2Abs                  = [0xFD] <> u32 236
  write I_F64x2Neg                  = [0xFD] <> u32 237
  write I_F64x2Sqrt                 = [0xFD] <> u32 239
  write I_F64x2Add                  = [0xFD] <> u32 240
  write I_F64x2Sub                  = [0xFD] <> u32 241
  write I_F64x2Mul                  = [0xFD] <> u32 242
  write I_F64x2Div                  = [0xFD] <> u32 243
  write I_F64x2Min                  = [0xFD] <> u32 244
  write I_F64x2Max                  = [0xFD] <> u32 245
  write I_F64x2Pmin                 = [0xFD] <> u32 246
  write I_F64x2Pmax                 = [0xFD] <> u32 247
  write I_I32x4TruncSatF32x4S       = [0xFD] <> u32 248
  write I_I32x4TruncSatF32x4U       = [0xFD] <> u32 249
  write I_F32x4ConvertI32x4S        = [0xFD] <> u32 250
  write I_F32x4ConvertI32x4U        = [0xFD] <> u32 251
  write I_I32x4TruncSatF64x2SZero   = [0xFD] <> u32 252
  write I_I32x4TruncSatF64x2UZero   = [0xFD] <> u32 253
  write I_F64x2ConvertLowI32x4S     = [0xFD] <> u32 254
  write I_F64x2ConvertLowI32x4U     = [0xFD] <> u32 255
  write I_F32x4DemoteF64x2Zero      = [0xFD] <> u32 94 
  write I_F64x2PromoteLowF32x4      = [0xFD] <> u32 95 
 
instance Writable (Bool, Bool) where
  write (False, False) = [0x00]
  write (True, False) = [0x01]
  write (False, True) = [0x02]
  write (True, True) = [0x02]

instance Writable (Int,Int) where
  write (align, offset) = u32 align <> u32 offset
