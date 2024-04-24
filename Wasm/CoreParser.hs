module Wasm.CoreParser where

import qualified Data.ByteString as B

import Control.Applicative (Alternative (..))
import Data.Word
import Lib.Parser
import Wasm.CommonParsing
import qualified Wasm.CommonWriting as WR
import Wasm.Core
import Prelude hiding (EQ)

core :: Readable Core
core = do items magic
          items version
          items layer
          many (section coreSection) <* eof

coreSection :: Word8 -> Readable Section
coreSection 0 = CustomSection <$> utf8 <*> many byte
coreSection 1 = TypeSection <$> vec recType
coreSection 2 = ImportSection <$> vec importData
coreSection 3 = FunctionSection <$> vec u32
coreSection 4 = TableSection <$> vec table
coreSection 5 = MemorySection <$> vec memType
coreSection 6 = GlobalSection <$> vec global
coreSection 7 = ExportSection <$> vec export
coreSection 8 = StartSection <$> u32
coreSection 9 = ElementSection <$> vec element
coreSection 10 = CodeSection <$> vec code
coreSection 11 = DataSection <$> vec dataData
coreSection 12 = DataCountSection <$> u32
coreSection i = do d <- many byte
                   pure (UnknownSection i d)

-- Type section contents
numType :: Readable NumType
numType = item 0x7F *> pure I32
      <|> item 0x7E *> pure I64
      <|> item 0x7D *> pure F32
      <|> item 0x7C *> pure F64

vecType :: Readable VecType
vecType = item 0x7B *> pure V128

absHeapType :: Readable (HeapType Int)
absHeapType = item 0x73 *> pure NOFUNC
          <|> item 0x72 *> pure NOEXTERN
          <|> item 0x71 *> pure NONE
          <|> item 0x70 *> pure FUNC
          <|> item 0x6F *> pure EXTERN
          <|> item 0x6E *> pure ANY
          <|> item 0x6D *> pure EQ
          <|> item 0x6C *> pure I31
          <|> item 0x6B *> pure STRUCT
          <|> item 0x6A *> pure ARRAY

heapType :: Readable (HeapType Int)
heapType = absHeapType
       <|> HT . fromIntegral <$> leb128
      
refType :: Readable (RefType Int)
refType = item 0x64 *> (Ref False <$> heapType)
      <|> item 0x63 *> (Ref True <$> heapType)
      <|> Ref True <$> absHeapType

valType :: Readable (ValType Int)
valType = N <$> numType
      <|> V <$> vecType
      <|> R <$> refType

resultType :: Readable [ValType Int]
resultType = vec valType

funcType :: Readable ([ValType Int], [ValType Int])
funcType = (,) <$> resultType <*> resultType

arrayType :: Readable (StorageType Int, Mut)
arrayType = fieldType

structType :: Readable [(StorageType Int, Mut)]
structType = vec fieldType

fieldType :: Readable (StorageType Int, Mut)
fieldType = (,) <$> storageType <*> mut

storageType :: Readable (StorageType Int)
storageType = U <$> valType
          <|> P <$> packedType

packedType :: Readable PackedType
packedType = item 0x78 *> pure I8
         <|> item 0x77 *> pure I16

compType :: Readable (CompType Int)
compType = item 0x5E *> (Array <$> arrayType)
       <|> item 0x5F *> (Struct <$> structType)
       <|> item 0x60 *> (Func <$> resultType <*> resultType)

recType :: Readable (RecType Int)
recType = item 0x4E *> vec subType
      <|> pure <$> subType

subType :: Readable (SubType Int)
subType = item 0x50 *> ((Sub False) <$> vec u32 <*> compType)
      <|> item 0x4F *> ((Sub True) <$> vec u32 <*> compType)
      <|> (Sub True []) <$> compType

limits :: Readable Limits
limits = item 0x00 *> ((,Nothing) <$> u32)
     <|> item 0x01 *> ((,) <$> u32 <*> (Just <$> u32))

memType = limits

tableType :: Readable (RefType Int, Limits)
tableType = (,) <$> refType <*> limits

globalType :: Readable (ValType Int, Mut)
globalType = (,) <$> valType <*> mut

mut :: Readable Mut
mut = item 0x00 *> pure Imm
  <|> item 0x01 *> pure Mut

-- Import section contents
importData :: Readable (String, String, ImportDesc)
importData = (,,) <$> utf8 <*> utf8 <*> importDesc

importDesc :: Readable ImportDesc
importDesc = item 0x00 *> (FuncImport <$> u32)
         <|> item 0x01 *> (TableImport <$> tableType)
         <|> item 0x02 *> (MemImport <$> memType)
         <|> item 0x03 *> (GlobalImport <$> globalType)

-- Table section contents
table :: Readable ((RefType Int, Limits), Maybe (Expr Int))
table = (,Nothing) <$> tableType
    <|> items [0x40, 0x00] *> ((,) <$> tableType <*> (Just <$> expr))

-- Global section contents
global :: Readable ((ValType Int, Mut), Expr Int)
global = (,) <$> globalType <*> expr

-- Export section contents
export :: Readable (String, ExportDesc)
export = (,) <$> utf8 <*> exportDesc

exportDesc :: Readable ExportDesc
exportDesc = item 0x00 *> (FuncExport <$> u32)
         <|> item 0x01 *> (TableExport <$> u32)
         <|> item 0x02 *> (MemExport <$> u32)
         <|> item 0x03 *> (GlobalExport <$> u32)

-- Element section contents
element :: Readable Elem
element = item 0x00 *> (Elem0 <$> expr <*> vec u32)
      <|> item 0x01 *> (Elem1 <$> elemKind <*> vec u32)
      <|> item 0x02 *> (Elem2 <$> u32 <*> expr <*> elemKind <*> vec u32)
      <|> item 0x03 *> (Elem3 <$> elemKind <*> vec u32)
      <|> item 0x04 *> (Elem4 <$> expr <*> vec expr)
      <|> item 0x05 *> (Elem5 <$> refType <*> vec expr)
      <|> item 0x06 *> (Elem6 <$> u32 <*> expr <*> refType <*> vec expr)
      <|> item 0x07 *> (Elem7 <$> refType <*> vec expr)

elemKind :: Readable ElemKind
elemKind = item 0x00 *> pure ElemKindRefFunc

-- code section
code :: Readable ([ValType Int], Expr Int)
code = do size <- u32
          subParse size (funcData <* eof)

funcData :: Readable ([ValType Int], Expr Int)
funcData = (,) <$> (concat <$> vec locals) <*> expr

locals :: Readable [ValType Int]
locals = replicate <$> u32 <*> valType

dataData :: Readable ([Word8], DataMode)
dataData = item 0x00 *> (dataMode0 <$> expr <*> vec byte)
       <|> item 0x01 *> (dataMode1 <$> vec byte)
       <|> item 0x02 *> (dataMode2 <$> u32 <*> expr <*> vec byte)

dataMode0 e b = (b, Active 0 e)
dataMode1 b = (b, Passive)
dataMode2 x e b = (b, Active x e)

-- Instructions
blockType :: Readable (BlockType Int)
blockType = item 0x40 *> pure BNone
        <|> BVal <$> valType
        <|> BType . fromIntegral <$> sleb128

expr :: Readable (Expr Int)
expr = many instr <* item 0x0B

instr :: Readable (Instruction Int)
instr = pure I_Unreachable <* item 0x00
    <|> pure I_Nop <* item 0x01
    <|> item 0x02 *> (I_Block <$> blockType <*> many instr) <* item 0x0B
    <|> item 0x03 *> (I_Loop <$> blockType <*> many instr) <* item 0x0B
    <|> item 0x04 *> (I_If <$> blockType <*> many instr) <* item 0x0B
    <|> item 0x04 *> (I_IfElse <$> blockType
                               <*> many instr
                               <*> (item 0x05 *> many instr)) <* item 0x0B
    <|> item 0x0C *> (I_Br <$> u32)
    <|> item 0x0D *> (I_BrIf <$> u32)
    <|> item 0x0E *> (I_BrTable <$> vec u32 <*> u32)
    <|> item 0x0F *> pure I_Return
    <|> item 0x10 *> (I_Call <$> u32)
    <|> item 0x11 *> (I_CallIndirect <$> u32 <*> u32)
    <|> item 0x12 *> (I_ReturnCall <$> u32)
    <|> item 0x13 *> (I_ReturnCallIndirect <$> u32 <*> u32)
    <|> item 0x14 *> (I_CallRef <$> u32)
    <|> item 0x15 *> (I_ReturnCallRef <$> u32)
    <|> item 0xD5 *> (I_BrOnNull <$> u32)
    <|> item 0xD6 *> (I_BrOnNonNull <$> u32)
    <|> item 0xFB *> p32 24 *> (I_BrOnCast <$> castFlags
                                           <*> u32
                                           <*> heapType
                                           <*> heapType)
    <|> item 0xFB *> p32 25 *> (I_BrOnCastFail
                                           <$> castFlags
                                           <*> u32
                                           <*> heapType
                                           <*> heapType)
    <|> item 0xD0 *> (I_RefNull <$> heapType)
    <|> item 0xD1 *> pure I_RefIsNull
    <|> item 0xD2 *> (I_RefFunc <$> u32)
    <|> item 0xD3 *> pure I_RefEq
    <|> item 0xD4 *> pure I_RefAsNonNull
    <|> item 0xFB *> p32 0 *> (I_StructNew <$> u32)
    <|> item 0xFB *> p32 1 *> (I_StructNewDefault <$> u32)
    <|> item 0xFB *> p32 2 *> (I_StructGet <$> u32 <*> u32)
    <|> item 0xFB *> p32 3 *> (I_StructGetS <$> u32 <*> u32)
    <|> item 0xFB *> p32 4 *> (I_StructGetU <$> u32 <*> u32)
    <|> item 0xFB *> p32 5 *> (I_StructSet <$> u32 <*> u32)
    <|> item 0xFB *> p32 6 *> (I_ArrayNew <$> u32)
    <|> item 0xFB *> p32 7 *> (I_ArrayNewDefault <$> u32)
    <|> item 0xFB *> p32 8 *> (I_ArrayNewFixed <$> u32 <*> u32)
    <|> item 0xFB *> p32 9 *> (I_ArrayNewData <$> u32 <*> u32)
    <|> item 0xFB *> p32 10 *> (I_ArrayNewElem <$> u32 <*> u32)
    <|> item 0xFB *> p32 11 *> (I_ArrayGet <$> u32)
    <|> item 0xFB *> p32 12 *> (I_ArrayGetS <$> u32)
    <|> item 0xFB *> p32 13 *> (I_ArrayGetU <$> u32)
    <|> item 0xFB *> p32 14 *> (I_ArraySet <$> u32)
    <|> item 0xFB *> p32 15 *> pure I_ArrayLen
    <|> item 0xFB *> p32 16 *> (I_ArrayFill <$> u32)
    <|> item 0xFB *> p32 17 *> (I_ArrayCopy <$> u32 <*> u32)
    <|> item 0xFB *> p32 18 *> (I_ArrayInitData <$> u32 <*> u32)
    <|> item 0xFB *> p32 19 *> (I_ArrayInitElem <$> u32 <*> u32)
    <|> item 0xFB *> p32 20 *> (I_RefTest False <$> heapType)
    <|> item 0xFB *> p32 21 *> (I_RefTest True <$> heapType)
    <|> item 0xFB *> p32 22 *> (I_RefCast False <$> heapType)
    <|> item 0xFB *> p32 23 *> (I_RefCast True <$> heapType)
    <|> item 0xFB *> p32 26 *> pure I_AnyConvertExtern
    <|> item 0xFB *> p32 27 *> pure I_ExternConvertAny
    <|> item 0xFB *> p32 28 *> pure I_RefI31
    <|> item 0xFB *> p32 29 *> pure I_I31GetS
    <|> item 0xFB *> p32 30 *> pure I_I31GetU
    <|> item 0x1A *> pure I_Drop
    <|> item 0x1B *> pure I_Select
    <|> item 0x1C *> (I_SelectT <$> vec valType)
    <|> item 0x20 *> (I_LocalGet <$> u32)
    <|> item 0x21 *> (I_LocalSet <$> u32)
    <|> item 0x22 *> (I_LocalTee <$> u32)
    <|> item 0x23 *> (I_GlobalGet <$> u32)
    <|> item 0x24 *> (I_GlobalSet <$> u32)
    <|> item 0x25 *> (I_TableGet <$> u32)
    <|> item 0x26 *> (I_TableSet <$> u32)
    <|> item 0xFC *> p32 12 *> (I_TableInit <$> u32 <*> u32)
    <|> item 0xFC *> p32 13 *> (I_ElemDrop <$> u32)
    <|> item 0xFC *> p32 14 *> (I_TableCopy <$> u32 <*> u32)
    <|> item 0xFC *> p32 15 *> (I_TableGrow <$> u32)
    <|> item 0xFC *> p32 16 *> (I_TableSize <$> u32)
    <|> item 0xFC *> p32 17 *> (I_TableFill <$> u32)
    <|> item 0x28 *> (I_I32Load <$> memArg)
    <|> item 0x29 *> (I_I64Load    <$> memArg)
    <|> item 0x2A *> (I_F32Load    <$> memArg)
    <|> item 0x2B *> (I_F64Load    <$> memArg)
    <|> item 0x2C *> (I_I32Load8S  <$> memArg)
    <|> item 0x2D *> (I_I32Load8U  <$> memArg)
    <|> item 0x2E *> (I_I32Load16S <$> memArg)
    <|> item 0x2F *> (I_I32Load16U <$> memArg)
    <|> item 0x30 *> (I_I64Load8S  <$> memArg)
    <|> item 0x31 *> (I_I64Load8U  <$> memArg)
    <|> item 0x32 *> (I_I64Load16S <$> memArg)
    <|> item 0x33 *> (I_I64Load16U <$> memArg)
    <|> item 0x34 *> (I_I64Load32S <$> memArg)
    <|> item 0x35 *> (I_I64Load32U <$> memArg)
    <|> item 0x36 *> (I_I32Store   <$> memArg)
    <|> item 0x37 *> (I_I64Store   <$> memArg)
    <|> item 0x38 *> (I_F32Store   <$> memArg)
    <|> item 0x39 *> (I_F64Store   <$> memArg)
    <|> item 0x3A *> (I_I32Store8  <$> memArg)
    <|> item 0x3B *> (I_I32Store16 <$> memArg)
    <|> item 0x3C *> (I_I64Store8  <$> memArg)
    <|> item 0x3D *> (I_I64Store16 <$> memArg)
    <|> item 0x3E *> (I_I64Store32 <$> memArg)
    <|> item 0x3F *> item 0x00 *> pure I_MemorySize
    <|> item 0x40 *> item 0x00 *> pure I_MemoryGrow
    <|> item 0xFC *> p32 8 *> (I_MemoryInit <$> u32) <* item 0x00
    <|> item 0xFC *> p32 9 *> (I_DataDrop <$> u32)
    <|> item 0xFC *> p32 10 *> item 0x00 *> item 0x00 *> pure I_MemoryCopy
    <|> item 0xFC *> p32 11 *> item 0x00 *> pure I_MemoryFill
    <|> item 0x41 *> (I_I32Const <$> sleb128)
    <|> item 0x42 *> (I_I64Const <$> sleb128)
    <|> item 0x43 *> (I_F32Const <$> takeN 4)
    <|> item 0x44 *> (I_F64Const <$> takeN 8)
    <|> item 0x45 *> pure I_I32Eqz
    <|> item 0x46 *> pure I_I32Eq
    <|> item 0x47 *> pure I_I32Ne
    <|> item 0x48 *> pure I_I32LtS
    <|> item 0x49 *> pure I_I32LtU
    <|> item 0x4A *> pure I_I32GtS
    <|> item 0x4B *> pure I_I32GtU
    <|> item 0x4C *> pure I_I32LeS
    <|> item 0x4D *> pure I_I32LeU
    <|> item 0x4E *> pure I_I32GeS
    <|> item 0x4F *> pure I_I32GeU
    <|> item 0x50 *> pure I_I64Eqz
    <|> item 0x51 *> pure I_I64Eq
    <|> item 0x52 *> pure I_I64Ne
    <|> item 0x53 *> pure I_I64LtS
    <|> item 0x54 *> pure I_I64LtU
    <|> item 0x55 *> pure I_I64GtS
    <|> item 0x56 *> pure I_I64GtU
    <|> item 0x57 *> pure I_I64LeS
    <|> item 0x58 *> pure I_I64LeU
    <|> item 0x59 *> pure I_I64GeS
    <|> item 0x5A *> pure I_I64GeU
    <|> item 0x5B *> pure I_F32Eq
    <|> item 0x5C *> pure I_F32Ne
    <|> item 0x5D *> pure I_F32Lt
    <|> item 0x5E *> pure I_F32Gt
    <|> item 0x5F *> pure I_F32Le
    <|> item 0x60 *> pure I_F32Ge
    <|> item 0x61 *> pure I_F64Eq
    <|> item 0x62 *> pure I_F64Ne
    <|> item 0x63 *> pure I_F64Lt
    <|> item 0x64 *> pure I_F64Gt
    <|> item 0x65 *> pure I_F64Le
    <|> item 0x66 *> pure I_F64Ge
    <|> item 0x67 *> pure I_I32Clz
    <|> item 0x68 *> pure I_I32Ctz
    <|> item 0x69 *> pure I_I32Popcnt
    <|> item 0x6A *> pure I_I32Add
    <|> item 0x6B *> pure I_I32Sub
    <|> item 0x6C *> pure I_I32Mul
    <|> item 0x6D *> pure I_I32DivS
    <|> item 0x6E *> pure I_I32DivU
    <|> item 0x6F *> pure I_I32RemS
    <|> item 0x70 *> pure I_I32RemU
    <|> item 0x71 *> pure I_I32And
    <|> item 0x72 *> pure I_I32Or
    <|> item 0x73 *> pure I_I32Xor
    <|> item 0x74 *> pure I_I32Shl
    <|> item 0x75 *> pure I_I32ShrS
    <|> item 0x76 *> pure I_I32ShrU
    <|> item 0x77 *> pure I_I32Rotl
    <|> item 0x78 *> pure I_I32Rotr
    <|> item 0x79 *> pure I_I64Clz
    <|> item 0x7A *> pure I_I64Ctz
    <|> item 0x7B *> pure I_I64Popcnt
    <|> item 0x7C *> pure I_I64Add
    <|> item 0x7D *> pure I_I64Sub
    <|> item 0x7E *> pure I_I64Mul
    <|> item 0x7F *> pure I_I64DivS
    <|> item 0x80 *> pure I_I64DivU
    <|> item 0x81 *> pure I_I64RemS
    <|> item 0x82 *> pure I_I64RemU
    <|> item 0x83 *> pure I_I64And
    <|> item 0x84 *> pure I_I64Or
    <|> item 0x85 *> pure I_I64Xor
    <|> item 0x86 *> pure I_I64Shl
    <|> item 0x87 *> pure I_I64ShrS
    <|> item 0x88 *> pure I_I64ShrU
    <|> item 0x89 *> pure I_I64Rotl
    <|> item 0x8A *> pure I_I64Rotr
    <|> item 0x8B *> pure I_F32Abs
    <|> item 0x8C *> pure I_F32Neg
    <|> item 0x8D *> pure I_F32Ceil
    <|> item 0x8E *> pure I_F32Floor
    <|> item 0x8F *> pure I_F32Trunc
    <|> item 0x90 *> pure I_F32Nearest
    <|> item 0x91 *> pure I_F32Sqrt
    <|> item 0x92 *> pure I_F32Add
    <|> item 0x93 *> pure I_F32Sub
    <|> item 0x94 *> pure I_F32Mul
    <|> item 0x95 *> pure I_F32Div
    <|> item 0x96 *> pure I_F32Min
    <|> item 0x97 *> pure I_F32Max
    <|> item 0x98 *> pure I_F32CopySign
    <|> item 0x99 *> pure I_F64Abs
    <|> item 0x9A *> pure I_F64Neg
    <|> item 0x9B *> pure I_F64Ceil
    <|> item 0x9C *> pure I_F64Floor
    <|> item 0x9D *> pure I_F64Trunc
    <|> item 0x9E *> pure I_F64Nearest
    <|> item 0x9F *> pure I_F64Sqrt
    <|> item 0xA0 *> pure I_F64Add
    <|> item 0xA1 *> pure I_F64Sub
    <|> item 0xA2 *> pure I_F64Mul
    <|> item 0xA3 *> pure I_F64Div
    <|> item 0xA4 *> pure I_F64Min
    <|> item 0xA5 *> pure I_F64Max
    <|> item 0xA6 *> pure I_F64CopySign
    <|> item 0xA7 *> pure I_I32WrapI64
    <|> item 0xA8 *> pure I_I32TruncF32S
    <|> item 0xA9 *> pure I_I32TruncF32U
    <|> item 0xAA *> pure I_I32TruncF64S
    <|> item 0xAB *> pure I_I32TruncF64U
    <|> item 0xAC *> pure I_I64ExtendI32S
    <|> item 0xAD *> pure I_I64ExtendI32U
    <|> item 0xAE *> pure I_I64TruncF32S
    <|> item 0xAF *> pure I_I64TruncF32U
    <|> item 0xB0 *> pure I_I64TruncF64S
    <|> item 0xB1 *> pure I_I64TruncF64U
    <|> item 0xB2 *> pure I_F32ConvertI32S
    <|> item 0xB3 *> pure I_F32ConvertI32U
    <|> item 0xB4 *> pure I_F32ConvertI64S
    <|> item 0xB5 *> pure I_F32ConvertI64U
    <|> item 0xB6 *> pure I_F32DemoteF64
    <|> item 0xB7 *> pure I_F64ConvertI32S
    <|> item 0xB8 *> pure I_F64ConvertI32U
    <|> item 0xB9 *> pure I_F64ConvertI64S
    <|> item 0xBA *> pure I_F64ConvertI64U
    <|> item 0xBB *> pure I_F64PromoteF32
    <|> item 0xBC *> pure I_I32ReinterpretF32
    <|> item 0xBD *> pure I_I64ReinterpretF64
    <|> item 0xBE *> pure I_F32ReinterpretI32
    <|> item 0xBF *> pure I_F64ReinterpretI64
    <|> item 0xC0 *> pure I_I32Extend8S
    <|> item 0xC1 *> pure I_I32Extend16S
    <|> item 0xC2 *> pure I_I64Extend8S
    <|> item 0xC3 *> pure I_I64Extend16S
    <|> item 0xC4 *> pure I_I64Extend32S
    <|> item 0xFC *> p32 0 *> pure I_I32TruncSatF32S
    <|> item 0xFC *> p32 1 *> pure I_I32TruncSatF32U
    <|> item 0xFC *> p32 2 *> pure I_I32TruncSatF64S
    <|> item 0xFC *> p32 3 *> pure I_I32TruncSatF64U
    <|> item 0xFC *> p32 4 *> pure I_I64TruncSatF32S
    <|> item 0xFC *> p32 5 *> pure I_I64TruncSatF32U
    <|> item 0xFC *> p32 6 *> pure I_I64TruncSatF64S
    <|> item 0xFC *> p32 7 *> pure I_I64TruncSatF64U
    <|> item 0xFD *> p32 0 *> (I_V128Load        <$> memArg)
    <|> item 0xFD *> p32 1 *> (I_V128Load8x8S    <$> memArg)
    <|> item 0xFD *> p32 2 *> (I_V128Load8x8U    <$> memArg)
    <|> item 0xFD *> p32 3 *> (I_V128Load16x4S   <$> memArg)
    <|> item 0xFD *> p32 4 *> (I_V128Load16x4U   <$> memArg)
    <|> item 0xFD *> p32 5 *> (I_V128Load32x2S   <$> memArg)
    <|> item 0xFD *> p32 6 *> (I_V128Load32x2U   <$> memArg)
    <|> item 0xFD *> p32 7 *> (I_V128Load8Splat  <$> memArg)
    <|> item 0xFD *> p32 8 *> (I_V128Load16Splat <$> memArg)
    <|> item 0xFD *> p32 9 *> (I_V128Load32Splat <$> memArg)
    <|> item 0xFD *> p32 10 *> (I_V128Load64Splat <$> memArg)
    <|> item 0xFD *> p32 92 *> (I_V128Load32Zero  <$> memArg)
    <|> item 0xFD *> p32 93 *> (I_V128Load64Zero  <$> memArg)
    <|> item 0xFD *> p32 11 *> (I_V128Store       <$> memArg)
    <|> item 0xFD *> p32 84 *> (I_V128Load8Lane   <$> memArg <*> u32)
    <|> item 0xFD *> p32 85 *> (I_V128Load16Lane  <$> memArg <*> u32)
    <|> item 0xFD *> p32 86 *> (I_V128Load32Lane  <$> memArg <*> u32)
    <|> item 0xFD *> p32 87 *> (I_V128Load64Lane  <$> memArg <*> u32)
    <|> item 0xFD *> p32 88 *> (I_V128Store8Lane  <$> memArg <*> u32)
    <|> item 0xFD *> p32 89 *> (I_V128Store16Lane <$> memArg <*> u32)
    <|> item 0xFD *> p32 90 *> (I_V128Store32Lane <$> memArg <*> u32)
    <|> item 0xFD *> p32 91 *> (I_V128Store64Lane <$> memArg <*> u32)
    <|> item 0xFD *> p32 12 *> (I_V128Const <$> takeN 16)
    <|> item 0xFD *> p32 13 *> (I_I8x16Shuffle <$> nTimes 16 u32)
    <|> item 0xFD *> p32 21 *> (I_I8x16ExtractLaneS <$> u32)
    <|> item 0xFD *> p32 22 *> (I_I8x16ExtractLaneU <$> u32)
    <|> item 0xFD *> p32 23 *> (I_I8x16ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 24 *> (I_I16x8ExtractLaneS <$> u32)
    <|> item 0xFD *> p32 25 *> (I_I16x8ExtractLaneU <$> u32)
    <|> item 0xFD *> p32 26 *> (I_I16x8ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 27 *> (I_I32x4ExtractLane  <$> u32)
    <|> item 0xFD *> p32 28 *> (I_I32x4ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 29 *> (I_I64x2ExtractLane  <$> u32)
    <|> item 0xFD *> p32 30 *> (I_I64x2ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 31 *> (I_F32x4ExtractLane  <$> u32)
    <|> item 0xFD *> p32 32 *> (I_F32x4ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 33 *> (I_F64x2ExtractLane  <$> u32)
    <|> item 0xFD *> p32 34 *> (I_F64x2ReplaceLane  <$> u32)
    <|> item 0xFD *> p32 14 *> pure I_I8x16Swizzle
    <|> item 0xFD *> p32 15 *> pure I_I8x16Splat
    <|> item 0xFD *> p32 16 *> pure I_I16x8Splat
    <|> item 0xFD *> p32 17 *> pure I_I32x4Splat
    <|> item 0xFD *> p32 18 *> pure I_I64x2Splat
    <|> item 0xFD *> p32 19 *> pure I_F32x4Splat
    <|> item 0xFD *> p32 20 *> pure I_F64x2Splat
    <|> item 0xFD *> p32 35 *> pure I_I8x16Eq
    <|> item 0xFD *> p32 36 *> pure I_I8x16Ne
    <|> item 0xFD *> p32 37 *> pure I_I8x16LtS
    <|> item 0xFD *> p32 38 *> pure I_I8x16LtU
    <|> item 0xFD *> p32 39 *> pure I_I8x16GtS
    <|> item 0xFD *> p32 40 *> pure I_I8x16GtU
    <|> item 0xFD *> p32 41 *> pure I_I8x16LeS
    <|> item 0xFD *> p32 42 *> pure I_I8x16LeU
    <|> item 0xFD *> p32 43 *> pure I_I8x16GeS
    <|> item 0xFD *> p32 44 *> pure I_I8x16GeU
    <|> item 0xFD *> p32 45 *> pure I_I16x8Eq
    <|> item 0xFD *> p32 46 *> pure I_I16x8Ne
    <|> item 0xFD *> p32 47 *> pure I_I16x8LtS
    <|> item 0xFD *> p32 48 *> pure I_I16x8LtU
    <|> item 0xFD *> p32 49 *> pure I_I16x8GtS
    <|> item 0xFD *> p32 50 *> pure I_I16x8GtU
    <|> item 0xFD *> p32 51 *> pure I_I16x8LeS
    <|> item 0xFD *> p32 52 *> pure I_I16x8LeU
    <|> item 0xFD *> p32 53 *> pure I_I16x8GeS
    <|> item 0xFD *> p32 54 *> pure I_I16x8GeU
    <|> item 0xFD *> p32 55 *> pure I_I32x4Eq
    <|> item 0xFD *> p32 56 *> pure I_I32x4Ne
    <|> item 0xFD *> p32 57 *> pure I_I32x4LtS
    <|> item 0xFD *> p32 58 *> pure I_I32x4LtU
    <|> item 0xFD *> p32 59 *> pure I_I32x4GtS
    <|> item 0xFD *> p32 60 *> pure I_I32x4GtU
    <|> item 0xFD *> p32 61 *> pure I_I32x4LeS
    <|> item 0xFD *> p32 62 *> pure I_I32x4LeU
    <|> item 0xFD *> p32 63 *> pure I_I32x4GeS
    <|> item 0xFD *> p32 64 *> pure I_I32x4GeU
    <|> item 0xFD *> p32 214 *> pure I_I64x2Eq
    <|> item 0xFD *> p32 215 *> pure I_I64x2Ne
    <|> item 0xFD *> p32 216 *> pure I_I64x2LtS
    <|> item 0xFD *> p32 217 *> pure I_I64x2GtS
    <|> item 0xFD *> p32 218 *> pure I_I64x2LeS
    <|> item 0xFD *> p32 219 *> pure I_I64x2GeS
    <|> item 0xFD *> p32 65 *> pure I_F32x4Eq
    <|> item 0xFD *> p32 66 *> pure I_F32x4Ne
    <|> item 0xFD *> p32 67 *> pure I_F32x4Lt
    <|> item 0xFD *> p32 68 *> pure I_F32x4Gt
    <|> item 0xFD *> p32 69 *> pure I_F32x4Le
    <|> item 0xFD *> p32 70 *> pure I_F32x4Ge
    <|> item 0xFD *> p32 71 *> pure I_F64x2Eq
    <|> item 0xFD *> p32 72 *> pure I_F64x2Ne
    <|> item 0xFD *> p32 73 *> pure I_F64x2Lt
    <|> item 0xFD *> p32 74 *> pure I_F64x2Gt
    <|> item 0xFD *> p32 75 *> pure I_F64x2Le
    <|> item 0xFD *> p32 76 *> pure I_F64x2Ge
    <|> item 0xFD *> p32 77 *> pure I_V128Not
    <|> item 0xFD *> p32 78 *> pure I_V128And
    <|> item 0xFD *> p32 79 *> pure I_V128AndNot
    <|> item 0xFD *> p32 80 *> pure I_V128Or
    <|> item 0xFD *> p32 81 *> pure I_V128Xor
    <|> item 0xFD *> p32 82 *> pure I_V128Bitselect
    <|> item 0xFD *> p32 83 *> pure I_V128AnyTrue
    <|> item 0xFD *> p32 96 *> pure I_I8x16Abs
    <|> item 0xFD *> p32 97 *> pure I_I8x16Neg
    <|> item 0xFD *> p32 98 *> pure I_I8x16Popcnt
    <|> item 0xFD *> p32 99 *> pure I_I8x16AllTrue
    <|> item 0xFD *> p32 100 *> pure I_I8x16Bitmask
    <|> item 0xFD *> p32 101 *> pure I_I8x16NarrowI16x8S
    <|> item 0xFD *> p32 102 *> pure I_I8x16NarrowI16x8U
    <|> item 0xFD *> p32 107 *> pure I_I8x16Shl
    <|> item 0xFD *> p32 108 *> pure I_I8x16ShrS
    <|> item 0xFD *> p32 109 *> pure I_I8x16ShrU
    <|> item 0xFD *> p32 110 *> pure I_I8x16Add
    <|> item 0xFD *> p32 111 *> pure I_I8x16AddSatS
    <|> item 0xFD *> p32 112 *> pure I_I8x16AddSatU
    <|> item 0xFD *> p32 113 *> pure I_I8x16Sub
    <|> item 0xFD *> p32 114 *> pure I_I8x16SubSatS
    <|> item 0xFD *> p32 115 *> pure I_I8x16SubSatU
    <|> item 0xFD *> p32 118 *> pure I_I8x16MinS
    <|> item 0xFD *> p32 119 *> pure I_I8x16MinU
    <|> item 0xFD *> p32 120 *> pure I_I8x16MaxS
    <|> item 0xFD *> p32 121 *> pure I_I8x16MaxU
    <|> item 0xFD *> p32 123 *> pure I_I8x16AvgrU
    <|> item 0xFD *> p32 124 *> pure I_I16x8ExtaddPairwiseI8x16S
    <|> item 0xFD *> p32 125 *> pure I_I16x8ExtaddPairwiseI8x16U
    <|> item 0xFD *> p32 128 *> pure I_I16x8Abs
    <|> item 0xFD *> p32 129 *> pure I_I16x8Neg
    <|> item 0xFD *> p32 130 *> pure I_I16x8Q15mulrSatS
    <|> item 0xFD *> p32 131 *> pure I_I16x8AllTrue
    <|> item 0xFD *> p32 132 *> pure I_I16x8Bitmask
    <|> item 0xFD *> p32 133 *> pure I_I16x8NarrowI32x4S
    <|> item 0xFD *> p32 134 *> pure I_I16x8NarrowI32x4U
    <|> item 0xFD *> p32 135 *> pure I_I16x8ExtendLowI8x16S
    <|> item 0xFD *> p32 136 *> pure I_I16x8ExtendHighI8x16S
    <|> item 0xFD *> p32 137 *> pure I_I16x8ExtendLowI8x16U
    <|> item 0xFD *> p32 138 *> pure I_I16x8ExtendHighI8x16U
    <|> item 0xFD *> p32 139 *> pure I_I16x8Shl
    <|> item 0xFD *> p32 140 *> pure I_I16x8ShrS
    <|> item 0xFD *> p32 141 *> pure I_I16x8ShrU
    <|> item 0xFD *> p32 142 *> pure I_I16x8Add
    <|> item 0xFD *> p32 143 *> pure I_I16x8AddSatS
    <|> item 0xFD *> p32 144 *> pure I_I16x8AddSatU
    <|> item 0xFD *> p32 145 *> pure I_I16x8Sub
    <|> item 0xFD *> p32 146 *> pure I_I16x8SubSatS
    <|> item 0xFD *> p32 147 *> pure I_I16x8SubSatU
    <|> item 0xFD *> p32 148 *> pure I_I16x8Mul
    <|> item 0xFD *> p32 149 *> pure I_I16x8MinS
    <|> item 0xFD *> p32 150 *> pure I_I16x8MinU
    <|> item 0xFD *> p32 151 *> pure I_I16x8MaxS
    <|> item 0xFD *> p32 152 *> pure I_I16x8MaxU
    <|> item 0xFD *> p32 155 *> pure I_I16x8AvgrU
    <|> item 0xFD *> p32 156 *> pure I_I16x8ExtmulLowI8x16S
    <|> item 0xFD *> p32 157 *> pure I_I16x8ExtmulHighI8x16S
    <|> item 0xFD *> p32 158 *> pure I_I16x8ExtmulLowI8x16U
    <|> item 0xFD *> p32 159 *> pure I_I16x8ExtmulHighI8x16U
    <|> item 0xFD *> p32 126 *> pure I_I32x4ExtaddPairwiseI16x8S
    <|> item 0xFD *> p32 127 *> pure I_I32x4ExtaddPairwiseI16x8U
    <|> item 0xFD *> p32 160 *> pure I_I32x4Abs
    <|> item 0xFD *> p32 161 *> pure I_I32x4Neg
    <|> item 0xFD *> p32 163 *> pure I_I32x4AllTrue
    <|> item 0xFD *> p32 164 *> pure I_I32x4Bitmask
    <|> item 0xFD *> p32 167 *> pure I_I32x4ExtendLowI16x8S
    <|> item 0xFD *> p32 168 *> pure I_I32x4ExtendHighI16x8S
    <|> item 0xFD *> p32 169 *> pure I_I32x4ExtendLowI16x8U
    <|> item 0xFD *> p32 170 *> pure I_I32x4ExtendHighI16x8U
    <|> item 0xFD *> p32 171 *> pure I_I32x4Shl
    <|> item 0xFD *> p32 172 *> pure I_I32x4ShrS
    <|> item 0xFD *> p32 173 *> pure I_I32x4ShrU
    <|> item 0xFD *> p32 174 *> pure I_I32x4Add
    <|> item 0xFD *> p32 177 *> pure I_I32x4Sub
    <|> item 0xFD *> p32 181 *> pure I_I32x4Mul
    <|> item 0xFD *> p32 182 *> pure I_I32x4MinS
    <|> item 0xFD *> p32 183 *> pure I_I32x4MinU
    <|> item 0xFD *> p32 184 *> pure I_I32x4MaxS
    <|> item 0xFD *> p32 185 *> pure I_I32x4MaxU
    <|> item 0xFD *> p32 186 *> pure I_I32x4DotI16x8S
    <|> item 0xFD *> p32 187 *> pure I_I32x4ExtmulLowI16x8S
    <|> item 0xFD *> p32 188 *> pure I_I32x4ExtmulHighI16x8S
    <|> item 0xFD *> p32 189 *> pure I_I32x4ExtmulLowI16x8U
    <|> item 0xFD *> p32 190 *> pure I_I32x4ExtmulHighI16x8U
    <|> item 0xFD *> p32 191 *> pure I_I64x2Abs
    <|> item 0xFD *> p32 192 *> pure I_I64x2Neg
    <|> item 0xFD *> p32 195 *> pure I_I64x2AllTrue
    <|> item 0xFD *> p32 196 *> pure I_I64x2Bitmask
    <|> item 0xFD *> p32 199 *> pure I_I64x2ExtendLowI32x4S
    <|> item 0xFD *> p32 200 *> pure I_I64x2ExtendHighI32x4S
    <|> item 0xFD *> p32 201 *> pure I_I64x2ExtendLowI32x4U
    <|> item 0xFD *> p32 202 *> pure I_I64x2ExtendHighI32x4U
    <|> item 0xFD *> p32 203 *> pure I_I64x2Shl
    <|> item 0xFD *> p32 204 *> pure I_I64x2ShrS
    <|> item 0xFD *> p32 205 *> pure I_I64x2ShrU
    <|> item 0xFD *> p32 206 *> pure I_I64x2Add
    <|> item 0xFD *> p32 209 *> pure I_I64x2Sub
    <|> item 0xFD *> p32 213 *> pure I_I64x2Mul
    <|> item 0xFD *> p32 220 *> pure I_I64x2ExtmulLowI32x4S
    <|> item 0xFD *> p32 221 *> pure I_I64x2ExtmulHighI32x4S
    <|> item 0xFD *> p32 222 *> pure I_I64x2ExtmulLowI32x4U
    <|> item 0xFD *> p32 223 *> pure I_I64x2ExtmulHighI32x4U
    <|> item 0xFD *> p32 103 *> pure I_F32x4Ceil
    <|> item 0xFD *> p32 104 *> pure I_F32x4Floor
    <|> item 0xFD *> p32 105 *> pure I_F32x4Trunc
    <|> item 0xFD *> p32 106 *> pure I_F32x4Nearest
    <|> item 0xFD *> p32 224 *> pure I_F32x4Abs
    <|> item 0xFD *> p32 225 *> pure I_F32x4Neg
    <|> item 0xFD *> p32 227 *> pure I_F32x4Sqrt
    <|> item 0xFD *> p32 228 *> pure I_F32x4Add
    <|> item 0xFD *> p32 229 *> pure I_F32x4Sub
    <|> item 0xFD *> p32 230 *> pure I_F32x4Mul
    <|> item 0xFD *> p32 231 *> pure I_F32x4Div
    <|> item 0xFD *> p32 232 *> pure I_F32x4Min
    <|> item 0xFD *> p32 233 *> pure I_F32x4Max
    <|> item 0xFD *> p32 234 *> pure I_F32x4Pmin
    <|> item 0xFD *> p32 235 *> pure I_F32x4Pmax
    <|> item 0xFD *> p32 116 *> pure I_F64x2Ceil
    <|> item 0xFD *> p32 117 *> pure I_F64x2Floor
    <|> item 0xFD *> p32 122 *> pure I_F64x2Trunc
    <|> item 0xFD *> p32 148 *> pure I_F64x2Nearest
    <|> item 0xFD *> p32 236 *> pure I_F64x2Abs
    <|> item 0xFD *> p32 237 *> pure I_F64x2Neg
    <|> item 0xFD *> p32 239 *> pure I_F64x2Sqrt
    <|> item 0xFD *> p32 240 *> pure I_F64x2Add
    <|> item 0xFD *> p32 241 *> pure I_F64x2Sub
    <|> item 0xFD *> p32 242 *> pure I_F64x2Mul
    <|> item 0xFD *> p32 243 *> pure I_F64x2Div
    <|> item 0xFD *> p32 244 *> pure I_F64x2Min
    <|> item 0xFD *> p32 245 *> pure I_F64x2Max
    <|> item 0xFD *> p32 246 *> pure I_F64x2Pmin
    <|> item 0xFD *> p32 247 *> pure I_F64x2Pmax
    <|> item 0xFD *> p32 248 *> pure I_I32x4TruncSatF32x4S
    <|> item 0xFD *> p32 249 *> pure I_I32x4TruncSatF32x4U
    <|> item 0xFD *> p32 250 *> pure I_F32x4ConvertI32x4S
    <|> item 0xFD *> p32 251 *> pure I_F32x4ConvertI32x4U
    <|> item 0xFD *> p32 252 *> pure I_I32x4TruncSatF64x2SZero
    <|> item 0xFD *> p32 253 *> pure I_I32x4TruncSatF64x2UZero
    <|> item 0xFD *> p32 254 *> pure I_F64x2ConvertLowI32x4S
    <|> item 0xFD *> p32 255 *> pure I_F64x2ConvertLowI32x4U
    <|> item 0xFD *> p32 94 *> pure I_F32x4DemoteF64x2Zero
    <|> item 0xFD *> p32 95 *> pure I_F64x2PromoteLowF32x4

p32 :: Integer -> Readable [Word8]
p32 i = items (WR.leb128 i)

castFlags :: Readable (Bool, Bool)
castFlags = item 0x00 *> pure (False, False)
        <|> item 0x01 *> pure (True, False)
        <|> item 0x02 *> pure (False, True)
        <|> item 0x03 *> pure (True, True)

memArg :: Readable (Int, Int) -- align, offset
memArg = (,) <$> u32 <*> u32

laneidx :: Readable Word8
laneidx = byte
