{-# LANGUAGE OverloadedStrings, TypeFamilies #-}
module Wasm.Core where

import Data.Maybe (mapMaybe)
import Data.List (nub, sort)
import Data.String (IsString(..))
import Data.Word (Word8)

magic, version, layer :: [Word8]
magic   = [0x00, 0x61, 0x73, 0x6D]
version = [0x01, 0x00]
layer   = [0x00, 0x00]

-- Sections must come in correct order, described by
-- https://webassembly.github.io/gc/core/binary/modules.html#binary-module
type Core = [Section]

data Section
  = CustomSection String [Word8]
  | TypeSection [RecType Int]
  | ImportSection [(String, String, ImportDesc Int)]
  | FunctionSection [TypeIdx]
  | TableSection [((RefType Int, Limits), Maybe (Expr Int))]
  | MemorySection [Limits]
  | GlobalSection [((ValType Int, Mut), (Expr Int))]
  | ExportSection [(String, ExportDesc)]
  | StartSection FuncIdx
  | ElementSection [Elem]
  | CodeSection [([ValType Int], Expr Int)]
  | DataSection [([Word8], DataMode)]
  | DataCountSection Int
  | UnknownSection Word8 [Word8]
  deriving (Show)

type TypeIdx = Idx
type FuncIdx = Idx
type TableIdx = Idx
type MemIdx = Idx
type GlobalIdx = Idx
type ElemIdx = Idx
type DataIdx = Idx
type LocalIdx = Idx
type LabelIdx = Idx
type Idx = Int

sectionId :: Num n => Section -> n
sectionId (CustomSection _ _) = 0
sectionId (TypeSection _) = 1
sectionId (ImportSection _) = 2
sectionId (FunctionSection _) = 3
sectionId (TableSection _) = 4
sectionId (MemorySection _) = 5
sectionId (GlobalSection _) = 6
sectionId (ExportSection _) = 7
sectionId (StartSection _) = 8
sectionId (ElementSection _) = 9
sectionId (CodeSection _) = 10
sectionId (DataSection _) = 11
sectionId (DataCountSection _) = 12

sectionOrder :: Num n => Section -> n
sectionOrder (CustomSection _ _) = 0
sectionOrder (TypeSection _) = 1
sectionOrder (ImportSection _) = 2
sectionOrder (FunctionSection _) = 3
sectionOrder (TableSection _) = 4
sectionOrder (MemorySection _) = 5
sectionOrder (GlobalSection _) = 6
sectionOrder (ExportSection _) = 7
sectionOrder (StartSection _) = 8
sectionOrder (ElementSection _) = 9
sectionOrder (DataCountSection _) = 10
sectionOrder (CodeSection _) = 11
sectionOrder (DataSection _) = 12

validateOrder :: [Section] -> Bool
validateOrder sections = (sort (nub order) == order)
  where order = filter (/=0) (map sectionOrder sections)

-- Types
data NumType = I32 | I64 | F32 | F64
               deriving (Show, Eq, Ord)

class IsNumType a where
  fromNumType :: NumType -> a
  i32, i64, f32, f64 :: a
  i32 = fromNumType I32
  i64 = fromNumType I64
  f32 = fromNumType F32
  f64 = fromNumType F64

instance IsNumType NumType where
  fromNumType = id

data PackedType = I8 | I16
               deriving (Show, Eq, Ord)

class IsPackedType a where
  fromPackedType :: PackedType -> a
  i8, i16 :: a
  i8 = fromPackedType I8
  i16 = fromPackedType I16

instance IsPackedType PackedType where
  fromPackedType = id

data VecType = V128
               deriving (Show, Eq, Ord)

class IsVecType a where
  fromVecType :: VecType -> a
  v128 :: a
  v128 = fromVecType V128

instance IsVecType VecType where
  fromVecType = id

data HeapType a = ANY | EQ | I31 | STRUCT | ARRAY
                | NONE | FUNC | NOFUNC | EXTERN | NOEXTERN
                | HT a
                deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance IsString a => IsString (HeapType a) where
  fromString = HT . fromString

data RefType a = Ref Bool (HeapType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

class IsRefType f where
  fromRefType :: RefType a -> f a
  ref, refn :: HeapType a -> f a
  ref = fromRefType . Ref False
  refn = fromRefType . Ref True

instance IsRefType RefType where
  fromRefType = id

data ValType a = N NumType
               | V VecType
               | R (RefType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance IsNumType (ValType a) where
  fromNumType = N

instance IsVecType (ValType a) where
  fromVecType = V

instance IsRefType ValType where
  fromRefType = R

data StorageType a = U (ValType a)
                   | P PackedType
                   deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance IsNumType (StorageType a) where
  fromNumType = U . fromNumType

instance IsVecType (StorageType a) where
  fromVecType = U . fromVecType

instance IsRefType StorageType where
  fromRefType = U . fromRefType

instance IsPackedType (StorageType a) where
  fromPackedType = P

data Mut = Imm | Mut deriving (Show, Eq, Ord)

type FieldType a = (StorageType a, Mut)

data CompType a = Array (FieldType a)
                | Struct [FieldType a]
                | Func [ValType a] [ValType a]
                deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

class IsCompType f where
  type Plug f
  fromCompType :: CompType (Plug f) -> f
  array  :: FieldType (Plug f) -> f
  array = fromCompType . Array
  struct :: [FieldType (Plug f)] -> f
  struct = fromCompType . Struct
  func   :: [ValType (Plug f)] -> [ValType (Plug f)] -> f
  func x y = fromCompType (Func x y)

instance IsCompType (CompType a) where
  type Plug (CompType a) = a
  fromCompType = id

data SubType a = Sub Final [a] (CompType a)
               deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
type Final = Bool
type Limits = (Int, Maybe Int)

type RecType a = [SubType a]

instance IsCompType (SubType a) where
  type Plug (SubType a) = a
  fromCompType = Sub True []

-- Imports
data ImportDesc a
  = FuncImport a
  | TableImport (RefType a, Limits)
  | MemImport Limits
  | GlobalImport (ValType a, Mut)
  deriving (Show, Functor, Traversable, Foldable)

-- Exports
data ExportDesc
  = FuncExport FuncIdx
  | TableExport TableIdx
  | MemExport MemIdx
  | GlobalExport GlobalIdx
  deriving (Show)

-- Elements
data Elem
  = Elem0 (Expr Int) [FuncIdx]
  | Elem1 ElemKind [FuncIdx]
  | Elem2 TableIdx (Expr Int) ElemKind [FuncIdx]
  | Elem3 ElemKind [FuncIdx]
  | Elem4 (Expr Int) [Expr Int]
  | Elem5 (RefType Int) [Expr Int]
  | Elem6 TableIdx (Expr Int) (RefType Int) [Expr Int]
  | Elem7 (RefType Int) [Expr Int]
  deriving (Show)

data ElemKind
  = ElemKindRefFunc
  deriving (Show)

-- Data
data DataMode
  = Active MemIdx (Expr Int)
  | Passive
  deriving (Show)

-- Instructions
data BlockType a = BNone | BVal (ValType a) | BType a
  deriving (Show, Eq, Ord, Functor, Traversable, Foldable)

type Expr a = [Instruction a]

data Instruction a
  = I_Unreachable
  | I_Nop
  | I_Block (BlockType a) [Instruction a]
  | I_Loop (BlockType a) [Instruction a]
  | I_If (BlockType a) [Instruction a]
  | I_IfElse (BlockType a) [Instruction a] [Instruction a]
  | I_Br LabelIdx
  | I_BrIf LabelIdx
  | I_BrTable [LabelIdx] LabelIdx
  | I_Return
  | I_Call FuncIdx
  | I_CallIndirect a TableIdx
  | I_ReturnCall FuncIdx
  | I_ReturnCallIndirect a TableIdx
  | I_CallRef a
  | I_ReturnCallRef a
  | I_BrOnNull LabelIdx
  | I_BrOnNonNull LabelIdx
  | I_BrOnCast (Bool,Bool) LabelIdx (HeapType a) (HeapType a)
  | I_BrOnCastFail (Bool,Bool) LabelIdx (HeapType a) (HeapType a)
  | I_RefNull (HeapType a)
  | I_RefIsNull
  | I_RefFunc FuncIdx
  | I_RefEq
  | I_RefAsNonNull
  | I_StructNew a
  | I_StructNewDefault a
  | I_StructGet a Idx
  | I_StructGetS a Idx
  | I_StructGetU a Idx
  | I_StructSet a Idx
  | I_ArrayNew a
  | I_ArrayNewDefault a
  | I_ArrayNewFixed a Int
  | I_ArrayNewData a DataIdx
  | I_ArrayNewElem a ElemIdx
  | I_ArrayGet a
  | I_ArrayGetS a
  | I_ArrayGetU a
  | I_ArraySet a
  | I_ArrayLen
  | I_ArrayFill a
  | I_ArrayCopy a a
  | I_ArrayInitData a DataIdx
  | I_ArrayInitElem a ElemIdx
  | I_RefTest Bool (HeapType a)
  | I_RefCast Bool (HeapType a)
  | I_AnyConvertExtern
  | I_ExternConvertAny
  | I_RefI31
  | I_I31GetS
  | I_I31GetU
  | I_Drop
  | I_Select
  | I_SelectT [ValType a]
  | I_LocalGet LocalIdx
  | I_LocalSet LocalIdx
  | I_LocalTee LocalIdx
  | I_GlobalGet GlobalIdx
  | I_GlobalSet GlobalIdx
  | I_TableGet TableIdx
  | I_TableSet TableIdx
  | I_TableInit ElemIdx TableIdx
  | I_ElemDrop ElemIdx
  | I_TableCopy TableIdx TableIdx
  | I_TableGrow TableIdx
  | I_TableSize TableIdx
  | I_TableFill TableIdx
  | I_I32Load (Int, Int)
  | I_I64Load (Int, Int)
  | I_F32Load (Int, Int)
  | I_F64Load (Int, Int)
  | I_I32Load8S (Int, Int)
  | I_I32Load8U (Int, Int)
  | I_I32Load16S (Int, Int)
  | I_I32Load16U (Int, Int)
  | I_I64Load8S (Int, Int)
  | I_I64Load8U (Int, Int)
  | I_I64Load16S (Int, Int)
  | I_I64Load16U (Int, Int)
  | I_I64Load32S (Int, Int)
  | I_I64Load32U (Int, Int)
  | I_I32Store (Int, Int)
  | I_I64Store (Int, Int)
  | I_F32Store (Int, Int)
  | I_F64Store (Int, Int)
  | I_I32Store8 (Int, Int)
  | I_I32Store16 (Int, Int)
  | I_I64Store8 (Int, Int)
  | I_I64Store16 (Int, Int)
  | I_I64Store32 (Int, Int)
  | I_MemorySize
  | I_MemoryGrow
  | I_MemoryInit DataIdx
  | I_DataDrop DataIdx
  | I_MemoryCopy
  | I_MemoryFill
  | I_I32Const Integer
  | I_I64Const Integer
  | I_F32Const [Word8]
  | I_F64Const [Word8]
  | I_I32Eqz
  | I_I32Eq
  | I_I32Ne
  | I_I32LtS
  | I_I32LtU
  | I_I32GtS
  | I_I32GtU
  | I_I32LeS
  | I_I32LeU
  | I_I32GeS
  | I_I32GeU
  | I_I64Eqz
  | I_I64Eq
  | I_I64Ne
  | I_I64LtS
  | I_I64LtU
  | I_I64GtS
  | I_I64GtU
  | I_I64LeS
  | I_I64LeU
  | I_I64GeS
  | I_I64GeU
  | I_F32Eq
  | I_F32Ne
  | I_F32Lt
  | I_F32Gt
  | I_F32Le
  | I_F32Ge
  | I_F64Eq
  | I_F64Ne
  | I_F64Lt
  | I_F64Gt
  | I_F64Le
  | I_F64Ge
  | I_I32Clz
  | I_I32Ctz
  | I_I32Popcnt
  | I_I32Add
  | I_I32Sub
  | I_I32Mul
  | I_I32DivS
  | I_I32DivU
  | I_I32RemS
  | I_I32RemU
  | I_I32And
  | I_I32Or
  | I_I32Xor
  | I_I32Shl
  | I_I32ShrS
  | I_I32ShrU
  | I_I32Rotl
  | I_I32Rotr
  | I_I64Clz
  | I_I64Ctz
  | I_I64Popcnt
  | I_I64Add
  | I_I64Sub
  | I_I64Mul
  | I_I64DivS
  | I_I64DivU
  | I_I64RemS
  | I_I64RemU
  | I_I64And
  | I_I64Or
  | I_I64Xor
  | I_I64Shl
  | I_I64ShrS
  | I_I64ShrU
  | I_I64Rotl
  | I_I64Rotr
  | I_F32Abs
  | I_F32Neg
  | I_F32Ceil
  | I_F32Floor
  | I_F32Trunc
  | I_F32Nearest
  | I_F32Sqrt
  | I_F32Add
  | I_F32Sub
  | I_F32Mul
  | I_F32Div
  | I_F32Min
  | I_F32Max
  | I_F32CopySign
  | I_F64Abs
  | I_F64Neg
  | I_F64Ceil
  | I_F64Floor
  | I_F64Trunc
  | I_F64Nearest
  | I_F64Sqrt
  | I_F64Add
  | I_F64Sub
  | I_F64Mul
  | I_F64Div
  | I_F64Min
  | I_F64Max
  | I_F64CopySign
  | I_I32WrapI64
  | I_I32TruncF32S
  | I_I32TruncF32U
  | I_I32TruncF64S
  | I_I32TruncF64U
  | I_I64ExtendI32S
  | I_I64ExtendI32U
  | I_I64TruncF32S
  | I_I64TruncF32U
  | I_I64TruncF64S
  | I_I64TruncF64U
  | I_F32ConvertI32S
  | I_F32ConvertI32U
  | I_F32ConvertI64S
  | I_F32ConvertI64U
  | I_F32DemoteF64
  | I_F64ConvertI32S
  | I_F64ConvertI32U
  | I_F64ConvertI64S
  | I_F64ConvertI64U
  | I_F64PromoteF32
  | I_I32ReinterpretF32
  | I_I64ReinterpretF64
  | I_F32ReinterpretI32
  | I_F64ReinterpretI64
  | I_I32Extend8S
  | I_I32Extend16S
  | I_I64Extend8S
  | I_I64Extend16S
  | I_I64Extend32S
  | I_I32TruncSatF32S
  | I_I32TruncSatF32U
  | I_I32TruncSatF64S
  | I_I32TruncSatF64U
  | I_I64TruncSatF32S
  | I_I64TruncSatF32U
  | I_I64TruncSatF64S
  | I_I64TruncSatF64U
  | I_V128Load (Int, Int)
  | I_V128Load8x8S (Int, Int)
  | I_V128Load8x8U (Int, Int)
  | I_V128Load16x4S (Int, Int)
  | I_V128Load16x4U (Int, Int)
  | I_V128Load32x2S (Int, Int)
  | I_V128Load32x2U (Int, Int)
  | I_V128Load8Splat (Int, Int)
  | I_V128Load16Splat (Int, Int)
  | I_V128Load32Splat (Int, Int)
  | I_V128Load64Splat (Int, Int)
  | I_V128Load32Zero (Int, Int)
  | I_V128Load64Zero (Int, Int)
  | I_V128Store (Int, Int)
  | I_V128Load8Lane (Int, Int) Idx
  | I_V128Load16Lane (Int, Int) Idx
  | I_V128Load32Lane (Int, Int) Idx
  | I_V128Load64Lane (Int, Int) Idx
  | I_V128Store8Lane (Int, Int) Idx
  | I_V128Store16Lane (Int, Int) Idx
  | I_V128Store32Lane (Int, Int) Idx
  | I_V128Store64Lane (Int, Int) Idx
  | I_V128Const [Word8]
  | I_I8x16Shuffle [Idx]
  | I_I8x16ExtractLaneS Idx
  | I_I8x16ExtractLaneU Idx
  | I_I8x16ReplaceLane Idx
  | I_I16x8ExtractLaneS Idx
  | I_I16x8ExtractLaneU Idx
  | I_I16x8ReplaceLane Idx
  | I_I32x4ExtractLane Idx
  | I_I32x4ReplaceLane Idx
  | I_I64x2ExtractLane Idx
  | I_I64x2ReplaceLane Idx
  | I_F32x4ExtractLane Idx
  | I_F32x4ReplaceLane Idx
  | I_F64x2ExtractLane Idx
  | I_F64x2ReplaceLane Idx
  | I_I8x16Swizzle
  | I_I8x16Splat
  | I_I16x8Splat
  | I_I32x4Splat
  | I_I64x2Splat
  | I_F32x4Splat
  | I_F64x2Splat
  | I_I8x16Eq
  | I_I8x16Ne
  | I_I8x16LtS
  | I_I8x16LtU
  | I_I8x16GtS
  | I_I8x16GtU
  | I_I8x16LeS
  | I_I8x16LeU
  | I_I8x16GeS
  | I_I8x16GeU
  | I_I16x8Eq
  | I_I16x8Ne
  | I_I16x8LtS
  | I_I16x8LtU
  | I_I16x8GtS
  | I_I16x8GtU
  | I_I16x8LeS
  | I_I16x8LeU
  | I_I16x8GeS
  | I_I16x8GeU
  | I_I32x4Eq
  | I_I32x4Ne
  | I_I32x4LtS
  | I_I32x4LtU
  | I_I32x4GtS
  | I_I32x4GtU
  | I_I32x4LeS
  | I_I32x4LeU
  | I_I32x4GeS
  | I_I32x4GeU
  | I_I64x2Eq
  | I_I64x2Ne
  | I_I64x2LtS
  | I_I64x2GtS
  | I_I64x2LeS
  | I_I64x2GeS
  | I_F32x4Eq
  | I_F32x4Ne
  | I_F32x4Lt
  | I_F32x4Gt
  | I_F32x4Le
  | I_F32x4Ge
  | I_F64x2Eq
  | I_F64x2Ne
  | I_F64x2Lt
  | I_F64x2Gt
  | I_F64x2Le
  | I_F64x2Ge
  | I_V128Not
  | I_V128And
  | I_V128AndNot
  | I_V128Or
  | I_V128Xor
  | I_V128Bitselect
  | I_V128AnyTrue
  | I_I8x16Abs
  | I_I8x16Neg
  | I_I8x16Popcnt
  | I_I8x16AllTrue
  | I_I8x16Bitmask
  | I_I8x16NarrowI16x8S
  | I_I8x16NarrowI16x8U
  | I_I8x16Shl
  | I_I8x16ShrS
  | I_I8x16ShrU
  | I_I8x16Add
  | I_I8x16AddSatS
  | I_I8x16AddSatU
  | I_I8x16Sub
  | I_I8x16SubSatS
  | I_I8x16SubSatU
  | I_I8x16MinS
  | I_I8x16MinU
  | I_I8x16MaxS
  | I_I8x16MaxU
  | I_I8x16AvgrU
  | I_I16x8ExtaddPairwiseI8x16S
  | I_I16x8ExtaddPairwiseI8x16U
  | I_I16x8Abs
  | I_I16x8Neg
  | I_I16x8Q15mulrSatS
  | I_I16x8AllTrue
  | I_I16x8Bitmask
  | I_I16x8NarrowI32x4S
  | I_I16x8NarrowI32x4U
  | I_I16x8ExtendLowI8x16S
  | I_I16x8ExtendHighI8x16S
  | I_I16x8ExtendLowI8x16U
  | I_I16x8ExtendHighI8x16U
  | I_I16x8Shl
  | I_I16x8ShrS
  | I_I16x8ShrU
  | I_I16x8Add
  | I_I16x8AddSatS
  | I_I16x8AddSatU
  | I_I16x8Sub
  | I_I16x8SubSatS
  | I_I16x8SubSatU
  | I_I16x8Mul
  | I_I16x8MinS
  | I_I16x8MinU
  | I_I16x8MaxS
  | I_I16x8MaxU
  | I_I16x8AvgrU
  | I_I16x8ExtmulLowI8x16S
  | I_I16x8ExtmulHighI8x16S
  | I_I16x8ExtmulLowI8x16U
  | I_I16x8ExtmulHighI8x16U
  | I_I32x4ExtaddPairwiseI16x8S
  | I_I32x4ExtaddPairwiseI16x8U
  | I_I32x4Abs
  | I_I32x4Neg
  | I_I32x4AllTrue
  | I_I32x4Bitmask
  | I_I32x4ExtendLowI16x8S
  | I_I32x4ExtendHighI16x8S
  | I_I32x4ExtendLowI16x8U
  | I_I32x4ExtendHighI16x8U
  | I_I32x4Shl
  | I_I32x4ShrS
  | I_I32x4ShrU
  | I_I32x4Add
  | I_I32x4Sub
  | I_I32x4Mul
  | I_I32x4MinS
  | I_I32x4MinU
  | I_I32x4MaxS
  | I_I32x4MaxU
  | I_I32x4DotI16x8S
  | I_I32x4ExtmulLowI16x8S
  | I_I32x4ExtmulHighI16x8S
  | I_I32x4ExtmulLowI16x8U
  | I_I32x4ExtmulHighI16x8U
  | I_I64x2Abs
  | I_I64x2Neg
  | I_I64x2AllTrue
  | I_I64x2Bitmask
  | I_I64x2ExtendLowI32x4S
  | I_I64x2ExtendHighI32x4S
  | I_I64x2ExtendLowI32x4U
  | I_I64x2ExtendHighI32x4U
  | I_I64x2Shl
  | I_I64x2ShrS
  | I_I64x2ShrU
  | I_I64x2Add
  | I_I64x2Sub
  | I_I64x2Mul
  | I_I64x2ExtmulLowI32x4S
  | I_I64x2ExtmulHighI32x4S
  | I_I64x2ExtmulLowI32x4U
  | I_I64x2ExtmulHighI32x4U
  | I_F32x4Ceil
  | I_F32x4Floor
  | I_F32x4Trunc
  | I_F32x4Nearest
  | I_F32x4Abs
  | I_F32x4Neg
  | I_F32x4Sqrt
  | I_F32x4Add
  | I_F32x4Sub
  | I_F32x4Mul
  | I_F32x4Div
  | I_F32x4Min
  | I_F32x4Max
  | I_F32x4Pmin
  | I_F32x4Pmax
  | I_F64x2Ceil
  | I_F64x2Floor
  | I_F64x2Trunc
  | I_F64x2Nearest
  | I_F64x2Abs
  | I_F64x2Neg
  | I_F64x2Sqrt
  | I_F64x2Add
  | I_F64x2Sub
  | I_F64x2Mul
  | I_F64x2Div
  | I_F64x2Min
  | I_F64x2Max
  | I_F64x2Pmin
  | I_F64x2Pmax
  | I_I32x4TruncSatF32x4S
  | I_I32x4TruncSatF32x4U
  | I_F32x4ConvertI32x4S
  | I_F32x4ConvertI32x4U
  | I_I32x4TruncSatF64x2SZero
  | I_I32x4TruncSatF64x2UZero
  | I_F64x2ConvertLowI32x4S
  | I_F64x2ConvertLowI32x4U
  | I_F32x4DemoteF64x2Zero
  | I_F64x2PromoteLowF32x4
  deriving (Show, Eq, Ord, Functor, Traversable, Foldable)
