module Wasm.Component where

import qualified Wasm.Core as Core
import Data.Word (Word8)

magic, version, layer :: [Word8]
magic   = [0x00, 0x61, 0x73, 0x6D]
version = [0x0d, 0x00]
layer   = [0x01, 0x00]

type Component = [Section]

data Section
  = CustomSection String [Word8]
  | ModuleSection Core.Core
  | InstanceSection
  | TypeSection

sectionId :: Num n => Section -> n
