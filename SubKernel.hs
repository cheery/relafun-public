{-# LANGUAGE OverloadedStrings #-}
module SubKernel where

import Wasm.Core
import qualified Wasm.CoreWriter as W
import qualified Wasm.CommonWriting as CW
import Sub

types :: [TypeDecl]
types = [
  "values" ==> array (refn ANY, Mut),
  "thunk-func" ==> func [ref "thunk"]
                        [refn ANY],
  "thunk" ==> struct [
           (ref "thunk-func", Mut),
           (refn ANY, Mut) ],
  "closure-func" ==> func [ref "values",
                           ref "values"]
                          [refn ANY],
  "closure" ==> struct [
            (i32, Imm),
            (ref "values", Imm),
            (ref "closure-func", Imm) ],
  "pap" ==> struct [
            (ref "closure", Imm),
            (ref "values", Imm) ] ]

{--
The current compiler makes it harder to
define values like this.

contents :: [SuperDeclaration Inp]
contents = [
  ElemDeclareFunc 0, -- thunk-blackhole
  Export "blackhole" (FuncExport 0),
  DefFunc "thunk-func" [] [Terminal (I_Unreachable % [])],
  Export "eval" (FuncExport 1),
  DefFunc (func [refn ANY] [refn ANY])
          [ref "thunk"]
          [CastCase (I_LocalGet 0 % [])
                    (refn ANY)
                    [(ref "thunk", [Do (I_LocalSet 1 % []),
                                    Terminal (I_ReturnCallRef "thunk-func" % [ I_LocalGet 1 % [],
                                                                               I_StructGet "thunk" 0 % [ I_LocalGet 1 % [] ] ])])]
                    (Just [Terminal (I_Return % [])])],
  Export "apply" (FuncExport 2),
  DefFunc (func [refn ANY, ref "values"] [refn ANY])
          [ref "closure", ref "pap", ref "values"]
          [CastCase (I_LocalGet 0 % [])
                    (refn ANY)
                    [(ref "closure", [
                       Do (I_LocalSet 2 % []),
                       If (I_I32LtU % [I_ArrayLen % [I_LocalGet 1 % []],
                                       I_StructGet "closure" 0 % [I_LocalGet 2 % []]])
                          [Terminal $ I_Return % [I_StructNew "pap" % [I_LocalGet 2 % [],
                                                                       I_LocalGet 1 % []]]]
                          [If (I_I32Eq % [I_ArrayLen % [I_LocalGet 1 % []],
                                          I_StructGet "closure" 0 % [I_LocalGet 2 % []]])
                              [Terminal $ I_ReturnCallRef "closure-func" % [
                                            I_StructGet "closure" 1 % [I_LocalGet 2 % []],
                                            I_LocalGet 1 % [],
                                            I_StructGet "closure" 2 % [I_LocalGet 2 % []]]]
                              [Do (I_CallRef "closure-func" % [
                                            I_StructGet "closure" 1 % [I_LocalGet 2 % []],
                                            I_LocalGet 1 % [],
                                            I_StructGet "closure" 2 % [I_LocalGet 2 % []]]),
                               Do (I_LocalSet 4 % [
                                     I_ArrayNew "values" % [I_RefNull ANY % [],
                                                            I_I32Sub % [
                                                              I_ArrayLen % [I_LocalGet 1 % []],
                                                              I_StructGet "closure" 0 % [I_LocalGet 2 % []]]]]),
                               Do (I_ArrayCopy "values" "values" % [
                                     I_LocalGet 4 % [], I_I32Const 0 % [],
                                     I_LocalGet 1 % [], I_StructGet "closure" 0 % [I_LocalGet 2 % []],
                                     I_ArrayLen % [I_LocalGet 4 % []]]),
                               Terminal $ I_ReturnCall 2 % [
                                  -- f in stack
                                  I_LocalGet 4 % []]]]]),
                     (ref "pap", [
                       Do (I_LocalSet 3 % []),
                       Do (I_LocalSet 4 % [
                             I_ArrayNew "values" % [I_RefNull ANY % [],
                                                    I_I32Add % [
                                                      I_ArrayLen % [I_StructGet "pap" 1 % [I_LocalGet 3 % []]],
                                                      I_ArrayLen % [I_LocalGet 1 % []]]]]),
                       Do (I_ArrayCopy "values" "values" % [
                             I_LocalGet 4 % [], I_I32Const 0 % [],
                             I_StructGet "pap" 1 % [I_LocalGet 3 % []], I_I32Const 0 % [],
                             I_ArrayLen % [I_StructGet "pap" 1 % [I_LocalGet 3 % []]]]),
                       Do (I_ArrayCopy "values" "values" % [
                             I_LocalGet 4 % [],
                             I_ArrayLen % [I_StructGet "pap" 1 % [I_LocalGet 3 % []]],
                             I_LocalGet 1 % [], I_I32Const 0 % [],
                             I_ArrayLen % [I_LocalGet 1 % []]]),
                       Terminal $ I_ReturnCall 2 % [
                                    I_StructGet "pap" 0 % [I_LocalGet 3 % []],
                                    I_LocalGet 4 % []]])]
                    Nothing],
  Export "begin-thunk" (FuncExport 3),
  DefFunc (func [ref "thunk"] [ref "values"]) []
          [Do $ I_StructSet "thunk" 0 % [I_LocalGet 0 % [], I_RefFunc 0 % []],
           Terminal $ I_Return % [I_RefCast False "values" % [I_StructGet "thunk" 1 % [I_LocalGet 0 % []]]]],
  ElemDeclareFunc 4, -- thunk-resolved
  DefFunc "thunk-func" [] [Terminal $ I_Return % [
                             I_StructGet "thunk" 1 % [I_LocalGet 0 % []]]],
  Export "resolve" (FuncExport 5),
  DefFunc (func [refn ANY, ref "thunk"] [refn ANY]) []
          [Do $ I_StructSet "thunk" 1 % [I_LocalGet 1 % [], I_LocalGet 0 % []],
           Do $ I_StructSet "thunk" 0 % [I_LocalGet 1 % [], I_RefFunc 4 % []],
           Terminal $ I_Return % [I_LocalGet 0 % []]]
  ] 

compile = CW.writeFile "subkernel.wasm" (compileDecls types contents)
--}

--   (func $begin-thunk (export "begin-thunk") (param (ref $thunk)) (result (ref $values))
--       local.get 0
--       ref.func $thunk-blackhole
--       struct.set $thunk $code
--       local.get 0
--       struct.get $thunk $to
--       ref.cast (ref $values))
--  
--   (func $resolve (export "resolve") (param anyref)
--                  (param (ref $thunk))
--                  (result anyref)
--       local.get 1
--       local.get 0
--       struct.set $thunk $to
--       local.get 1
--       ref.func $thunk-resolved
--       struct.set $thunk $code
--       local.get 0))
