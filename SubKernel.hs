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


contents :: [Declaration Inp]
contents = [
  ElemDeclareFunc 0, -- thunk-blackhole
  DefFunc "thunk-func" [] [Terminal (I_Unreachable % [])],
  --Export "eval" (FuncExport 1),
  DefFunc (func [refn ANY] [refn ANY])
          [ref "thunk"]
          [CastCase (I_LocalGet 0 % [])
                    (refn ANY)
                    [(ref "thunk", [Do (I_LocalSet 1 % []),
                                    Terminal (I_ReturnCallRef "thunk-func" % [ I_LocalGet 1 % [],
                                                                               I_StructGet "thunk" 0 % [ I_LocalGet 1 % [] ] ])])]
                    (Just [Terminal (I_Return % [])])]
  ]

compile = CW.writeFile "subkernel.wasm" (compileDecls types contents)
--   DefFunc (func [refn ANY] [refn ANY])
--           [ref "thunk"]
--           [CastCase (LocalGet 0)
--             [(ref "thunk", LocalSet 1,
--               [Return (Just (Call
--                 (StructGet 0 (LocalGet 1))
--                 [LocalGet 1]))])]
--             (Just (refn ANY, Drop, [Return (Just (LocalGet 0))])) ],
--   DefFunc (func [refn ANY, ref "values"] [refn ANY])
--           [ref "closure", ref "pap", ref "values", i32, i32]
--           [CastCase (LocalGet 0)
--                     [(ref "closure", LocalSet 2, [
--                        --if lt_u (len args) closure.arity
--                        --then
--                        --   return struct.new pap closure args
--                        --else
--                        --   if i32.eq (len args) closure.arity
--                        --   then
--                        --       return call closure.func args
--                        --   else
--                        --       f = call closure.func args
--                        --       next = array.new null (len args - closure.arity)
--                        --       copy next 0 args closure.arity (len next)
--                        --       return apply f next
--                        ]),
--                      (ref "pap", LocalSet 3, [
--                        -- next = array.new null (len pap.args + len args)
--                        -- copy next 0 pap.args 0 (len pap.args)
--                        -- copy next (len pap.args) args 0 (len args)
--                        -- return apply pap.closure next
--                        ])]
--                     Nothing] ]
-- --}

--   (func $apply (export "apply") (param $o anyref) (param (ref $values)) (result anyref)
--             unreachable) ;; is-fun
--         local.set $f
--         ;; lt comparison
--         local.get 1
--         array.len
--         local.get $f
--         struct.get $closure $arity
--         i32.lt_u
--         (if ;; not enough args
--           (then
--             local.get $f
--             local.get 1
--             struct.new $pap
--             return)
--           (else
--             local.get $f
--             struct.get $closure $context
--             local.get 1
--             local.get $f
--             struct.get $closure $code
--             ;; eq comparison
--             local.get 1
--             array.len
--             local.get $f
--             struct.get $closure $arity
--             i32.eq
--             (if (param (ref $values))
--                 (param (ref $values))
--                 (param (ref $closure-func))
--               (then return_call_ref $closure-func)
--               (else ;; excess arguments.
--                     call_ref $closure-func
--                     local.set $o
--                     ;; setup new array
--                     ref.null any ;; use null as dummy value.
--                     local.get 1
--                     array.len
--                     local.get $f
--                     struct.get $closure $arity
--                     i32.sub
--                     array.new $values
--                     local.set $next
--                     ;; lets slice it from the end.
--                     local.get $next ;; to array
--                     i32.const 0 ;; to-base
--                     local.get 1 ;; from array
--                     local.get $f
--                     struct.get $closure $arity ;; base
--                     local.get $next
--                     array.len ;; count
--                     array.copy $values $values
--                     ;; call apply again
--                     local.get $o
--                     call $eval
--                     local.get $next
--                     return_call $apply))))
--         unreachable) ;; is-pap
--       local.set $p
--       ;; initialize blank array
--       ref.null any
--       ;; get pap args length
--       local.get $p
--       struct.get $pap $args
--       array.len
--       ;; get arglist length
--       local.get 1
--       array.len
--       i32.add
--       array.new $values
--       local.set $next
--       ;; copy the first part
--       local.get $next       ;; to
--       i32.const 0           ;; to-base
--       local.get $p
--       struct.get $pap $args ;; from
--       i32.const 0           ;; from-base
--       local.get $p
--       struct.get $pap $args
--       array.len             ;; count
--       array.copy $values $values
--       ;; copy the next part
--       local.get $next       ;; to
--       local.get $p
--       struct.get $pap $args
--       array.len             ;; to-base
--       local.get 1           ;; from
--       i32.const 0           ;; from-base
--       local.get 1
--       array.len             ;; count
--       array.copy $values $values
--       ;; call closure with concatenated arguments
--       local.get $p
--       struct.get $pap $closure
--       local.get $next
--       return_call $apply)
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
