(module
  (type $values (array (mut anyref)))
  (rec
    (type $thunk-func (func
      (param (ref $thunk))
      (result anyref)))
    (type $thunk (struct
      (field $code (mut (ref $thunk-func)))
      (field $to (mut anyref)))))
  (type $closure-func (func (param (ref $values))
                            (param (ref $values))
                            (result anyref)))
  (type $closure (struct (field $arity i32)
                         (field $context (ref $values))
                         (field $code (ref $closure-func))))
  (type $pap (struct (field $closure (ref $closure))
                     (field $args    (ref $values))))

  (elem declare func $thunk-blackhole)
  (export "blackhole" (func $thunk-blackhole))
  (func $thunk-blackhole (type $thunk-func)
      unreachable)
  (elem declare func $thunk-resolved)
  (func $thunk-resolved (type $thunk-func)
      local.get 0
      struct.get $thunk $to)

  (func $eval (export "eval") (param $o anyref) (result anyref)
      (local $t (ref $thunk))
      (block $is-thunk (result (ref $thunk))
        local.get $o
        br_on_cast $is-thunk anyref (ref $thunk)
        return) ;; is-thunk
      local.set $t
      ;; Get the thunk code and run it.
      local.get $t
      local.get $t
      struct.get $thunk $code
      call_ref $thunk-func
      ;; result in stack, lets try eval it again.
      return_call $eval)
      
  (func $apply (export "apply") (param $o anyref) (param (ref $values)) (result anyref)
      (local $t (ref $thunk))
      (local $f (ref $closure))
      (local $p (ref $pap))
      (local $next (ref $values))
      (local $i i32)
      (local $j i32)
      (block $is-pap (result (ref $pap))
        (block $is-fun (result (ref $closure))
            local.get $o
            br_on_cast $is-fun anyref (ref $closure)
            br_on_cast $is-pap anyref (ref $pap)
            unreachable) ;; is-fun
        local.set $f
        ;; lt comparison
        local.get 1
        array.len
        local.get $f
        struct.get $closure $arity
        i32.lt_u
        (if ;; not enough args
          (then
            local.get $f
            local.get 1
            struct.new $pap
            return)
          (else
            local.get $f
            struct.get $closure $context
            local.get 1
            local.get $f
            struct.get $closure $code
            ;; eq comparison
            local.get 1
            array.len
            local.get $f
            struct.get $closure $arity
            i32.eq
            (if (param (ref $values))
                (param (ref $values))
                (param (ref $closure-func))
              (then return_call_ref $closure-func)
              (else ;; excess arguments.
                    call_ref $closure-func
                    local.set $o
                    ;; setup new array
                    ref.null any ;; use null as dummy value.
                    local.get 1
                    array.len
                    local.get $f
                    struct.get $closure $arity
                    i32.sub
                    array.new $values
                    local.set $next
                    ;; lets slice it from the end.
                    local.get $next ;; to array
                    i32.const 0 ;; to-base
                    local.get 1 ;; from array
                    local.get $f
                    struct.get $closure $arity ;; base
                    local.get $next
                    array.len ;; count
                    array.copy $values $values
                    ;; call apply again
                    local.get $o
                    call $eval
                    local.get $next
                    return_call $apply))))
        unreachable) ;; is-pap
      local.set $p
      ;; initialize blank array
      ref.null any
      ;; get pap args length
      local.get $p
      struct.get $pap $args
      array.len
      ;; get arglist length
      local.get 1
      array.len
      i32.add
      array.new $values
      local.set $next
      ;; copy the first part
      local.get $next       ;; to
      i32.const 0           ;; to-base
      local.get $p
      struct.get $pap $args ;; from
      i32.const 0           ;; from-base
      local.get $p
      struct.get $pap $args
      array.len             ;; count
      array.copy $values $values
      ;; copy the next part
      local.get $next       ;; to
      local.get $p
      struct.get $pap $args
      array.len             ;; to-base
      local.get 1           ;; from
      i32.const 0           ;; from-base
      local.get 1
      array.len             ;; count
      array.copy $values $values
      ;; call closure with concatenated arguments
      local.get $p
      struct.get $pap $closure
      local.get $next
      return_call $apply)
  (func $begin-thunk (export "begin-thunk") (param (ref $thunk)) (result (ref $values))
      local.get 0
      ref.func $thunk-blackhole
      struct.set $thunk $code
      local.get 0
      struct.get $thunk $to
      ref.cast (ref $values))
 
  (func $resolve (export "resolve") (param anyref)
                 (param (ref $thunk))
                 (result anyref)
      local.get 1
      local.get 0
      struct.set $thunk $to
      local.get 1
      ref.func $thunk-resolved
      struct.set $thunk $code
      local.get 0))
