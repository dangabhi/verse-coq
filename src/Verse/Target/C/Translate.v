Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Error.
Require Import Verse.Nibble.

Module Internal.

  Definition tgt  := resultSystem c_type_system.

  Definition trType (ty : Types.type direct) : typeOf tgt direct
    := let couldNotError := error (CouldNotTranslate ty)
       in match ty with
          | Types.word 0 => {- uint8_t  -}
          | Types.word 1 => {- uint16_t -}
          | Types.word 2 => {- uint32_t -}
          | Types.word 3 => {- uint64_t -}
          | _ => couldNotError
          end.

  Definition trConst (ty : Types.type direct)
    : Types.const ty -> constOf tgt (trType ty)
    := match ty with
       | word n =>
         match n as n0
               return Types.const (word n0)
                      -> constOf tgt (trType (word n0))
         with
         | 0 | 1 | 2 | 3  => @toNibbleTuple _
         | _ => fun x : _ => error (CouldNotTranslate x)
         end
       | multiword _ _  => fun x => error (CouldNotTranslate x)
       end.

End Internal.

Canonical Structure c_type_compile : typeCompile c_type_system
  := TypeTranslation Internal.trType Internal.trConst.
