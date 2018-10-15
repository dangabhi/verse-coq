Require Vector.
Require Import Arith.
Import Nat.
Require Import Verse.Error.
Require Import Verse.Types.Internal.
Require Import Verse.PrettyPrint.

(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)

(** * Types in verse.

There are two kinds of types supported by verse [direct] and
[memory]. A value of a direct type can potentially be stored in one of
the machine registers. The supported direct types include the word
types [Word8], [Word16] , [Word32] and [Word64] and the vector types
[Vector128 w] and [Vector256 w] where [w] is any of the above word
types.  Verse supports arrays of these direct types but arrays are
memory types.


A user is only expected to use the types exposed from this
module. There is more to types and all its gory details are exposed
from the module [Verse.Types.Internal].

*)


(** Standard word types/scalars *)
Notation Byte   := (word 0).
Notation Word8  := (word 0).
Notation Word16 := (word 1).
Notation Word32 := (word 2).
Notation Word64 := (word 3).

(* Array constructor sticking with the convention  with no alignment restriction *)
Definition Array  := array.

(* begin hide *)
Inductive BadVectorType : Prop := BadVectorTypeError.
Definition vector {k} m (t : type k) : type direct + {BadVectorType} :=
  match t with
  | word n => match compare n m with
              | LT => {- multiword (m - n) n -}
             (* | _  => error BadVectorTypeError *)
              end
  | _ => error BadVectorTypeError
  end.
(* end hide *)

Definition Vector128 (t : type direct) := recover (vector 4 t).
Definition Vector256 (t : type direct) := recover (vector 4 t).

Definition constant (ty : type direct) :=
  let _ := mkTypeDenote StandardWord.wordDenote
  in typeDenote ty.

Module Type CONST_SEMANTICS (W : WORD_SEMANTICS).
  Parameter constWordDenote : forall n, StandardWord.wordDenote n -> W.wordDenote n.
End CONST_SEMANTICS.

Module StandardConsts <: CONST_SEMANTICS StandardWord.
  Definition constWordDenote n := @id (StandardWord.wordDenote n).
End StandardConsts.

(* To lift the interpretation of constant words to other types *)
Module ConstDenote (W : WORD_SEMANTICS) (C : CONST_SEMANTICS W).

  Definition TypeDenote := mkTypeDenote W.wordDenote.

  Fixpoint constDenote {ty : type direct} :=
    match ty in type direct return constant ty -> @typeDenote _ TypeDenote _ ty with
    | word n        => @C.constWordDenote n
    | multiword m n => Vector.map (@C.constWordDenote n)
    end.

End ConstDenote.

(* begin hide *)

Definition constant_doc (ty : type direct)  : constant ty -> Doc.
  refine( match ty with
          | word _         => fun w => text "0x" <> doc w
          | multiword _ _  => fun w => doc w
          end
        ); repeat simpl;  try apply vector_pretty_print.
Defined.

Global Instance constant_pretty (ty : type direct) : PrettyPrint (constant ty)
  := { doc := constant_doc ty }.
(* end hide *)
