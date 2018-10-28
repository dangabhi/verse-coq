Require Import Verse.
Require Import Verse.Arch.C.
Require Import Verse.Types.Internal.
(*
Require Import NSemantics.
Import NSemantics.
 *)

Import NArith.
Require Import Vector.
Import VectorNotations.

Set Implicit Arguments.

Section TestFunction.

  Variable variable : VariableT.

  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable arr     : variable (Array 5 bigE Word16).
  Variable A B     : variable Byte.

  Definition parameters := [Var arr; Var A; Var B].

  (* The local variables *)
  Variable num      : variable Word16.

  Definition locals := [Var num].

  (* The temp register *)
  Variable tmp       : variable Word16.

  Definition registers := [Var tmp].
  Definition regAssignment := (- cr uint16_t "temp" -).
  Definition someInstruction i (_ : i < 5) : Code variable.
    Import Nat.
    verse [ arr[- i -] ::=^ arr[- (i + 1) mod 5 -] ]%list.
  Defined.

  Definition testFunction : code variable.
    verse
      [ num ::= tmp [+] Ox "abcd";
        
        ASSERT num HAS n ; tmp HAS t IN n = XorW (RotR 2 t) n;
        
        ASSERT A HAS a; num HAS n ; tmp HAS t IN (n = t) /\ (t = n);

        A   ::= A [+] B;
        num ::= tmp [-] num ;
                
        ASSERT num HAS n ; tmp HAS t IN n = t;
        ASSERT num HAS n IN (n = n);

        ASSERT A HAS a IN (2 = 3) /\ (Val num = Val num)%N;

        num      ::= tmp      [*] arr[-1-];

        ASSERT num HAS n ; tmp HAS t ; A HAS a IN (and (n = t) (n = n))%N;

        num      ::= arr[-1-] [/] tmp ;

        (* binary update *)
        num ::=+ tmp;
        num ::=- arr[-1-];
        num ::=* Ox "1234";
        num ::=/ tmp;

        ASSERT num HAS n ; tmp HAS t ; num HAS n' IN
                                           (and (n' = t) (n' = n))%N;
        
        CLOBBER arr
      ]%list.
  Defined.

End TestFunction.

Import StandardSemantics.

Definition toProve : Prop.

  extractSAT testFunction.
  
Defined.

(* A potential proof template *)

Definition proof : toProve.
  (*
  unfold toProve.
  unfold genSAT.
  unfold SAT.
  simpl.
   *)
  Hint Unfold allocation S.store SAT genSAT.
Abort.

Import Compile.

Set Printing Implicit.
Definition testcode : Doc + {Compile.CompileError}.
  Compile.function "testFunction" parameters locals registers.
  assignRegisters regAssignment.
  statements testFunction.
Defined.

Compute (tryLayout testcode).


(*

Require Import Verse.Extraction.Ocaml.

Definition main : unit := print_code testcode.

Recursive Extraction main.

 *)
