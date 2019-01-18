Require Import Verse.
Require Import Verse.Arch.C.
Require Import Verse.Types.Internal.
Require Import Semantics.
Require Import NFacts.

Require Import Vector.
Import VectorNotations.

Import StandardSemantics.
Open Scope semantic_scope.
Open Scope word_scope.

Import NArith.

Set Implicit Arguments.

Section TestFunction.

  Variable variable : VariableT.

  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable A B C D     : variable Word16.

  Definition parameters := [Var A; Var B; Var C; Var D].

  Definition locals : list (some type) := []%list.

  (* The temp register *)
  Variable tmp       : variable Word16.

  Definition registers := [Var tmp].

  Definition regAssignment := (- cr uint16_t "temp" -).

  Definition Select8 : constant Word16 := Ox "00 FF".

  Definition testFunction : code variable.
    (* Simulating ex-mul :

       Final C := Higher 16 bits of (Init A * Init B)
    *)
    verse
      [ tmp ::= Ox "00 FF";
        C ::= A & tmp;
        D ::= B & Select8;
        A ::=>> 8;    (* Initial A has now been split into (A : C) *)
        B ::=>> 8;    (* Initial B has now been split into (B : C) *)
        C ::=* B;
        C ::=>>8;
        D ::=* A;
        D ::=>> 8;
        C ::=+ D;
        D ::= A * B;
        C ::=+ D;     (* If A was (A1 : A2) and B was (B1 : B2),
                         C = A1 * B1 + A2 * B1 / 2 ^ 8 + A1 * B2 / 2 ^ 8 *)
        ASSERT Bv2N (Val C) = ((Bv2N (Old A) * Bv2N (Old B)) / (2 ^ 16))%N
      ]%list.
  Defined.

End TestFunction.

Import StandardTactics.

Definition toProve : Prop.
  extractSAT testFunction.
Defined.

(* A potential proof template *)

Require Import Verse.Semantics.NSemantics.
Import NSemanticTactics.

Definition proof : toProve.
  time (
  unfold toProve;
  unfold genSAT;
  unfold SAT;
  breakStore;
  lazy -[RotRW RotLW ShiftRW ShiftLW XorW AndW OrW NegW
              fromNibbles
              numBinOp numBigargExop numOverflowBinop Bv2N
              Nat.add Nat.sub Nat.mul Nat.div Nat.pow
              N.add N.sub N.mul N.div N.div_eucl N.modulo N.gt N.pow
              Ox nth replace]).
  intuition.
  simplify_arith.
Abort.

Import Compile.

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
