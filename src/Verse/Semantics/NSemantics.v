Require Import Verse.Word.
Require Import WordFacts.
Require Import Verse.NFacts.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.Operators.
Require Import Verse.Error.
Require Import Verse.Semantics.

Require Import Arith.
Require Import NArith.

Module NWord <: WORD_SEMANTICS.

  Definition wordDenote (n : nat) : Type :=
    N.

End NWord.

Module NConst <: CONST_SEMANTICS NWord.

  Definition constWordDenote n (w : constant (word n)) : NWord.wordDenote n :=
    Nibble.toN w.

End NConst.

Module NOps <: OP_SEMANTICS (NWord).

  Definition OpError := True.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote la ra (NWord.wordDenote n) :=
    let split2 n0 := (n0 / 2 ^ N.of_nat n, n0 mod (2 ^ N.of_nat n))%N in
    let merge2 n0 n1 := (2 ^ N.of_nat n * n0 + n1)%N in
    match o in op la0 ra0 return arityDenote la0 ra0 (NWord.wordDenote n) with
    | plus => fun a b => N.add a b
    | minus => fun a b => N.sub a b
    | mul => fun a b => N.mul a b
    | exmul => fun a b => split2 (a * b)%N
    | quot => fun a b => N.div a b
    | eucl => fun a b c => N.div_eucl (merge2 a b) c
    | rem => fun a b => N.modulo a b
    | bitOr => fun a b => N.lor a b
    | bitAnd => fun a b => N.land a b
    | bitXor => fun a b => N.lxor a b
    | bitComp => fun a => Bv2N (Bvector.Bneg n (N2Bv_gen n a) )
    | rotL m => fun b => Bv2N (BOps.BRotL m (N2Bv_gen n b))
    | rotR m => fun b => Bv2N (BOps.BRotR m (N2Bv_gen n b))
    | shiftL m => fun b => (N.shiftl_nat b m mod two_power_nat_N (8 * 2 ^ n))%N
    | shiftR m => fun b => N.shiftr_nat b m
    | nop => fun b => b
    end.

End NOps.

Module NSemantics := Semantics NWord NConst NOps.
(* Module NSemanticsTactics := SemanticTactics NWord NConst NOps. *)

Module NSemanticTactics.

  Definition my_mod_small x p := N.mod_small x (two_power_nat_N (4 * (2 * p))).

  Ltac mask_mod :=
    match goal with
    | [ |- context [ @Bv2N ?vs (@fromNibbles ?ns ?x)] ] =>
      try (let ones := fresh "ones" in
           assert (ones : (@Bv2N vs (@fromNibbles ns x) = 2 ^ (N.log2 (@Bv2N vs (@fromNibbles ns x)) + 1) - 1)%N) by (now compute);
           simpl N.log2 in ones;
           simpl N.add in ones;
           rewrite ?ones;
           rewrite ?andOnes_mod)
    end.

  Ltac simplify_arith :=
    unfold numBinOp; (* expose operator internals *)

    rewrite ?shiftRW_div; (* rewrite shiftR's as div's *)
    simpl N.of_nat;

    rewrite ?Bv2N_N2Bv_gen_mod; (* nested use is a modulus *)

    rewrite ?andW_equiv; (* all 'and's should be lower masks *)
    rewrite ?Nand_BVand;
    mask_mod; (* rewrite masks as mod *)

    repeat match goal with
           | [ |- context [ @Bv2N ?ns ?bv] ] => let bvn := fresh bv in
                                                set (bvn := @Bv2N ns bv) in *
           end;
    (* try to solve assuming no overflows *)
    (repeat rewrite_strat innermost (my_mod_small));
    simpl N.of_nat.

End NSemanticTactics.
