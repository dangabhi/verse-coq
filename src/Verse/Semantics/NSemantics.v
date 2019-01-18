Require Import Verse.Word.
Require Import WordFacts.
Require Import Verse.NFacts.

Require Import Arith.
Require Import NArith.

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
