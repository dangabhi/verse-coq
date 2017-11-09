Require Import Verse.Word.
Require Import Verse.ZFacts.

Require Import Coq.setoid_ring.Ring_theory.
Require Import BinNums.
Require Import ZArith.
Require Import Coq.ZArith.Zdigits.
Require Import ZArith_base.
Require Import BinInt.


Section ModRing.

  Variable n : nat.

  Definition wO   := bits (Z_to_binary n 0).
  Definition wI   := bits (Z_to_binary n 1).
  Definition wadd := @numBinOp n Z.add.
  Definition wmul := @numBinOp n Z.mul.
  Definition wsub := @numBinOp n Z.sub.
  Definition wopp := @numUnaryOp n Z.opp.
  Definition weq  := @eq (Word.t n).

  Infix "==" := weq (at level 70).

  Ltac crush_mod_ring :=
    repeat (intros []); unfold wadd, wmul, wsub, wopp, weq, wO, wI, numBinOp, numUnaryOp;
    apply f_equal;
    apply binary_value_inj; rewrite ?Z_to_binary_to_Z_mod;
    simpl;
    try (rewrite ?Z.add_mod_idemp_l);
    try rewrite ?Z.add_mod_idemp_r;
    try rewrite ?Z.mul_mod_idemp_l;
    try rewrite ?Z.mul_mod_idemp_r;
    try rewrite Z.mul_1_l;
    try rewrite Z.mul_add_distr_l;
    try rewrite Z.mul_add_distr_r;
    try rewrite Z.add_opp_diag_r;
    try rewrite Z.add_opp_diag_l;
    trivial;
    try rewrite Z.add_assoc +
    rewrite Z.mul_assoc +
    rewrite Z.add_comm  +
    rewrite Z.mul_comm  +
    rewrite Z.mod_small;
    trivial;
    try (discriminate +
         (constructor;
          [> apply Z.ge_le_iff; apply binary_value_pos | apply binary_value_small]
         )
        ).

  
    
  Lemma wadd_0_l : forall x, wadd wO x == x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wadd_comm : forall x y, wadd x y == wadd y x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wadd_assoc : forall x y z, wadd x (wadd y z) == wadd (wadd x y) z.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_1_l : forall x, wmul wI x == x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_comm : forall x y, wmul x y == wmul y x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_assoc : forall x y z, wmul x (wmul y z) == wmul (wmul x y) z.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wdistr_l : forall x y z, wmul (wadd x y) z == wadd (wmul x z) (wmul y z).
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wsub_def : forall x y, wsub x y == wadd x (wopp y).
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wopp_def : forall x, wadd x (wopp x) == wO.
  Proof.
    crush_mod_ring.
  Qed.

  Definition mod_ring : ring_theory wO wI wadd wmul wsub wopp weq :=
    {|
      Radd_0_l := wadd_0_l;
      Radd_comm := wadd_comm;
      Radd_assoc := wadd_assoc;
      Rmul_1_l := wmul_1_l;
      Rmul_comm := wmul_comm;
      Rmul_assoc := wmul_assoc;
      Rdistr_l := wdistr_l;
      Rsub_def := wsub_def;
      Ropp_def := wopp_def
    |}.

  Add Ring Word : mod_ring.

End ModRing.