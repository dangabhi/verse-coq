Require Import Word.

Require Import NArith.
Require Import Vector.
Require Import CoLoR_VecUtil.

Require Import Equality.

Import BOps.

Set Implicit Arguments.


Definition Distr T f g := forall a b c : T,
    g a (f b c) = f (g a b) (g a c).

Definition Comm T (f : T -> T -> T) := forall a b, f a b = f b a.

Arguments Distr [T] f g.
Arguments Comm [T] _.

Section Basics.

  Variable f g : bool -> bool -> bool.
  Variable n : nat.

  Lemma liftDistr : Distr f g -> Distr (@Vmap2 _ _ _ f n)
                                       (@Vmap2 _ _ _ g n).
    unfold Distr.
    intros.
    induction n.
    now VOtac.
    VSntac a. VSntac b. VSntac c.
    simpl.
    f_equal.
    apply H.
    apply IHn0.
  Qed.

  Lemma liftComm : Comm f -> Comm (@Vmap2 _ _ _ f n).
    unfold Comm.
    intros.
    induction n.
    now VOtac.
    VSntac a. VSntac b.
    simpl.
    f_equal.
    apply H.
    apply IHn0.
  Qed.

End Basics.

Lemma andW_equiv n v1 v2 : AndW v1 v2 = Bvector.BVand n v1 v2.
  induction n.
  - VOtac.
    now easy.
  - VSntac v1. VSntac v2.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma shiftR1_div2 n (v : Word.t (S n)) : Bv2N (Bvector.BshiftRl _ v false) = (Bv2N v / 2)%N.
  unfold Bvector.BshiftRl.
  unfold Bvector.Bhigh.
  VSntac v.
  simpl.
  rewrite <- N.div2_div.
  case (Vhead v); [rewrite N.div2_succ_double | rewrite N.div2_double].
  all: (generalize (Vtail v);
        clear v H;
        induction t; [ easy |
                       simpl; case h; now rewrite IHt ]).
Qed.

Lemma shiftRW_div n (v1 : Word.t n) : forall m, Bv2N (ShiftRW m v1) = (Bv2N v1 / (2 ^ (N.of_nat m)))%N.
  unfold ShiftRW.
  unfold BShiftR.

  unfold Bvector.Bvector in v1.

  induction n.
  * now VOtac.
  * induction m.
    - VSntac v1.
      simpl.
      apply eq_sym.
      apply N.div_1_r.
    - rewrite Nat2N.inj_succ.
      simpl Bvector.BshiftRl_iter.
      rewrite shiftR1_div2.
      rewrite IHm.
      rewrite N.div_div.
      f_equal.
      rewrite N.pow_succ_r'.
      now rewrite N.mul_comm.

      apply N.pow_nonzero.
      all: discriminate.
Qed.

Lemma size_sizenat n : N.size n = N.of_nat (N.size_nat n).
  unfold N.size.
  unfold N.size_nat.

  induction n.
  - easy.
  - case_eq (Pos.size_nat p).
    intro.
    contradict H.
    case p; simpl; discriminate.
    intros.
    simpl.
    f_equal.
    rewrite Pos.of_nat_succ.
    rewrite <- H. clear H.
    induction p;
      [ simpl;
        case_eq (Pos.size_nat p);
        [ intro H; contradict H; case p; simpl; discriminate |
          intros;
          rewrite <- H;
          f_equal; apply IHp ]
          .. | simpl; easy].
Qed.

Lemma andOnes_mod m N : N.land N (2^m - 1) = (N mod 2^m)%N.
  rewrite N.sub_1_r.
  rewrite <- N.ones_equiv.
  now rewrite <- N.land_ones.
Qed.

Lemma ntimesCompose A (f : A -> A) n1 n2 a
  : ntimes f n1 (ntimes f n2 a) = ntimes f (n1 + n2) a.
  induction n1.
  trivial.
  simpl.
  f_equal.
  apply IHn1.
Qed.

Lemma OrComm n (w1 w2 : Word.t n)
  : OrW w1 w2 = OrW w2 w1.
  unfold OrW.
  apply liftComm.
  unfold Comm.
  apply Bool.orb_comm.
Qed.

Lemma AndComm n (w1 w2 : Word.t n)
  : AndW w1 w2 = AndW w2 w1.
  unfold AndW.
  apply liftComm.
  unfold Comm.
  apply Bool.andb_comm.
Qed.

Lemma OrDistrAnd n (w1 w2 w3 : Word.t n)
  : OrW w1 (AndW w2 w3) = AndW (OrW w1 w2) (OrW w1 w3).
  unfold OrW.
  apply liftDistr.
  unfold Distr.
  apply Bool.orb_andb_distrib_r.
Qed.

Lemma AndDistrOr n (w1 w2 w3 : Word.t n)
  : AndW w1 (OrW w2 w3) = OrW (AndW w1 w2) (AndW w1 w3).
  unfold OrW.
  apply liftDistr.
  unfold Distr.
  apply Bool.andb_orb_distrib_r.
Qed.

Lemma rotRCompose n r1 r2 (w : Word.t n)
  : RotRW r1 (RotRW r2 w) = RotRW (r1 + r2) w.
Proof.
  destruct w.
  unfold RotRW.
  unfold BRotR.
  all: apply ntimesCompose.
Qed.

Lemma rotRDistrXor n : forall (w1 w2 : Word.t n) r,
    RotRW r (XorW w1 w2) = XorW (RotRW r w1) (RotRW r w2).
Proof.
  intros w1 w2.
  intro r.
  unfold RotRW.
  unfold XorW.

  (* Reduced to assertion on BVectors *)
  induction r.
  - unfold BRotR; trivial.
  - unfold BRotR.
    unfold Word.BOps.ntimes.
    fold Word.BOps.ntimes.
    fold (BRotR r (Vmap2 xorb w1 w2)).
    fold (BRotR r w1).
    fold (BRotR r w2).
    rewrite IHr.
    generalize (BRotR r w1) as bv1.
    generalize (BRotR r w2) as bv2.
    (* Reduced to the single rotation case *)
    clear IHr.
    intros.
    destruct n.
    simpl; trivial.
    VSntac (Vmap2 xorb bv1 bv2).
    VSntac bv1. VSntac bv2.
    simpl.
    (* This assertion does not have an induction by n proof *)
    f_equal.
    * destruct n.
      assert (Vtail bv1 = Vnil).
      apply VO_eq.
      rewrite H2.
      assert (Vtail bv2 = Vnil).
      apply VO_eq.
      rewrite H3.
      trivial.

      assert (n < S n) by auto.
      repeat rewrite (Vlast_nth _ _ H2).
      rewrite Vnth_map2; trivial.
    * unfold Vmap2 at 1.
      fold (Vmap2 xorb bv1 bv2).
      rewrite <- H0.
      rewrite <- H1.
      (* Finally down to an assertion that can be proved by induction on n *)
      clear w1 w2 r H H0 H1.
      induction n.
      + apply VO_eq.
      + VSntac bv1. VSntac bv2.

        unfold Vremove_last at 1.
        simpl.
        f_equal.
        (* Now to rewrite to look like induction hypothesis *)
        repeat rewrite Vsub_cons.
        unfold Vmap2 at 1.
        fold (Vmap2 xorb (Vtail bv1) (Vtail bv2)).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vmap2 xorb (Vtail bv1) (Vtail bv2))).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vtail bv1)).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vtail bv2)).

        apply IHn.
Qed.
