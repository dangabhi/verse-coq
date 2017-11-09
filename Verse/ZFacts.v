Require Import BinNums.
Require Import ZArith.
Require Import Coq.ZArith.Zdigits.
Require Import ZArith_base.
Require Import BinInt.

Definition OneGtZero : (0 < 1)%Z.
  apply Pos2Z.is_pos.
Defined.  

Lemma two_power_even : forall n, Z.Even (two_power_nat (S n)).
Proof.
  pose (forall n, Z.even (two_power_nat (S n)) = true).
  trivial.
  intros.
  now apply Z.even_spec. 
Qed.

Lemma two_power_pos : forall n, (0 < two_power_nat n)%Z.
  intros.
  rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg; auto with *.
Qed.

Lemma binary_value_small : forall n b, (binary_value n b < two_power_nat n)%Z.
Proof.
  induction n.
  unfold binary_value. simpl.
  - intros; apply two_power_pos.
  - dependent inversion b.
    rewrite binary_value_Sn.
    pose (Zlt_le_succ _ _ (IHn t)).
    rewrite <- Z.add_1_l in l.
    assert (O_le_2 : (0 <= 2)%Z).
      auto with *.
    pose (Z.mul_le_mono_nonneg_l _ _ 2 O_le_2 l).
    rewrite Z.mul_add_distr_l in l0.
    assert (bv_small : (bit_value h < 2)%Z).
      case h; simpl; auto with *.
    rewrite two_power_nat_S.
    pose (Zplus_lt_compat_r _ _ (2 * binary_value n t) bv_small).
    auto with *.
Qed.
    
Lemma Z_to_binary_to_Z_mod : forall n z, binary_value n (Z_to_binary n z) = Zmod z (two_power_nat n).
Proof.
  induction n as [| n IHn].
  unfold two_power_nat, shift_nat. simpl. intros.
  assert (bounds : (0 <= z mod 1 < 1)%Z).
  exact (Z.mod_pos_bound z 1 OneGtZero).
  destruct (Z.lt_succ_r (z mod 1) 0) as [X Y].
  destruct bounds as [lower upper].
  apply (Z.le_antisymm _ _ lower (X upper)).
  
  intros.  rewrite Z_to_binary_Sn_z.
  rewrite binary_value_Sn.
  rewrite IHn.
  pose (Z.div_mod z (two_power_nat (S n))).
  assert (two_power_nat (S n) <> 0%Z).
       unfold two_power_nat.
       discriminate.
  pose (e H).
  rewrite e0 at 1 2.
  rewrite (Z.add_comm _ (z mod (two_power_nat (S n)))).
  rewrite Z.odd_add_mul_even .
  rewrite Z.div2_div.
  rewrite two_power_nat_S at 3.
  rewrite <- (Z.mul_assoc 2). rewrite (Z.mul_comm 2 (two_power_nat n * (z / two_power_nat (S n)))).
  rewrite (Z.div_add).
  rewrite (Z.mul_comm (two_power_nat n)).
  rewrite Z_mod_plus_full.
  rewrite (Zmod_small _ (two_power_nat n)).
  rewrite <- Z.div2_div.
  apply Z_div2_value.
  rewrite Z.ge_le_iff.
  apply Z.mod_pos_bound.
  rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg.
  apply Z.lt_0_2.
  apply Zle_0_pos.
  constructor.
  Search (0 <= _ / _)%Z.
  apply Z.div_pos.
  apply Z.mod_pos_bound.
    rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg.
  apply Z.lt_0_2.
  apply Zle_0_pos.
  apply Z.lt_0_2.
  Search (Z.div2 _ < _)%Z.
  rewrite <- Z.div2_div.
  apply Zdiv2_two_power_nat.
  rewrite Z.ge_le_iff.
  apply Z.mod_pos_bound.
  rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg.
  apply Z.lt_0_2.
  apply Zle_0_pos.
  apply Z.mod_pos_bound.
  rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg.
  apply Z.lt_0_2.
  apply Zle_0_pos.
  discriminate.
  apply two_power_even.
Qed.

Lemma binary_value_inj : forall n b1 b2, binary_value n b1 = binary_value n b2 <-> b1 = b2.
  intros.
  constructor; intros.
  Check f_equal.
  pose (f_equal (Z_to_binary n) H).
  now rewrite ?binary_to_Z_to_binary in e.
  now apply f_equal.
Qed.

Lemma Z_to_binary_trunc : forall n z, Z_to_binary n z = Z_to_binary n (z mod two_power_nat n).
  intros.
  apply binary_value_inj.
  rewrite ?Z_to_binary_to_Z_mod.
  now rewrite Z.mod_mod.
Qed.
