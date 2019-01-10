(* begin hide *)

Require Import Verse.Error.
Require Import Coq.NArith.Ndigits.
Require Import BinNums.
Require Import NArith.
Require Import String.
Require Import Ascii.
Require Import Verse.PrettyPrint.
Require Import Arith.
Require Verse.Nibble.

Require Import CoLoR_VecUtil.

Import Basics.

Local Open Scope N_scope.

Set Implicit Arguments.

(* end hide *)

(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)


Notation t := (Bvector.Bvector).

Definition bytes n := t (4 * (2 * n)).
(* Written in this form instead of '8 * n' for type unification of
   translation from Nibbles
*)

Require Verse.Nibble.
Definition fromNibbles {n} (v : Vector.t Verse.Nibble.Nibble n) : t (4 * n) :=
  (N2Bv_gen (4 * n) (Verse.Nibble.toN v)).

Notation "[[ N ]]" := (fromNibbles N) (at level 100).

(**

Conversely we can convert a word constant to its hexadecimal string as
follows:

*)

Definition mapP {T U} (f : T -> U) (p : T * T) :=
  let '(p1, p2) := p in (f p1, f p2).

(* This function lifts numeric operations with overflow *)
Definition numOverflowBinop {n} f (x y : t n) : t n * t n :=
  let break_num m := (m / 2 ^ (N.of_nat n), m)
  in
  mapP (N2Bv_gen n)
       (break_num (f (Bv2N n x) (Bv2N n y))).

(* This function lifts a numeric binop with one big argument and two outputs *)
Definition numBigargExop {n} f (x y z : t n) : t n * t n :=
  let make_big x y := (2 ^ (N.of_nat n) * x + y) in
  mapP (N2Bv_gen n)
       (f (make_big (Bv2N n x) (Bv2N n y))
          (Bv2N n z)).


(** This function lifts a numeric binary function to the word type *)
Definition numBinOp {n} f  (x y : t n) : t n :=
  N2Bv_gen n (f (Bv2N n x) (Bv2N n y)).
Module BOps.

  Definition BShiftL m (n : nat) :=
    match n with
    | 0%nat    => fun vec => vec
    | S np => fun vec => Bvector.BshiftL_iter np vec m
    end.

  Definition BShiftR m (n : nat) :=
    match n with
    | 0%nat  => fun vec => vec
    | S np   => fun vec => Bvector.BshiftRl_iter np vec m
    end.

  Fixpoint ntimes A (f : A -> A) n (a : A) :=
    match n with
    | 0%nat => a
    | S n   => f (ntimes f n a)
    end.

  Definition BRotL m n : Bvector.Bvector n -> Bvector.Bvector n :=
    let BRotL1 v := match v with
                    | []      => []
                    | h :: vt => Vadd vt h
                    end
    in
    fun vec => ntimes BRotL1 m vec.

  Definition BRotR m n : Bvector.Bvector n -> Bvector.Bvector n :=
    let BRotR1 v := match v with
                    | [] => []
                    | v  => Vlast (Vhead v) v :: Vremove_last v
                    end
    in
    fun vec => ntimes BRotR1 m vec.

End BOps.


Definition AndW := Vmap2 andb.
Definition OrW  := Vmap2 orb.
Definition XorW := Vmap2 xorb.
Definition NegW := Bvector.Bneg.

Definition ShiftLW m := BOps.BShiftL m.
Definition ShiftRW m := BOps.BShiftR m.
Definition RotLW m := BOps.BRotL m.
Definition RotRW m := BOps.BRotR m.

Notation "A & B" := (AndW A B) (at level 100) : word_scope.
Notation "A ❘ B" := (OrW A B)  (at level 100) : word_scope.
Notation "A ⊕ B" := (XorW A B) (at level 100) : word_scope.
Notation "~ A"   := (NegW A)   (at level 75, right associativity) : word_scope.
Notation "A ≫ m" := (ShiftRW m A) (at level 100) : word_scope.
Notation "A ≪ m" := (ShiftLW m A) (at level 100) : word_scope.
Notation "A ⋘ m" := (RotLW m A) (at level 100) : word_scope.
Notation "A ⋙ m" := (RotRW m A) (at level 100) : word_scope.

Infix "+" := (numBinOp N.add) : word_scope.
Infix "*" := (numBinOp N.mul) : word_scope.
Infix "-" := (numBinOp N.sub) : word_scope.
Infix "/" := (numBinOp N.div) : word_scope.
