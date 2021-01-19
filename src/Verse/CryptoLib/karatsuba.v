Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.

Require Import Verse.

Open Scope verse_scope.

Require Import Vector.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Section Karatsuba.

  Variable sz : nat.

  Definition limb := word sz.

  Context {v : VariableT}.

  Inductive kvar : nat -> VariableT :=
  | kv     ty   : v direct ty -> kvar 0 direct ty
  | ksplit n ty : kvar n direct ty -> kvar n direct ty
                  -> kvar (S n) direct ty
  .

  Global Arguments kv [ty].
  Global Arguments ksplit [n ty].

  Definition kvar0   := kvar 0 direct.

  Definition getV {ty} (v : kvar0 ty)
    := match v with
       | kv v => v
       end.

  Coercion getV : kvar0 >-> v.

  Let low := false.
  Let high := true.

  Definition ksub {lvl ty}
             (i : bool)
             (x : kvar (S lvl) direct ty)
    : kvar lvl direct ty
    := match x with
       | ksplit a b => if i then a else b
       end.

  Notation tmpSet tnum n ty := (Vector.t (kvar n direct ty) tnum).

  Inductive ktmp tnum ty : nat -> Type :=
  | knil    : ktmp tnum ty 0
  | kS    n : tmpSet tnum n ty -> ktmp tnum ty n
              -> ktmp tnum ty (S n)
  .

  Global Arguments knil {tnum ty}.
  Global Arguments kS [tnum ty n].

  Definition currtmp tnum ty n (x : ktmp tnum ty (S n))
    := match x with
       | kS c r => (c, r)
       end.

  Fixpoint add {n ty} (a b c : kvar n direct ty)
    : list (statement v)
    :=
    match n as n0 return
             kvar n0 _ _
             -> kvar n0 _ _
             -> kvar n0 _ _
             -> _
       with
       | 0   => fun a b c =>
                  [ getV c ::= getV a + getV b ]%verse
       | S n => fun a b c =>
                  let al := ksub low a in
                  let ah := ksub high a in
                  let bl := ksub low b in
                  let bh := ksub high b in
                  let cl := ksub low c in
                  let ch := ksub high c in
                  add al bl cl ++ add ah bh ch
    end a b c.

  Fixpoint subsub {n ty} (a b c d : kvar n direct ty) (addeq : bool)
    : list (statement v)
    :=
      match n as n0 return
            kvar n0 _ _
            -> kvar n0 _ _
            -> kvar n0 _ _
            -> kvar n0 _ _
            -> _
      with
      | 0   => fun a b c d =>
                 if addeq then
                   [ getV d ::=+ getV a - getV b - getV c ]%verse
                 else
                   [ getV d ::=  getV a - getV b - getV c ]%verse
      | S n => fun a b c d =>
                 let al := ksub low a in
                 let ah := ksub high a in
                 let bl := ksub low b in
                 let bh := ksub high b in
                 let cl := ksub low c in
                 let ch := ksub high c in
                 let dl := ksub low d in
                 let dh := ksub high d in
                 subsub al bl cl dl addeq ++ subsub ah bh ch dh addeq
      end a b c d.

  (** Call notes : Maybe tmp [<nat>] could be a construct that gives
                   you a tmp var to use.
                   'mul' could be parametrized by a tmp var type
                   and its return could be a n-scope of that type
                   for some n.
                   Essentially a macro for writing code without
                   counting tmp variables upfront.
   *)
  Fixpoint mul {n ty} (a b : kvar n direct ty)
           (c : kvar (S n) direct ty)
           (tmp : ktmp 5 ty n)
    : list (statement v)
    := match n as n0 return
             kvar n0 _ _
             -> kvar n0 _ _
             -> kvar (S n0) _ _
             -> ktmp 5 _ n0
             -> _
       with
       | 0   => fun a b c tmp =>
                  let ch := ksub high c in
                  let cl := ksub low c in
                  [ getV cl ::= getV a * getV b;
                    getV ch ::= 0
                  ]%verse
       | S n => fun a b c tmp =>
                  let cl := ksub low c in
                  let ch := ksub high c in
                  let cll := ksub low cl in
                  let clh := ksub high cl in
                  let chl := ksub low ch in
                  let chh := ksub high ch in
                  let al := ksub low a in
                  let ah := ksub high a in
                  let bl := ksub low b in
                  let bh := ksub high b in
                  let (tmpv, tmpr) := currtmp _ _ _ tmp in
                  let t1 := hd tmpv in
                  let t2 := hd (tl tmpv) in
                  let t3 := hd (tl (tl tmpv)) in
                  let t4 := hd (tl (tl (tl tmpv))) in
                  let t5 := hd (tl (tl (tl (tl tmpv))))
                  in
                  mul al bl (ksplit t1 cll) tmpr
                      ++
                      mul ah bh (ksplit chh chl) tmpr
                      ++
                      add al ah t2
                      ++
                      add bl bh t3
                      ++
                      mul t2 t3 (ksplit t4 clh) tmpr
                      ++
                      subsub clh cll chl clh false
                      ++
                      (if n then
                        []
                      else
                        add clh t1 clh)
                      ++
                      (if n then
                        []
                      else
                        subsub t4 t1 chh chl true)
       end a b c tmp
  .

End Karatsuba.

Notation "X '₀'"
  := (ksub X false)
                      (only printing, left associativity, format "X '₀'", at level 40).

Notation "X '₁'"
  := (ksub X true)
                      (only printing, left associativity, format "X '₁'", at level 40).

Notation "X 'ₗ'"
       := (ksub X false)
            (only printing, left associativity, format "X 'ₗ'", at level 40).
Notation "X 'ₕ'"
  := (ksub X true)
       (only printing, left associativity, format "X 'ₕ'", at level 40).

Notation "[[ x %% y ]]" := (ksplit (kv x) (kv y)).
Notation "[[ x ## y ]]" := (ksplit x y).

Section Test.

  Variable var : VariableT.

  Variable a11 a12
           a21 a22
           b11 b12
           b21 b22
           c11 c12
           c21 c22
           c31 c32
           c41 c42
    : var direct Word64.

  Variable t11 t12 t13 t14 t15
           t21 t22 t23 t24 t25
           s1 s2 s3 s4 s5
    : var direct Word64.

  Definition a1 := [[ a12 %% a11 ]].
  Definition a2 := [[ a22 %% a21 ]].
  Definition a  := [[ a2 ## a1 ]].

  Definition b1 := [[ b12 %% b11 ]].
  Definition b2 := [[ b22 %% b21 ]].
  Definition b  := [[ b2 ## b1 ]].

  Definition c1 := [[ c12 %% c11 ]].
  Definition c2 := [[ c22 %% c21 ]].
  Definition cl := [[ c2 ## c1 ]].

  Definition c3 := [[ c32 %% c31 ]].
  Definition c4 := [[ c42 %% c41 ]].
  Definition ch := [[ c4 ## c3 ]].

  Definition c  := [[ ch ## cl ]].

  Definition t1 := [[ t11 %% t21 ]].
  Definition t2 := [[ t12 %% t22 ]].
  Definition t3 := [[ t13 %% t23 ]].
  Definition t4 := [[ t14 %% t24 ]].
  Definition t5 := [[ t15 %% t25 ]].

  Definition t   := [ t1; t2; t3; t4; t5 ]%vector.
  Definition s   := [ kv s1; kv s2; kv s3; kv s4; kv s5 ]%vector.

  Definition tmp := kS t (kS s knil).

  Definition splitMI1 := mul a1 b1 cl (kS s knil).
  Definition splitMI := mul a b c tmp.

  Compute (List.length splitMI1).
  Compute splitMI1.
  Compute (List.length splitMI).
  Compute splitMI.

  Definition splitMI1ann : AnnotatedCode var bvDenote.
    annotated_verse
      ((Vector.of_list (List.map (@instruct _ _ _)
                                 splitMI1))
         ++
         [ ASSERT (VAL c11 = BVmul (VAL a11) (VAL b11));
           ASSERT (VAL c12 = BVplus
                               (BVmul (VAL a12) (VAL b11))
                               (BVmul (VAL a11) (VAL b12)));
           ASSERT (VAL c21 = BVmul (VAL a12) (VAL b12))
      ]).
  Defined.

  Definition splitMIann : AnnotatedCode var bvDenote.
    annotated_verse
      ((Vector.of_list (List.map (@instruct _ _ _) splitMI))
          ++
      [ ASSERT (
               VAL c11 = BVmul (VAL a11) (VAL b11)
               /\
               VAL c12 = BVplus
                           (BVmul (VAL a12) (VAL b11))
                           (BVmul (VAL a11) (VAL b12))
               /\
               VAL c21 = BVplus
                           (BVplus (BVmul (VAL a11) (VAL b21))
                                   (BVmul (VAL a12) (VAL b12)))
                           (BVmul (VAL a21) (VAL b11))
               /\
               VAL c22 = BVplus
                           (BVplus
                              (BVplus (BVmul (VAL a22) (VAL b11))
                                      (BVmul (VAL a21) (VAL b12)))
                              (BVmul (VAL a12) (VAL b21)))
                           (BVmul (VAL a11) (VAL b22))
               /\
               VAL c31 = BVplus
                           (BVmul (VAL a22) (VAL b12))
                           (BVplus (BVmul (VAL a21) (VAL b21))
                                   (BVmul (VAL a12) (VAL b22)))
               /\
               VAL c32 = BVplus
                           (BVmul (VAL a22) (VAL b21))
                           (BVmul (VAL a21) (VAL b22))
             )
      ]).
  Defined.

End Test.

Require Import NArith.
Require Import Verse.BitVector.ArithRing.

Add Ring bitvector : (bit_arithm_ring 63).

Definition toProve1 : Prop.
  time getProp splitMI1ann.
Defined.

Definition proof1 : toProve1.
  time simplify.

  all: now ring_simplify.
Qed.

Definition toProve : Prop.
  time getProp splitMIann.
Defined.

Definition proof : toProve.
  time simplify.

  all: now ring_simplify.
Qed.
