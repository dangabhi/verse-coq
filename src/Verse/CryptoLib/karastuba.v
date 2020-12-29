Require Import BinNat.
Require Import Verse.
Require Vector.

Require List.
Import List.ListNotations.

Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.

Require Import Verse.
Close Scope vector_scope.
Open Scope verse_scope.
Open Scope list_scope.
(*
 x = a * b

64 bit variables carrying 32 bit values

a = aL + 2^k aH          (al * bl) + 2^k (...) + 2^2k ah bh
b = bL + 2^k bH            xl            xh          xc



xL = aL * bL
xH = a


  *)

Notation "'Fin0'" := (Fin.F1).
Notation "'Fin1'" := (Fin.FS Fin0).
Notation "'Fin2'" := (Fin.FS Fin0).

Section Karatsuba.

  Variable base : nat.

  Inductive bigv (v : VariableT) : VariableT :=
  | sv : v direct (word (S base)) -> bigv v direct (word base)
  | tv :  forall sz, bigv v direct (word sz)
                     -> bigv v direct (word sz)
                     -> bigv v direct (word sz)
                     -> bigv v direct (word (S sz)).

  Inductive idx := low | high | carry.

  Inductive kvar (v : VariableT) : nat -> VariableT :=
  | kv    : v direct (word (S base)) -> kvar v 0 direct (word base)
  | kbig  : forall lvl, kvar v lvl direct (word (lvl + base))
                       -> kvar v lvl direct (word (lvl + base))
                       -> kvar v lvl direct (word (lvl + base))
                       -> kvar v (S lvl) direct (word (S (lvl + base)))
  (* Feels like ksub and kt shouldn't be constrnnuctors, but functions.
     The problem is you cannot dismiss the case of the thing being
     indexed being a 'kv'
   *)
  | ksub  : forall lvl, kvar v (S lvl) direct (word (S lvl + base))
                        -> idx -> kvar v lvl direct (word (lvl + base))
  (* The temporary variables *)
  | kt    : forall lvl, kvar v (S lvl) direct (word (S lvl + base))
                       -> idx -> kvar v lvl direct (word (lvl + base)).

  Arguments kv [v].
  Arguments kbig [v lvl].
  Arguments ksub [v lvl].
  Arguments kt [v lvl].

  Definition kty n := word (n + base).

  (* Only these expressions are involved in karatsuba multiplication *)
  Inductive kexp (v : VariableT) (ty : type direct) :=
  | MUL (a b : v _ ty) : kexp v ty
  | PLUS (a b : v _ ty) : kexp v ty
  | SUBSUB (a b c : v _ ty) : kexp v ty
  .

  Global Arguments MUL     [v ty].
  Global Arguments PLUS    [v ty].
  Global Arguments SUBSUB  [v ty].
(*  Global Arguments CPROP   [v n].*)

  Inductive kInst v : nat -> Type :=
  | kassign n : (kvar v n direct (kty n)) ->
                kexp (kvar v n) (kty n) ->
                kInst v n
  | CProp   n : (kvar v (S n) direct (kty (S n))) ->
                (kvar v (S n) direct (kty (S n))) ->
                kInst v (S n)
  .

  Arguments kassign [v n].
  Arguments CProp [v n].

  Definition kProg (v : VariableT) n := list (kInst v n).

  (* And what they mean *)

  Fixpoint lvlDenote v n : Type
    := match n with
       | 0   => v direct (word (S base))
       | S n => lvlDenote v n * lvlDenote v n * lvlDenote v n
       end.

  Fixpoint varDenote [v] [lvl] (x : kvar v lvl _ (word (lvl + base)))
    : lvlDenote v lvl :=
    match x in @kvar _ lvl0 _ _ return lvlDenote v lvl0 with
       | kv x         => x
       | kbig x y z   => (varDenote x, varDenote y, varDenote z)
       | ksub x low   => fst (fst (varDenote x))
       | ksub x high  => snd (fst (varDenote x))
       | ksub x carry => snd (varDenote x)
       | kt x low     => fst (fst (varDenote x))
       | kt x high    => snd (fst (varDenote x))
       | kt x carry   => snd (varDenote x)
    end.

  Definition expDenote [v] (k : kexp (kvar v 0) (word base))
    : expr v (word (S base))
    := match k with
       | MUL     a b    => (varDenote a) * (varDenote b)
       | PLUS    a b    => (varDenote a) + (varDenote b)
       | SUBSUB  a c d  => (varDenote a) - (varDenote c) - (varDenote d)
       end.

  Definition instDenote [v] (i : kInst v 0)
    : instruction v (word (S base)) :=

    match i with
    | @kassign _ 0 a e => assign (toLexpr (varDenote a)) (expDenote e)
    (*
    | @CProp _ 0 a b   => binopUpdate (toLexpr (varDenote (ksub b low)))
                                         plus
                                         (valueOf (var (varDenote (ksub a high))))
*)
    end.

  (** TODO : Absolutely no clue why the extra CProp thing is required!

             It is much worse -- turns out it requires that extra clause
             for the second constructor. Changing order of constructors
             in kInst requires a redundant kassign match instead of the
             CProp!
   *)

  Definition ksplitInst [lvl][v]
                        (ktmp : kvar v (S lvl) direct (word (S lvl + base)))
                        (ki : kInst v (S lvl))
    : (list (kInst v lvl)) :=
    match ki in kInst _ (S lvl0)
          return kvar _ (S lvl0) _ (word (S lvl0 + _))
                 -> list (kInst _ lvl0)
    with
    | @kassign _ (S kalvl) x (MUL a b) =>
      fun t =>
        let xL  := ksub x low   in
        let xH  := ksub x high  in
        let xC  := ksub x carry in
        let u0 := kt t low in
        let u1 := kt t high in
        let u2 := kt t carry in
        let aL := ksub a low  in
        let aH := ksub a high in
        let bL := ksub b low  in
        let bH := ksub b high in
        [ kassign xL (MUL aL bL);
        kassign xC (MUL aH bH);
        kassign u0 (PLUS aL aH);
        kassign u1 (PLUS bL bH);
        kassign u2 (MUL u0 u1);
        kassign xH (SUBSUB u2 xL xC)
        ] ++
          match kalvl as lvl0
                return kvar _ lvl0 _ _ ->
                       kvar _ lvl0 _ _ ->
                       kvar _ lvl0 _ _ -> _
          with
          | 0   => fun _ _ _ => []
          | S n => fun xL xH xC =>
                     [ CProp xL xH;
                       CProp xH xC
                     ]
          end xL xH xC
    | @kassign _ (S _) x (PLUS a b) =>
      fun _ =>
        let xL  := ksub x low   in
        let xH  := ksub x high  in
        let xC  := ksub x carry in
        let aL := ksub a low  in
        let aH := ksub a high in
        let aC := ksub a carry in
        let bL := ksub b low  in
        let bH := ksub b high in
        let bC := ksub b carry
        in [ kassign xL (PLUS aL bL);
           kassign xH (PLUS aH bH);
           kassign xC (PLUS aC bC) ]

    | @kassign _ (S _) x (SUBSUB a c d) =>
      fun _ =>
        let xL  := ksub x low   in
        let xH  := ksub x high  in
        let xC  := ksub x carry in
        let aL := ksub a low in
        let aH := ksub a high in
        let aC := ksub a carry in
        let cL := ksub c low in
        let cH := ksub c high in
        let cC := ksub c carry in
        let dL := ksub d low in
        let dH := ksub d high in
        let dC := ksub d carry
        in [ kassign xL (SUBSUB aL cL dL);
           kassign xH (SUBSUB aH cH dH);
           kassign xC (SUBSUB aC cC dC)
           ]
    | CProp a b => fun _ =>
                     [ kassign (ksub b low)
                               (PLUS (ksub b low) (ksub a carry)) ]
    end ktmp.

  Definition ksplit [lvl][v]
             (kp : kProg v  (S lvl))
             (ktmp : kvar v (S lvl) direct (word (S lvl + base)))
    : list (kInst v lvl)
    := List.concat (List.map (ksplitInst ktmp) kp).

End Karatsuba.

Arguments kv [base v].
Arguments ksub [base v lvl].
Arguments kt [base v lvl].

Arguments ksplitInst [base lvl v].

Notation "X '₀'"
  := (kt X Fin0)
                      (only printing, left associativity, format "X '₀'", at level 40).

Notation "X '₁'"
  := (kt X Fin1)
                      (only printing, left associativity, format "X '₁'", at level 40).

Notation "X '₂'"
  := (kt X Fin2)
                      (only printing, left associativity, format "X '₂'", at level 40).

Notation "X 'ₗ'"
       := (ksub X low)
            (only printing, left associativity, format "X 'ₗ'", at level 40).
Notation "X 'ₕ'"
  := (ksub X high)
       (only printing, left associativity, format "X 'ₕ'", at level 40).
Notation "X '₊'"
  := (ksub X carry)
       (only printing, left associativity, format "X '₊'", at level 40).
Notation "A × B" := (MUL A B) (only printing, format "A  ×  B", at level 50).
Notation "A ⨥ B" := (PLUS A B) (only printing, format "A  ⨥  B", at level 50).
Notation "A - B - C" := (SUBSUB A B C) (only printing, format "A  -  B  -  C", at level 50).
Notation "[ X ; .. ; Y ]"
  := (cons X .. (cons Y nil) ..)
       (only printing, format "[ '//' X ; '//' .. ; '//' Y '//' ]").

Notation "[[[ x ]]]" := (kv x) (at level 100).
Notation "[[ x %% y %% z ]]" := (kbig _ _ _ (kv x) (kv y) (kv z)).
Notation "[[ x ## y ## z ]]" := (kbig _ _ _ x y z).


Section Test.

  Variable var : VariableT.

  Variable a11 a12 a13
           a21 a22 a23
           a31 a32 a33
           b11 b12 b13
           b21 b22 b23
           b31 b32 b33
           c11 c12 c13
           c21 c22 c23
           c31 c32 c33
    : var direct (word 4).

  Variable t11 t12 t13
           t21 t22 t23
           t31 t32 t33
           s1  s2  s3
    : var direct (word 4).

  Definition a1 := [[ a11 %% a12 %% a13 ]].
  Definition a2 := [[ a21 %% a22 %% a23 ]].
  Definition a3 := [[ a31 %% a32 %% a33 ]].
  Definition a  := [[ a1 ## a2 ## a3 ]].

  Definition b1 := [[ b11 %% b12 %% b13 ]].
  Definition b2 := [[ b21 %% b22 %% b23 ]].
  Definition b3 := [[ b31 %% b32 %% b33 ]].
  Definition b  := [[ b1 ## b2 ## b3 ]].

  Definition c1 := [[ c11 %% c12 %% c13 ]].
  Definition c2 := [[ c21 %% c22 %% c23 ]].
  Definition c3 := [[ c31 %% c32 %% c33 ]].
  Definition x  := [[ c1 ## c2 ## c3 ]].

  Definition t1 := [[ t11 %% t12 %% t13 ]].
  Definition t2 := [[ t21 %% t22 %% t23 ]].
  Definition t3 := [[ t31 %% t32 %% t33 ]].
  Definition t := [[ t1 ## t2 ## t3 ]].

  Definition s := [[ s1 %% s2 %% s3 ]].

  Definition mI1 := kassign _ _ _ c1 (MUL a1 b1).
  Definition mI := kassign _ _ _ x (MUL a b).

  Compute  mI.

  Definition splitMI1
    := List.map (@instDenote _ _) (ksplitInst s mI1).

  Definition splitMI
    := List.map (@instDenote _ _ ) (List.concat (List.map (ksplitInst s) (ksplitInst t mI))).

  Open Scope verse_scope.
  Compute (List.length splitMI).
  Compute splitMI.

  Definition splitMI1ann : AnnotatedCode var bvDenote.
    annotated_verse
      ((Vector.of_list (List.map (fun i => instruct (existT _ _ i))
                                 splitMI1))
         ++
         [ ASSERT (VAL c11 = BVmul (VAL a11) (VAL b11));
           ASSERT (VAL c12 = BVplus
                               (BVmul (VAL a12) (VAL b11))
                               (BVmul (VAL a11) (VAL b12)));
           ASSERT (VAL c13 = BVmul (VAL a12) (VAL b12))
      ]).
  Defined.

  Definition splitMIann : AnnotatedCode var bvDenote.
    annotated_verse
      ((Vector.of_list (List.map (fun i => instruct (existT _ _ i))
                                 splitMI))
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

Add Ring bitvector : (bit_arithm_ring 127).

Definition toProve1 : Prop.
  getProp splitMI1ann.
Defined.

Definition proof1 : toProve1.
  time simplify.

  all: now ring_simplify.
Qed.

Definition toProve : Prop.
  getProp splitMIann.
Defined.

Definition proof : toProve.
  time simplify.

  all: now ring_simplify.
Qed.
