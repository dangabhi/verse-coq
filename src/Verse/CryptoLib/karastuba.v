Require Import BinNat.
Require Import Verse.
Require Vector.
Open Scope verse_scope.

(* Only these expressions are involved in karatsuba multiplication *)
Inductive kexp (v : VariableT) (ty : type direct):=
| MUL    (a b : v direct ty)    : kexp v ty (* a * b *)
| PLUS   (a b : v direct ty)    : kexp v ty (* a + b *)
| SUBSUB (a c d : v direct ty)  : kexp v ty (* a - c - d *)
.

Arguments MUL     [v ty].
Arguments PLUS    [v ty].
Arguments SUBSUB  [v ty].

(* And what they mean *)
Definition expDenote {v}{ty} (k : kexp v ty) : expr v ty :=
  match k with
  | MUL     a b    => a * b
  | PLUS    a b    => a + b
  | SUBSUB  a c d  => a - c - d
  end.

Definition kInst (v : VariableT) (ty : type direct) := (v direct ty * kexp v ty)%type.

Inductive idx := low | high | carry.


Inductive kvar (v : VariableT) : VariableT :=
| kv    : forall sz, v direct (word sz) -> kvar v direct (word sz)
| ksub  : forall sz, kvar v direct (word (S sz)) -> idx -> kvar v direct (word sz)
(* The temporary variables *)
| kt0   : forall sz, kvar v direct (word sz)
| kt1   : forall sz, kvar v direct (word sz)
| kt2   : forall sz, kvar v direct (word sz).


Arguments kv [v sz].
Arguments ksub [v sz].
Arguments kt0 [v].
Arguments kt1 [v].
Arguments kt2 [v].


Require List.
Import List.ListNotations.

Definition ksplit {sz}{v}(ki : kInst (kvar v) (word (S sz)))
  : list (kInst (kvar v) (word sz))
  := let (x,ke) := ki in
     let xL  := ksub x low   in
     let xH  := ksub x high  in
     let xC  := ksub x carry in
     let u0 := kt0 sz in
     let u1 := kt1 sz in
     let u2 := kt2 sz in
     match ke with
     | MUL a b =>
       let aL := ksub a low  in
       let aH := ksub a high in
       let bL := ksub b low  in
       let bH := ksub b high
       in [ (xL , MUL aL bL);
            (xC , MUL aH bH);
            (u0 , PLUS aL aH);
            (u1 , PLUS bL bH);
            (u2 , MUL u0 u1);
            (xH , SUBSUB u2 u0 u1)
         ]
     | PLUS a b =>
       let aL := ksub a low  in
       let aH := ksub a high in
       let bL := ksub b low  in
       let bH := ksub b high
       in [ (xL , PLUS aL bL);
          (xH , PLUS aH bH)  ]
     | SUBSUB a c d =>
       let aL := ksub a low in
       let aH := ksub a high in
       let cL := ksub c low in
       let cH := ksub c high in
       let dL := ksub d low in
       let dH := ksub d high
         in [ (xL , SUBSUB aL cL dL);
            (xH, SUBSUB aH cH dH) ]

     end.

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
Notation "A - B - C" := (SUBSUB A B C) (only printing, format "A  - B  - C", at level 40).


Axiom var : VariableT.
Axiom a b c : kvar var direct (word 3).



Compute List.concat (List.map ksplit (ksplit (a, MUL b c))).
