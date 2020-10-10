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

(* And what they mean *)
Definition expDenote {v}{ty} (k : kexp v ty) : expr v ty :=
  match k with
  | MUL     a b    => a * b
  | PLUS    a b    => a + b
  | SUBSUB  a c d  => a - c - d
  end.
