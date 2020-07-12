Require Import Verse.CryptoLib.poly1305.c.karatsuba.tree.
Require Import Verse.

Definition Poly A = list A.



Inductive KVar : VariableT :=
| KaratsubaVar : forall (ty : type direct), nat -> KVar direct ty.

Definition assoc A := list (A * nat).

Arguments KaratsubaVar [ty].
Arguments KVar [k].

Notation "$ N" := (KaratsubaVar N) (at level 0).



Section Karatuba.
  Variable var : VariableT.


  Arguments var [k].
  Variable ty : type direct.

  Definition plus {n} (t1 t2 : tree (expr v ty) n) : tree (expr v ty) n
    := let fun e1 e2 => e1 + e2

  Definition freshList := list (var ty).

  Definition Assoc A := list (A * nat).



    := match

(* a0 b0  , (a0 + a1) (b0 + b1)

let x0 = a0 b0;
let x1 = a1 b1
let x2 = (a0 + a1)
let x3 = (a1 + b1)
let x4 = x2 * x3 - x0 - x1
in (x0 , 0), (x1, 2), (x4 , 1)

x0,
x1,
x4,


*)
Fixpoint kTree (A : Type) n : Type :=
  match n with
  | 0 => A
  | (S m) => kTree A m * kTree A m
  end.





Section Kar.
  Definition abs (ty : verse_type_system direct) := forall v : VariableT, expr v ty.

  (*
    a0 + X a1 + X^2 (a2 + X a3)  + X^4 (a4 + X

   *)


(*
Notation "a × b" := (mul a b) (at level 40, left associativity).
 *)

Inductive Term : Type -> Type -> Type :=
| L     : forall A, A -> Term A  False
| R     : forall B, B -> Term False B
| Plus  : forall A B, Term A B -> Term A B -> Term A B
| Minus : forall A B, Term A B -> Term A B -> Term A B
| Mul   : forall A B, Term A False -> Term False B -> Term A B.

Arguments L [A].
Arguments R [B].
Arguments Plus [A B].
Arguments Minus [A B].
Arguments Mul   [A B].

Require Import BinInt.
Require Import ZArith.

Inductive Coef A B : nat -> Type :=
| coef : forall i, Z ->  A -> B -> Coef A B i.


Definition monomial A B := sigT (Coef A B).

Definition grad {A B}(m : monomial A B) : nat :=
  match m with
  | existT _ i _ => i
  end.


(**

p = a * b =

let aP0 = (a00 + a10)
    aP1 = (a01 + a11)
    a0P = a00 + a01
    a1P = a10 + a11

    bP0 = (b00 + b10)
    bP1 = (b01 + b11)

    aP = aP0 + aP1 X
    bP = bP0 + bP1 X

    a0P =
    b0P = b00 + b01

    p00 = a00 b00
    p02 = a01 b01
    q01 = a0P b0P
    p01 = q01 - p00 - p02

    p0 = p00 + X p01 + X^2 p02

    p0 = a0 b0
    q1 = aP bP
    p2 = a1 b1
    p1 = q1 - p0 - p2
 in p00                a00 b00
 + p01 X               (a00 + a01)(a0a0P b0P
 + (p02 + p10) X^2
 + p11 X^3
 + (p12 + p20) X^4
 + p21 X^5
 + P22 x^6


 p0 + p1 X2 + p2 X^4


p0 + p1 X^2 + p2 X4
              where p0 = a0 b0; p2 = a1 b1; p1 = q1 - p0 - p2; q1 = (a0 + a1)(b0 + b1)

p0 = a0 * b0
p2 = a1 * b1
q1 = (a0 + a1)(b0 +b1)

p0 = p00 +
[p00 = a00 b00 ; q01 = (a00 + a01)(b00 + b01) ; p02 = a01 b01 ]
[q10 = (a0 + a1)0 (b0 + b1)



a = a00 + a01 X                 + (a10 + a11 X) Y
b = b00 + b01 X                 + (b10 + b11 X) Y

a b = (a0 + X2 a1) (b0 + X2 b1)
    = p0 + X2 (q1 - p0 - p2) + X^4 p2
    = p00 + (q01 - p00 - p02) X + X2 p02
                                + X2
    p00 = a00 * b00
    q01 = (a00 + a01)
    p02 = a01 * b01


p1 = (a0 + a1) * (b0 + b1) - p0 - p2
p2 = a1 * b1


*)


Arguments V [A].
Arguments Plus [A].
Arguments Minus [A].
Arguments Mul  [A B].

Require List.
Import List.ListNotations.

Definition karatsuba {A B} (i : nat) (a : A * A) (b : B * B) : Poly (Term (A * B))
  := match a, b with
     | (a0,a1), (b0,b1)
       => let p0 := V (a0, b0)  in
         let q1 := Mul (Plus (V a0) (V a1)) (Plus (V b0) (V b1)) in
         let p2 := V (a1, b1) in
         [ (p0,0) ; (Minus (Minus q1 p0) p2, i); (p2, 2 * i)]
     end%list.
