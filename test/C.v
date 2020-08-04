(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Verse.Ast.
Require List.
Import List.ListNotations.
Import Ast.Expr.
Import Nibble.
Require Vector.
Import Vector.VectorNotations.

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.


Section Variables.
  Variable name : Set.
  Variable x : cvar uint8_t.
  Variable arr : cvar (array 42 uint16_t).
  Variable ptr : cvar (ptrToArray 30 uint64_t).


  Variable myfunc : name.
  Variable a : cvar uint64_t.
  Variable b : cvar uint64_t.
  Variable temp : cvar uint8_t.

  Definition index_ptr := Expr.ptrDeref ptr.

  Definition e : Expr.expr := Expr.app mul [Expr.cvar2exp a
                                            ; Expr.app plus [Expr.cvar2exp a ; Expr.cvar2exp b]].
  Definition lDec := [ declare temp; declare a; declare ptr ]%list.

  Definition stmts := [ assign (Expr.index (Expr.ptrDeref(ptr)) 2) e;
                          update a bitAnd [e]%vector
                      ]%list.

  (*
    Compute (declare x).
    Compute (declare arr).
    Compute (declare ptr).
    Compute (index (index_ptr) 10).
    Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
    Compute (verse_const uint8_t (Ox1,Ox2)).
   *)

  Goal to_print (function myfunc (params [declare temp; declare temp]) (Braces stmts)).
    print.
  Abort.
End Variables.
