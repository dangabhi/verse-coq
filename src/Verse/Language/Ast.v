(* begin hide *)
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.

Require Import Bool.
Require Import Omega.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* end hide *)

(** * The Verse language as an inductive data type.

This module exposes the abstract syntax of the verse programming
language. The design takes the following points into consideration.

- A large number of instructions are shared across architectures. This
  include instructions that perform various arithmetic operations,
  bitwise operations etc.

- Certain architecture support various special registers like xmm
  registers, special instructions like native AES operations.

The design gives a portable way of expressing the former and
parameterise over the latter. Let us include arithmetic operators
first.

*)

Require Export Verse.Language.Operators.

(** * The abstract syntax tree.

This section build up towards the the inductive type that capture the
verse language's abstract syntax tree. One of the most important
elements in a programming language is variables. In verse, program
fragments are parameterised by an abstract variable type that is used
through out.

*)

Section AST.
  Variable v   : VariableT.


  (** Type that captures a memory variable's indices. *)
  Definition Indices {b e ty} (_ : v (array b e ty)) := { i : nat | i < b }.


  (** ** Arguments.

      Each verse program fragment consists of instructions applied to
      some arguments. Variables are one form of arguments, but so does
      indexed arrays or constants.

   *)

  Inductive argKind := lval | rval.
  Inductive arg : argKind -> VariableT :=
  | var   : forall aK, forall {k} {ty : type k}, v ty -> arg aK ty
  | const : forall {ty : type direct}, constant ty  -> arg rval ty
  | index : forall aK, forall {b : nat}{e : endian}{ty : type direct} (x : v (array b e ty)),
        Indices x  -> arg aK ty
  .

  Definition larg := arg lval.
  Definition rarg := arg rval.

  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
  Inductive assignment : Type :=
  | extassign4
    : forall (ty : type direct), op binary ternary -> larg ty -> larg ty -> rarg ty -> rarg ty -> rarg ty -> assignment
  | extassign3
    : forall (ty : type direct), op binary binary -> larg ty -> larg ty -> rarg ty -> rarg ty -> assignment
  | assign3
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> rarg ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall (ty : type direct), uniop -> larg ty -> rarg ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> assignment (** e.g. x += y    *)
  | update1
    : forall (ty : type direct), uniop -> larg ty -> assignment                   (** e.g. x ~= x    *)
  .

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
  Inductive instruction : Type :=
  | assign  : assignment -> instruction
  | moveTo  : forall b e ty, forall (x : v (array b e ty)), Indices x -> v ty -> instruction
  | CLOBBER : forall k (ty : type k), v ty -> instruction
  .

  Global Definition code := list instruction.
  (* begin hide *)

  (* Some instruction error checking code *)

  Definition isEndian {aK} {k} {ty : type k} (nHostE : endian) (a : arg aK ty) :=
    let eqEndb (e f : endian) : bool :=
        match e, f with
        | littleE, littleE
        | bigE, bigE       => true
        | _, _             => false
        end
    in
    match a  with
    | @index  _ _ ne _ _ _ => eqEndb ne nHostE
    | _                 => false
    end.

  (** Function to check if a non-mov/store instruction uses arrays of offending endianness.
      Passing hostE as parameter allows all arrays. **)

  Definition endianError (nHostE : endian) (i : instruction) :=
    match i with
    | assign e  => match e with
                   | assign2 nop _ _    => false
                   | assign3 _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
                   | extassign4 _ a1 a2 a3 a4 a5 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3) || (isEndian nHostE a4) || (isEndian nHostE a5)
                   | extassign3 _ a1 a2 a3 a4 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3) || (isEndian nHostE a4)
                   | assign2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update1 _ a1       => (isEndian nHostE a1)
                   end
    | _ => false
    end
  .

  Definition supportedInst (nhostE : endian) := fun i => endianError nhostE i = false.

  Definition instCheck e i : {supportedInst e i} + {~ supportedInst e i}
      := bool_dec (endianError e i) false.

  (* end hide *)


End AST.

Arguments Indices [v b e ty] _.


(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

*)
Record iterator (ty : type memory)(v : VariableT)
  := { setup    : code v;
       process  : v memory ty -> code v;
       finalise : code v
     }.


(* begin hide *)
Arguments setup [ty v] _.
Arguments process [ty v] _ _.
Arguments finalise [ty v] _.

Arguments var [v aK k ty] _ .
Arguments const [v ty] _ .
Arguments index [v aK  b e ty]  _ _.
Arguments extassign3 [v ty] _ _ _ _ _.
Arguments extassign4 [v ty] _ _ _ _ _ _.
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .
Arguments moveTo [v  b e ty] _ _ _.
Arguments CLOBBER [v k ty ] _.
(* end hide *)
