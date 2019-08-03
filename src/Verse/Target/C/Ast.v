Require Verse.TypeSystem.
Require Verse.Nibble.
Require Verse.Error.
Set Implicit Arguments.

(** * Naming stuff

This type is used for naming functions. We can create function names
by assuming names.

 *)

Axiom name : Set.

(** * The type of C

We now capture the type system for C. Only types that arise in
translation of verse code is captured here.

 *)

Inductive type : TypeSystem.kind -> Set :=
| uint8_t    : type TypeSystem.direct
| uint16_t   : type TypeSystem.direct
| uint32_t   : type TypeSystem.direct
| uint64_t   : type TypeSystem.direct
| array      : nat -> type TypeSystem.direct    -> type TypeSystem.memory
| ptrToArray : nat -> type TypeSystem.direct    -> type TypeSystem.memory
.


(** * The expression language.

We begin by defining C expressions. Since C is our target language,
and not a source language, its role is merely in obtaining the pretty
printed code. Therefore, being not too strict in the types would aid
us considerabily.

 *)

(** * Explanation for the constructors.

Essentially, C expressions are Verse operators applied to
subexpressions. However, there are some additional constructors which
we now explain.

* The constructors [rotateL] and [rotateR] for calls to C functions
  that implement the rotate instructions. For some strange reason C
  does not have rotate instructions.

* [convert_to] and [convert_from] for endian conversion functions.

* [verse_u8, verse_u16, verse_u32, verse_u64] for constant creation.
  The limitation of the notation system to combine nibbles without
  interleaving spaces meant we need a hack to get this working.

*)

Require Import Verse.Language.Core.

Require Vector.
Import Vector.VectorNotations.

Module Internal.

  Inductive voidparams : Set.

  Inductive expr :=
  | app : forall n, op n -> Vector.t expr n -> expr
  | index          : expr -> nat -> expr
  | rotateL        : nat -> (expr * nat) -> expr
  | rotateR        : nat -> (expr * nat) -> expr
  | convert_to     : endian -> nat -> expr -> expr
  | convert_from   : endian -> nat -> expr -> expr
  | verse_u8       : forall c, c -> expr
  | verse_u16      : forall c, c -> expr
  | verse_u32      : forall c, c -> expr
  | verse_u64      : forall c, c -> expr.



End Internal.


Import Internal.

Definition const (ty : type TypeSystem.direct) := Internal.expr.
Canonical Structure c_type_system : TypeSystem.typeSystem
    := TypeSystem.TypeSystem type const.

(** ** Variables and Constants as expressions.

Constants and variables are also represented by expressions. This is
an over-approximation of the situation as constants and variables are
only subclasses of expressions. However, since our interest is only in
the pretty printed form, this is not really a problem.

 *)


Definition cvar k (ty : type k) := Internal.expr.
Arguments cvar [k].
Inductive declaration :=
| declare_variable : forall k (ty : type k), cvar ty -> declaration.

Arguments declare_variable [k].


Inductive statement :=
| declareStmt : declaration -> statement
| assign      : expr -> expr -> statement
| update      : forall n, op (S n) -> expr -> Vector.t expr n -> statement
| increment   : expr -> statement
| decrement   : expr -> statement.


Definition declare k ty := @declare_variable k ty.
Arguments declare [k ty].

Inductive block :=
| endBlock   : block
| sequence   : statement -> block -> block.


Print List.fold_right.
Definition mkBlock := List.fold_right sequence endBlock.


Inductive whileLoop :=
| while : expr ->    (* counter expression *)
          block ->   (* body               *)
          whileLoop.

(* All the compiled C functions look like a setup block, an optional while loop
     followed by a finalisation block
 *)
Inductive function :=
| void_function :
    name -> forall params,
      params ->
      block  ->        (* setup        *)
      option whileLoop -> (* iteration    *)
      block         -> (* finalisation *)
      function.


Require List.
Print List.fold_right.
Import List.ListNotations.
