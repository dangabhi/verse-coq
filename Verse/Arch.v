Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Types.Internal.
Require Import String.
Require Import List.
Import ListNotations.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)

  Parameter reg : varT.
  Parameter stack : varT.

  (* #####################
     The archvar to be passed to functions would be something like this
  *)
  Inductive farchvar : varT :=
  | rv (ty : type) : reg ty -> farchvar ty
  | sv (ty : type) : farchvar ty
  .

  Inductive var  : varT :=
  | r (ty : type)  : reg ty -> var ty
  | s (ty : type)  : stack ty -> var ty
  .

  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter wfinstr : instruction var -> Prop.
  
  Fixpoint wfinstrB (b : block var) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfinstr i) (wfinstrB bt)
    end.

  (** Generate code with assurance of well formedness **)

  (* #####################
     Could have a notation for @sigT type and projT1 
  *)

  Parameter callConv : forall lt, {lv : list (sigT farchvar) | map (@projT1 _ farchvar) lv = lt}.

  (* #####################
     The following would be the stack allocator that computes offsets 
     given the complete allocation 'list'. However I cannot think of 
     what proof obligation I want the function to satisfy.
  *)
  Parameter stalloc  : forall (l : list (sigT farchvar)), list (sigT var).

  Parameter generate : forall b : block var, wftypesB b -> wfvarB b -> wfinstrB b -> string.
  
  (**

    Translate the assignment statement to assembly. Certain assignment
    instructions can fail, for example a three address assignment like
    [A <= B + C] is not supported on a 2-address machine like x86. and
    hence the result of a translation is a [option (list mnemonic)]
    instead of just a [list mnemonics].

   *)

  (** Convert the loop statement in assembly instruction. *)
  (*Parameter loop
  : forall {b : bound}{ty : type (Bounded b)},
      var reg ty -> arg reg ty -> list mnemonic -> list mnemonic.*)

End ARCH.

