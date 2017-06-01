Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Function.
Require Import Verse.Types.Internal.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Basics.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)

  Parameter reg : varT.
  Parameter stack : varT.

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


  Parameter callConv : forall {p l : list type}, betaT var (p ++ l).

  (** 
     Alloc instantiates a function into a FB with the assumption that the 
     loopvar is allocated on stack 
  **)
  Definition alloc' (p lv lr : list type) (t : type) (lalloc : betaT reg lr) (f : function p lv lr t) : FB var t :=
    (lalloc _) (lam_cv r (callConv _ ((tr f) var))).

  (** 
    Alloc instantiates a function into a FB with the assumption that the 
    loopvar is allocated in a register by the user
  **)
  Definition alloc (p lv lr : list type) (t : type) (lalloc : betaT reg (t :: lr)) (f : function p lv lr t) : FB var t :=
    (lalloc _) (lam_cv r (callConv _ ((tr' f) var))).

  (** Generate code with assurance of well formedness **)
  Parameter generate : forall b : block var, wftypesB b -> wfvarB b -> wfinstrB b -> string.
  
End ARCH.



  