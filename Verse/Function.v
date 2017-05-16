Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import Arch.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Fixpoint listSet {A : Type} (l : list A) : Ensemble A :=
  match l with
  | [] => Empty_set _
  | a :: lt => Ensembles.Add _ (listSet lt) a
  end.

(** #######################
The archvar that is passed to Function has to be the one with a dummy stack provided. The Arch module type should construct out of it's register and stack parameters a full archvar and a dummy archvar
 *)

Fixpoint fblock (l : list type) :=
  forall (v : varT),
  (fix fbt (l : list type) :=
    match l with
    | []      => block v
    | t :: lt => v t -> fbt lt
    end) l.

Record Function (archvar : varT) := func
                    {
                      name     : string;

                      (** The variable type on which the function body is parametrized *)
                      param    : list type;

                      (** The ordered list of parameters of the function *)
                      local    : list type;

                      (** Allocation onto _archvar_ from the local variables *)

                      localloc : {l : list (sigT archvar) | map (@projT1 _ archvar) l = local};
                      
                      (* -----------------------
                      Tactics needed for this proof obligation
                      *)

                      loopvar  : {i | i < length local};

                      setup    : fblock (param ++ local);
                      loop     : fblock (param ++ local);
                      cleanup  : fblock (param ++ local);
                    }.

Definition makeb {l : list type} (fb : fblock l) {v : varT} (alloc : {lv : list (sigT v) | map (@projT1 _ v) lv = l}) : block v.

(* ########################
I am trying to write this yet.
*)