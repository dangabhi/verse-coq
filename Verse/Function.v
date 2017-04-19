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

Record Function (archvar : varT) := func
                    {
                      name     : string;

                      (** The variable type on which the function body is parametrized *)
                      fvar     : type -> Type;

                      (** The ordered list of parameters of the function *)
                      param    : list {ty : type & fvar ty};

                      (** Allocation onto _archvar_ from the local variables *)
                      localloc : list {fv : {ty : type & fvar ty} & (archvar (projT1 fv))};

                      loopvar  : {ty : type & fvar ty};

                      setup    : block fvar;
                      loop     : block fvar;
                      cleanup  : block fvar
                    }.

(** #####################
These things could actually stay right here *)

Definition local {v : varT} (f : Function v) := map (@projT1 {ty : type & fvar f ty} _) (localloc f).

Definition usedvars {v : varT} (f : Function v) := Ensembles.Add _
                                                                                                                              (Union _
                                                                                                                                     (Union _ (bvars (setup f)) (bvars (loop f)))
                                                                                                                                     (bvars (cleanup f)))
                                                                                                                              (loopvar f).

(* #######################
Can be changed to use listSet and a disjoint union prop from the Ensemble library in case tactics get hard
*)

Definition allUsedListed := forall (v : varT) (f : Function v) (x : (sigT (fvar f))), Ensembles.In _ (usedvars f) x ->
                                                  or (In x (param f)) (In x (local f)).

(* -----------------------
Tactics needed for this proof obligation that callconv will generate
*)
