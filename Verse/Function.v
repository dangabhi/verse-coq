Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import Arch.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
Require Import Basics.

Set Implicit Arguments.

Fixpoint listSet {A : Type} (l : list A) : Ensemble A :=
  match l with
  | [] => Empty_set _
  | a :: lt => Ensembles.Add _ (listSet lt) a
  end.

Fixpoint fbv (v : varT) (l : list type) :=
  match l with
  | [] => block v
  | t :: lt => v t -> fbv v lt
  end.

Definition fblock (l : list type) :=
  forall (v : varT), fbv v l.

(** #######################
The archvar that is passed to Function has to be the one with a dummy stack provided. The Arch module type should construct out of it's register and stack parameters a full archvar and a dummy archvar
 *)

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

Lemma makebv {l : list type} {v : varT} (fb : fbv v l)  (alloc : {lv : list (sigT v) | map (@projT1 _ v) lv = l}) : block v.
  induction l.
  exact fb.
  unfold fbv in fb.
  destruct alloc.
  induction x; simpl in e.
  apply nil_cons in e. contradiction.
  injection e; intros.
  destruct a0.
  simpl in H0.
  assert (v0is : v a).
  subst a. exact v0.
  pose (fbn := fb v0is).
  fold fbv in fbn.
  exact (IHl fbn (exist _ x H)).
Qed.

Definition makeb {l : list type} (fb : fblock l) {v : varT} (alloc : {lv : list (sigT v) | map (@projT1 _ v) lv = l}) : block v.
exact (makebv (fb v) alloc).
Qed.