Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
Require Import Basics.

Set Implicit Arguments.

(* Function record parametrized by the varT and type of the loopvar *)
Record Function (v : varT) t    := func
                                {
                                  setup    : block v;
                                  loop     : v t -> block v;
                                  cleanup  : block v;
                                }.

(* Internal type which does not hide the loopvar from other blocks *)
Record FB (v : varT) t := fb
                                {
                                  pre    : block v;
                                  lv     : v t;
                                  rep    : block v;
                                  post   : block v;
                                }.

(* v l1 -> v l2 -> ... -> T *)
Fixpoint lamT (v : varT) (l : list type) (T : Type) : Type :=
  match l with
  | [] => T
  | ty :: lt => v ty -> lamT v lt T
  end.

(* Instantiation of a lamT *)
Definition betaT v l := forall T, lamT v l T -> T.

(* The user-defined function using the lamT to provide variables *)
Definition function (p lv lr : list type) t :=
  forall (v : varT), lamT v (p ++ lv ++ lr) (Function v t).

(* A list-like constructor for betaT *)
Lemma beta_app v t (vt : v t) (l : list type) (b : betaT v l) : betaT v (t :: l).
unfold betaT. unfold lamT. fold lamT.
exact (fun T f => b T (f vt)).
Qed.

(* lamT 'commutes' with ++ *)
Lemma lamT_app : forall {v} {l1 l2} {T}, lamT v (l1 ++ l2) T = lamT v l1 (lamT v l2 T).
Proof.
  intros.
  induction l1.
  trivial.
  unfold lamT. simpl. fold lamT.
  rewrite IHl1.
  trivial.
Qed.

(* lamT is functorial on T *)
Definition lamFT {T T'} (f : T -> T') {v l} : (lamT v l T) -> (lamT v l T').
  induction l.
  eauto.
  unfold lamT. simpl. fold lamT.
  intros. exact (IHl (X X0)).
Qed.

(* lamT is contravariantly functorial on v *)
Lemma lam_cv {v w} {l} {T} (f : subT w v) : lamT v l T -> lamT w l T.
Proof.
  induction l.
  trivial.
  unfold lamT. simpl. fold lamT.
  intros.
  exact (IHl (X (f _ X0))).
Qed.

(* Constructs a parametrized FB from a parametrized Function *)
Definition beta_loop v l t : lamT v l (Function v t) -> lamT v ([t] ++ l) (FB v t).
  intros.
  unfold lamT. simpl. fold lamT.
  induction l.
  simpl. simpl in X. 
  exact (fun x => fb _ (setup X) x (loop X x) (cleanup X)).
  simpl. simpl in X.
  exact (fun x y => IHl (X y) x).
Qed.

(* 
Breaks up the lamT parametrizing a Function into two lamT's which would be
instantiated by callConv and lalloc respectively.
This is with the assumption that the loopvar is allocated on the stack by the callConv.
 *)

Definition tr {p lv lr} t (f : function p lv lr t) : forall v, lamT v (p ++ lv ++ [t]) (lamT v lr (FB v t)).
  intros.
  unfold function in f.
  rewrite app_assoc in f.
  assert (f' := f v).
  rewrite lamT_app in f'.
  assert (f'':= lamFT (beta_loop v lr t) f').
  rewrite <- lamT_app in f''.
  rewrite app_assoc in f''.
  rewrite lamT_app in f''.
  rewrite app_assoc.
  exact f''.
Qed.

(*
Does the same as above but with the assumption that loopvar is allocated on a register
and by the user.
*)

Definition tr' {p lv lr} t (f : function p lv lr t) : forall v, lamT v (p ++ lv) (lamT v (t :: lr) (FB v t)).
  intros.
  unfold function in f.
  rewrite app_assoc in f.
  assert (f' := f v).
  rewrite lamT_app in f'.
  exact (lamFT (beta_loop v lr t) f').
Qed.

