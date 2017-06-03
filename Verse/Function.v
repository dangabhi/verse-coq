Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
Require Import Basics.
Require Import Setoid.

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
                              param    : list (sigT v);
                              local    : list (sigT v);

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
Defined.

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
Definition beta_loop v l t (lp ll : list (sigT v)) : lamT v l (Function v t) -> lamT v ([t] ++ l) (FB v t).
  intros.
  unfold lamT. simpl. fold lamT.
  induction l.
  simpl. simpl in X. 
  exact (fun x => fb _ lp ll (setup X) x (loop X x) (cleanup X)).
  simpl. simpl in X.
  exact (fun x y => IHl (X y) x).
Qed.

Definition lamF {v} {l} {T T'} (fl : lamT v l (T -> T')) (f : lamT v l T) : lamT v l T'.
  induction l.
  exact (fl f).
  unfold lamT; simpl; fold lamT.
  unfold lamT in fl, f. simpl in fl, f. fold lamT in fl, f.
  intros.
  exact (IHl (fl X) (f X)).
Qed.

(* Might be possible to write this in function mode *)
Definition make_list v l1 l2 l3 : lamT v (l1 ++ l2 ++ l3) (list (sigT v)).
induction l1.  
induction l2.
induction l3.
exact ([]).
exact (fun _ => IHl3).
exact (fun x => (lamFT (cons (existT _ _ x)) IHl2)).
exact (fun _ => IHl1).
Defined.

Definition add_plist {v} {l1 l2 l3} {t} (f : lamT v (l1 ++ l2 ++ l3) (FB v t)) : lamT v (l1 ++ l2 ++ l3) (FB v t) :=
  lamF (lamFT (fun l f => fb t (param f ++ l) (local f) (pre f) (lv f) (rep f) (post f)) (make_list v l1 l2 l3)) f.
  
Definition add_llist {v} {l1 l2 l3} {t} (f : lamT v (l1 ++ l2 ++ l3) (FB v t)) : lamT v (l1 ++ l2 ++ l3) (FB v t) :=
  lamF (lamFT (fun l f => fb t (param f) (local f ++ l) (pre f) (lv f) (rep f) (post f)) (make_list v l1 l2 l3)) f.

(* 
Breaks up the lamT parametrizing a Function into two lamT's which would be
instantiated by callConv and lalloc respectively.
This is with the assumption that the loopvar is allocated on the stack by the callConv.
*)

Definition tr {p lv lr} t (f : function p lv lr t) : forall v, lamT v (p ++ lv ++ [t]) (lamT v lr (FB v t)).
  intros.
  unfold function in f.
  rewrite app_assoc in f.
  assert (f1 := f v).
  rewrite lamT_app in f1.
  assert (f2 := lamFT (beta_loop lr t [] []) f1).
  rewrite <- lamT_app in f2.
  rewrite <- app_assoc in f2.
  assert (f3 := @add_plist _ [] p _ _ f2).
  assert (f4 := @add_llist _ p lv _ _ f3).
  assert (f4': lamT v ((p ++ lv ++ [t]) ++ lr ++ []) (FB v t)).
  rewrite app_nil_r. rewrite <- ?app_assoc. exact f4.
  assert (f5 :=@add_llist _ (p ++ lv ++ [t]) lr [] _ f4').
  rewrite app_nil_r in f5.
  rewrite lamT_app in f5. exact f5.
Qed.

(*
Does the same as above but with the assumption that loopvar is allocated on a register
and by the user.
*)


Definition tr' {p lv lr} t (f : function p lv lr t) : forall v, lamT v (p ++ lv) (lamT v (t :: lr) (FB v t)).
  intros.
  unfold function in f.
  rewrite app_assoc in f.
  assert (f1 := f v).
  rewrite lamT_app in f1.
  assert (f2 := lamFT (beta_loop lr t [] []) f1).
  rewrite <- lamT_app in f2.
  rewrite <- app_assoc in f2.
  assert (f3 := @add_plist _ [] p _ _ f2).
  assert (f4 := @add_llist _ p lv _ _ f3).
  assert (f4': lamT v ((p ++ lv ++ [t]) ++ lr ++ []) (FB v t)).
  rewrite app_nil_r. rewrite <- ?app_assoc. exact f4.
  assert (f5 := @add_llist _ _ lr [] _ f4').
  rewrite <- ?app_assoc in f5.
  rewrite app_assoc in f5.
  rewrite lamT_app in f5. rewrite app_nil_r in f5. exact f5.
Qed.

