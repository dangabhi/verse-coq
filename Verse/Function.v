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
                              loopvar  : sigT v;

                              fn       : Function v t;
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

Definition lamF {v} {l} {T T'} (fl : lamT v l (T -> T')) (f : lamT v l T) : lamT v l T'.
  induction l.
  exact (fl f).
  unfold lamT; simpl; fold lamT.
  unfold lamT in fl, f. simpl in fl, f. fold lamT in fl, f.
  intros.
  exact (IHl (fl X) (f X)).
Qed.

Parameter get_lv : forall v l1 t l2, lamT v (l1 ++ [t] ++ l2) (sigT v).
Parameter add_dummy : forall v l1 t l2 T, lamT v (l1 ++ l2) T -> lamT v (l1 ++ [t] ++ l2) T.

(* Constructs a parametrized FB from a parametrized Function *)
Definition internalize {p lv lr} t (f : function p lv lr t) : forall v, lamT v (p ++ lv ++ [t] ++ lr) (FB v t).
  unfold function in f.
  intros.
  assert (ll := make_list v p (lv ++ [t] ++ lr) []).
  assert (lp := make_list v [] p (lv ++ [t] ++ lr)).
  assert (loopvar := get_lv v (p ++ lv) t lr).
  simpl in ll, lp, loopvar. rewrite app_nil_r in ll. rewrite <- app_assoc in loopvar.
  rewrite app_assoc in f.
  assert (ft := add_dummy _ (p ++ lv) t lr _ (f v)). rewrite <- app_assoc in ft.
  exact (lamF (lamF (lamF (lamFT (@fb v t) ll) lp) loopvar) ft).

