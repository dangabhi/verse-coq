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

Section Function.
  (* Function record parametrized by the varT and type of the loopvar *)
  Variable v : varT.
  Record Function t    := func
                            {
                              setup    : block v;
                              loop     : v t -> block v;
                              cleanup  : block v;
                            }.

  (* Internal type which does not hide the loopvar from other blocks *)
  Record FB t := fb
                   {
                     param    : list (sigT v);
                     local    : list (sigT v);
                     loopvar  : sigT v;

                     fn       : Function t;
                   }.

  (* v l1 -> v l2 -> ... -> T *)
  Fixpoint lamT (l : list type) (T : Type) : Type :=
    match l with
    | [] => T
    | ty :: lt => v ty -> lamT lt T
    end.

  (* Instantiation of a lamT *)
  Definition betaT l := forall T, lamT l T -> T.

  (* A list-like constructor for betaT *)
  Lemma beta_app t (vt : v t) (l : list type) (b : betaT l) : betaT (t :: l).
    unfold betaT. unfold lamT. fold lamT.
    exact (fun T f => b T (f vt)).
  Qed.

  (* lamT 'commutes' with ++ *)
  Lemma lamT_app : forall {l1 l2} {T}, lamT (l1 ++ l2) T = lamT l1 (lamT l2 T).
  Proof.
    intros.
    induction l1.
    trivial.
    unfold lamT. simpl. fold lamT.
    rewrite IHl1.
    trivial.
  Qed.
  (* lamT is functorial on T *)
  Definition lamFT {T T'} (f : T -> T') l : (lamT l T) -> (lamT l T').
    induction l.
    eauto.
    unfold lamT. simpl. fold lamT.
    intros. exact (IHl (X X0)).
  Defined.

  Arguments lamFT {T T'} _ {l} _.

  (* Might be possible to write this in function mode *)
  Definition make_list l1 l2 l3 : lamT (l1 ++ l2 ++ l3) (list (sigT v)).
    induction l1.  
    induction l2.
    induction l3.
    exact ([]).
    exact (fun _ => IHl3).
    exact (fun x => (lamFT (cons (existT _ _ x)) IHl2)).
    exact (fun _ => IHl1).
  Defined.

  Definition lamF {l} {T T'} (fl : lamT l (T -> T')) (f : lamT l T) : lamT l T'.
    induction l.
    exact (fl f).
    unfold lamT; simpl; fold lamT.
    unfold lamT in fl, f. simpl in fl, f. fold lamT in fl, f.
    intros.
    exact (IHl (fl X) (f X)).
  Qed.

  Definition get_lv l1 t l2 : lamT (l1 ++ [t] ++ l2) (sigT v).
    induction l1.
    induction l2.
    exact (fun x => existT _ _ x).
    exact (fun x y => IHl2 x).
    exact (fun _ => IHl1).
  Qed.

  Definition add_dummy : forall l1 t l2 T, lamT (l1 ++ l2) T -> lamT (l1 ++ [t] ++ l2) T.
    intros.
    induction l1.
    exact (fun _ => X).
    simpl.
    exact (fun x => IHl1 (X x)).
  Qed.
  
End Function.

(* The user-defined function using the lamT to provide variables *)
Definition function (p lv lr : list type) t :=
  forall (v : varT), lamT v (p ++ lv ++ lr) (Function v t).

(* lamT is contravariantly functorial on v *)
Lemma lam_cv {v w} {l} {T} (f : subT w v) : lamT v l T -> lamT w l T.
Proof.
  induction l.
  trivial.
  unfold lamT. simpl. fold lamT.
  intros.
  exact (IHl (X (f _ X0))).
Qed.

Arguments lamFT {v T T'} _ {l} _.
Arguments lamF {v l T T'} _ _.

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
Defined.
