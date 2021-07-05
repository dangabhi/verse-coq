Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.AnnotatedCode.
Require Import Verse.AbstractMachine.
Require Import Verse.Scope.
Require Import Verse.ScopeStore.

Require Import List.
Import ListNotations.

Require Import Vector.
Import VectorNotations.

Fixpoint distinctL [T] (l : list T)
  := let fix distH t l :=
         match l with
         | []%list         => True
         | (hd :: tl)%list => t <> hd /\ hd <> t /\ distH t tl
         end
     in
     match l with
     | []%list         => True
     | (hd :: tl)%list => distH hd tl /\ distinctL tl
     end.

Definition qualV [ts] (v : Variables.U ts) := sigT (qualified v).

Definition qualify [ts] [v : Variables.U ts] [k ty] (x : v k ty)
  : qualV v
  := existT _ (existT _ _ ty) x.

Definition distinct ts n (sc : Scope.type ts n)
         (v : Variables.U ts)
         (a : allocation v sc)
  : Prop
  := distinctL
       ((fix alltolist [ts n] [sc : Scope.type ts n]
             [v : Variables.U ts]
             (a : allocation v sc) :=
           match n as n0 return forall (sc0 : Scope.type ts n0),
               allocation _ sc0 -> list _ with
           | 0   => fun _ _    => []
           | S n => fun scn an => (qualify (fst an))
                                    ::
                                    (alltolist (snd an))
           end sc a)%list ts n sc v a).

Require Fin.
Module Prodn.

  Fixpoint t T n : Type
    := match n with
       | 0   => Datatypes.unit
       | S n => (T * t T n)%type
       end.

  Fixpoint nth [T n] (p : t T n) (m : Fin.t n) : T
    := match m in Fin.t n0
             return t _ n0 -> _
       with
       | Fin.F1    => fun p1 => fst p1
       | Fin.FS mS => fun pS => nth (snd pS) mS
       end p.

  Fixpoint vecToProdn [T n] (v : Vector.t T n) : t T n
    := match v in Vector.t _ n0 return t _ n0 with
       | [] => tt
       | hd :: tl => (hd, vecToProdn tl)
       end.

  Fixpoint prodnToVec [T n] : t T n -> Vector.t T n
    := match n as n0 return t T n0 -> Vector.t T n0 with
       | 0   => fun _ => []
       | S m => fun p => (fst p) :: (prodnToVec (snd p))
       end.

  Lemma prodnToVec_vecToProdn [T n] (p : t T n)
    : vecToProdn (prodnToVec p) = p.
  Proof.
    induction n.
    * now destruct p.
    * destruct p.
      simpl.
      now rewrite (IHn t1).
  Defined.

  Lemma vecNth_prodnNth [T n] m (p : t T n)
    : Vector.nth (prodnToVec p) m = nth p m.
    induction m.
    * easy.
    * apply IHm.
  Defined.

End Prodn.

Module HProdn.

  Fixpoint t [T n] (u : T -> Type)
  : Vector.t T n -> Type
    := match n as n0 return Vector.t _ n0 -> Type with
       | 0   => fun _  => unit
       | S m => fun v0 => (u (Vector.hd v0) * t u (Vector.tl v0))%type
       end.

  Fixpoint nth [T n] [u : T -> Type]
           [sc : Vector.t T n] (hp : t u sc) (m : Fin.t n) : sigT u
    := match m as m0 in Fin.t n0
             return forall v0 : Vector.t _ n0, @t _ n0 u v0 -> _
       with
       | Fin.F1    => fun _ p1 => existT _ _ (fst p1)
       | Fin.FS mS => fun _ pS => nth (snd pS) mS
       end _ hp.

  Lemma nth_type [T n] [u : T -> Type]
        [sc : Vector.t T n] (hp : t u sc) (m : Fin.t n)
    : projT1 (nth hp m) = Vector.nth sc m.
    induction m.
    revert hp.
    eapply (caseS' sc).
    easy.

    simpl.
    revert hp.
    eapply (caseS' sc).
    intros.
    apply IHm.
  Defined.

End HProdn.

Import EqNotations.

Section Meta.

  Axiom onlyProj : forall (A B : Type) (f : forall T, B*T*T -> A),
    exists g : B -> A, forall B p, f B p = g (fst p).

  Axiom onlyMemVec : forall (n : nat) (f : forall T, Vector.t T (S n) -> T),
    exists m, forall T v, f T v = Vector.nth v m.

  Lemma onlyMemProdn : forall (n : nat)
                              (f : forall T, Prodn.t T (S n) -> T),
      exists m, forall T p, f T p = Prodn.nth p m.
  Proof.
    intros.
    pose (onlyMemVec _ (fun _ v => f _ (Prodn.vecToProdn v))).
    destruct e.
    exists x.
    intros.
    pose (H _ (Prodn.prodnToVec p)).
    rewrite Prodn.prodnToVec_vecToProdn in e.
    now rewrite Prodn.vecNth_prodnNth in e.
  Qed.

  Lemma onlyMemHProdn : forall (n : nat) T
                               (sc : Vector.t T n)
                               m (f : forall u, HProdn.t u sc -> u (Vector.nth sc m)),
      exists m', forall u hp, f u hp = rew [ u ] (HProdn.nth_type _ m)
          in projT2 (HProdn.nth hp m).
  Proof.
    intros.

  Qed.

  Variable ts : typeSystem.

  Definition uncurryToVec [C] {n} {sc : Scope.type ts n}
             (scC : forall v, scoped v sc C)
    : (forall v : Variables.U ts, Vector.t (qualV v) n -> C).
    fun v =>


  Lemma onlyScoped n (sc : Scope.type ts n)
        forall v, scoped v sc

End Meta.

Section Translate.

  Variable ts : typeSystem.

  Variable tyD : typeDenote verse_type_system.
  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel tyD ty -> Prop
  .

  Variable n  : nat.
  Variable sc : Scope.type verse_type_system n.

  Lemma scopeSemanticsTranslates :
    forall (C : forall v, scoped v sc (AnnotatedCode tyD Rels v)),
    forall (v : Variables.U verse_type_system)
           (va : allocation v sc),

      Prop.

End Translate.
