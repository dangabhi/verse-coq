Set Implicit Arguments.

(** * Representing Erros.

    We use the sumor type to represent constructs in the verse
language that might be erroneous. This module developes the monadic
notation for it for ease of use in the rest of the program.

*)


Global Notation "{- A -}" := (inleft A).
Global Notation "'error' A" := (inright A) (at level 40).

Definition noErr T E (x : T + {E}) : Prop := exists t : T, x = inleft t.

Definition isErr T E (x : T + {E}) : { noErr x } + { ~ noErr x }.
  refine (match x as y return x = y -> {noErr x} + {~ noErr x} with
         | {- t -} => fun p => left (ex_intro _ t p)
         | error e => fun p => right _
          end eq_refl).
  destruct 1 as [y H]. rewrite p in H. discriminate H.
Defined.

Definition getT T E (x : T + {E}) (p : noErr x) : T.
  refine (match x as y return noErr y -> T with
         | inleft t  => fun _ => t
         | inright e => _
          end p).
  unfold noErr.
  intro H; contradict H;
  destruct 1; discriminate.
Defined.

Section Error.
  Variable A   : Type.
  Variable Err : Prop.

  Section Apply.
    Variable B   :  Type.
    Definition ap (f : A -> B) (y : A + {Err}) :=
      match y with
      | {- a -}    => {- f a -}
      | inright err  => inright err
      end.

    Definition apA (f : (A -> B) + {Err})(x : A + {Err}) :  B + {Err} :=
      match f, x with
      | {- f -} , {- x -}  => {- f x -}
      | inright e, _         => inright e
      | _        , inright e => inright e
      end.

    Definition bind (x : A + {Err})(f : A -> B + {Err}) : B + {Err} :=
      match x with
      | {- a -} => f a
      | inright e => inright e
      end.

  End Apply.
  Definition recover (x : A + {Err}) : if x then A else Err
    := match x with
       | {- a -} => a
       | inright b => b
       end.

End Error.

Section Conditionals.

  (** Some type *)
  Variable A : Type.

  (** A decidable predicate on A *)
  Variable P : A -> Prop.

  (** The decision procedure for P *)
  Variable decP : forall a : A, {P a} + {~ P a}.

  (** Emit the value only whe the predicate is satisfied
   *)
  Definition when (a : A) : A + {~ P a} :=
    match decP a with
    | left _  => {- a -}
    | right err => error err
    end.

  (** Emit the value unless the predicate is true. *)
  Definition unless (a : A ) : A + {P a} :=
    match decP a with
    | left err => error err
    | right _ => {- a -}
    end.

End Conditionals.

Arguments when [A P] _ _.
Arguments unless [A P] _ _.
Arguments ap [A Err B] _ _.
Arguments apA [A Err B] _ _.
Arguments recover [A Err] _.
Arguments bind [A Err B] _ _.
(* Haskell like applicative notation for errors *)
Global Notation "F <$> A" := (ap  F A) (at level 40, left associativity).
Global Notation "F <*> A" := (apA F A) (at level 40, left associativity).
Global Notation "X <- A ; B" := (bind A (fun X => B))(at level 81, right associativity, only parsing).

Section Merge.
  Require Import Vector.
  Import VectorNotations.

  Variable A : Type.
  Variable Err : Prop.

  Fixpoint mergeVector {n} (verr : Vector.t (A + {Err}) n) : Vector.t A n + {Err} :=
  match verr with
  | []                            => {- [] -}
  | inright err :: _              => inright err
  | Vector.cons _ {- x -} m xs => Vector.cons _ x m  <$> (@mergeVector m xs)
  end.

  Require Import List.
  Import ListNotations.
  Fixpoint merge (actions : list (A + {Err})) : list A + {Err} :=
    match actions with
    | nil => {- nil -}
    | error err :: _ => inright err
    | cons {- x -} xs  => cons x <$> merge xs
    end.
End Merge.
