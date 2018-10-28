Require Import Verse.Language.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.
Require Import Verse.Word.

Require Import Bvector.
Require Import Vector.

Set Implicit Arguments.

Generalizable All Variables.

Module Semantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module C  := ConstDenote W CW.
  Module OP := OpDenote W O.

  Import OP.

  Section Store.
    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    Let v := scopeVar vT.

    (* Data structure to encode the variable values for the structured
       ProxyVar variable type
    *)
    Definition store := allocation (fun _ => typeDenote) vT.
    (* Omitting the implicit typeClass for `typeDenote` triggers a bug *)

  End Store.

  Arguments store [n] vT.

  (* Getting a variable value out of the store *)
  Fixpoint eval (tyd : VariableT)
                `{vT : Vector.t (some type) n} (s : allocation tyd vT)
                `{ty : type k} (x : scopeVar vT ty)
    : (tyd _ ty : Type) :=
    match x in scopeVar vT0 ty0 return (allocation tyd vT0)
                                       -> (tyd _ ty0 : Type) with
    | headVar    => fun s0 => let '(vx, _) := s0 in vx
    | restVar rx => fun s0 => let '(_, st) := s0 in eval _ st rx
    end s.

  Arguments eval [tyd n vT] _ [k ty] _.

  Fixpoint storeUpdate (tyd : VariableT)
                       `(vT : Vector.t (some type) n)
                       `{ty : type k} (var : scopeVar vT ty)
    : ((tyd _ ty : Type) -> (tyd _ ty : Type)) ->
      allocation tyd vT -> allocation tyd vT :=
    match var as var0 in scopeVar vT0 ty0 return
          ((tyd _ ty0 : Type)
           -> tyd _ ty0 : Type)
          -> allocation tyd vT0 -> allocation tyd vT0
    with
    | headVar    => fun f s => let '(vx, st) := s in (f vx, st)
    | restVar rx => fun f s => let '(vx, st) := s in (vx, storeUpdate _ rx f st)
    end.

  Arguments storeUpdate [tyd n vT k ty] _ _ _.

  Section InstructionDenote.

    Variable n  : nat.
    Variable vT : Vector.t (some type) n.

    (* Extracts from the store the value denoted by an arg *)

    Definition argDenote (S : store vT)
                         `{ty : type k} `(a : arg (scopeVar vT) aK ty)
      : typeDenote ty : Type := 
      match a in (arg _ _ ty) return typeDenote ty with
      | var av               => eval S av
      | Language.Ast.const c => C.constDenote c
      | index x i            => (fun y => nth_order y (proj2_sig i)) (eval S x)
      end.

    (* Auxiliary function to lift an arg value change to store *)
    Definition largUpdate `{ty : type k} (a : larg (scopeVar vT) ty)
                          (val : typeDenote ty : Type)
                          (S : store vT)
      : store vT :=
      match a in arg _ lval ty  return (typeDenote ty : Type)
                                       -> store vT
      with
      | @var _ lval _ _ av        => fun val' => storeUpdate av
                                                             (fun _ => val')
                                                             S
      | @index _ lval  _ _ _ x i => fun val' => storeUpdate x
                                                         (fun vec =>
                                                            replace_order vec (proj2_sig i) val')
                                                         S
      end val.

    (* The constant 1 as a verse constant to provide an interpretation
       for the increment/decrement instructions
    *)
    Let one (ty : type direct) : constant ty :=
      match ty as ty' in type direct return constant ty' with
      | word n        => bits (Ndigits.N2Bv_gen _ 1)
      | multiword _ _ => const (bits (Ndigits.N2Bv_gen _ 1)) _
      end
    .

    Fixpoint  instructionDenote (i : instruction (scopeVar vT)) (S : store vT) {struct i}
      : (store vT) :=
      let updatePair `{ty : type k} (a1 a2 : larg (scopeVar vT) ty) val :=
          let S' := largUpdate a1 (fst val) S in largUpdate a2 (snd val) S' in
      match i with
      | increment la => largUpdate la (OP.opDenote _ plus
                                                 (argDenote S la)
                                                 (argDenote S (Ast.const (one _))))
                                 S
      | decrement la => largUpdate la (OP.opDenote _ minus
                                                 (argDenote S la)
                                                 (argDenote S (Ast.const (one _))))
                                 S
      | assign ass => match ass with
                      | extassign4 op la1 la2 ra1 ra2 ra3 =>
                        updatePair la1 la2 (OP.opDenote _ op
                                                          (argDenote S ra1)
                                                          (argDenote S ra2)
                                                          (argDenote S ra3))
                      | extassign3 op la1 la2 ra1 ra2     =>
                        updatePair la1 la2 (OP.opDenote _ op
                                                          (argDenote S ra1)
                                                          (argDenote S ra2))
                      | assign3 op la ra1 ra2 => largUpdate la (OP.opDenote _ op
                                                                          (argDenote S ra1)
                                                                          (argDenote S ra2))
                                                          S
                      | assign2 op la ra1     => largUpdate la (OP.opDenote _ op
                                                                          (argDenote S ra1))
                                                          S
                      | update2 op la ra1     => largUpdate la (OP.opDenote _ op
                                                                          (argDenote S la)
                                                                          (argDenote S ra1))
                                                          S
                      | update1 op la         => largUpdate la (OP.opDenote _ op
                                                                          (argDenote S la))
                                                          S
                      end
      | moveTo x ix ra => largUpdate (index x ix) (@argDenote S _ _ rval (var ra))
                                     S
      | clobber ra     => S
      end.

  End InstructionDenote.

  Section Annotate.

    (** The specification at any given program point carries
        along the assumptions made so far and the accumulated
        claims

        The specification at the end of the sequence:
                     ...
                     ASSUME A1
                     ...
                     CLAIM C1
                     ...
                     ASSUME A2
                     ...
                     CLAIM C2

        would be the pair -

                 (A1 /\ A2, (A1 -> C1) /\ (A1 /\ A2 -> C2))

        with the annotations being instantiated with the stores
        at the corresponding program points.
     *)
    
    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    Definition storeE := allocation (fun _ ty => @typeDenote TypeDenote _ _ ty + {contextErr}) vT.
    Definition spec := (Prop * Prop * storeE)%type.

    Variable st : store vT.

    Set Printing Implicit.
    Definition annotationDenote (a : annotation (scopeVar vT)) (s : spec) : spec :=
      let (ann, oldst) := s in
      let (ass, cl) := ann in
      let ctxtP := (@eval _ _ _ st, @eval _ _ _ oldst) in
      match a with
      | remember x => (ann, storeUpdate x (fun _ => {- eval st x -}) oldst)
      | assert a   => (fun na => ((ass /\ na, cl), oldst)) (a ctxtP)
      | claim  c   => (fun nc : Prop => ((ass /\ nc, cl /\ (ass -> nc)), oldst)) (c ctxtP)
      end.

  End Annotate.

End Semantics.

Module CodeSemantics (W : WORD_SEMANTICS) (CW : CONST_SEMANTICS W) (O : OP_SEMANTICS W).

  Module S := Semantics W CW O.
  Import S.

  Section CodeDenote.

    Variable n : nat.
    Variable vT : Vector.t (some type) n.

    (* The Type capturing the program state *)
    Definition state := (store vT * spec vT)%type.

    Definition clDenote (cl : codeline (scopeVar vT)) (s : state) : state :=
      let (st, sp) := s in
      match cl with
      | annot a => (fun na => (st, na)) (annotationDenote st a sp)
      | inst  i => (fun ni => (ni, sp)) (instructionDenote i st)
      end.

    Functional Scheme clDenote_ind := Induction for clDenote Sort Type.

    Definition codeDenote c s : state := List.fold_left
                                           (fun s i => (clDenote i) s)
                                           c
                                           s.
      
    Definition codeCheck c init : Prop :=
      let fix mkInvalid {n} (v : Vector.t (some type) n) {struct v} : storeE v :=
          match v as v' return storeE v' with
          | []      => tt
          | _ :: vt => (error Invalid, mkInvalid vt)
          end in
      let invst := mkInvalid vT in
      (fun x => snd (fst (snd x))) (List.fold_left
                                      (fun s i => (clDenote i) s)
                                      c
                                      (init, ((True, True), invst))).

    Definition SAT c    := forall init, codeCheck c init.
    Definition genSAT c := SAT (@fillDummy (@code _) _ vT c).

  End CodeDenote.

  Arguments codeDenote [n vT] _ _.

  Ltac mapTyOf xt :=
    match xt with
    | _ ?y -> ?z => refine ((existT _ _ y) :: _); mapTyOf z
    | _          => exact []
    end.

  (* Extract the scope out of a generic function *)
  Ltac getScope x := let xt := type of (x ProxyVar) in mapTyOf xt.

  Let addErr (Err : Prop) v1 `(vT : Vector.t (some type) n)
           (a : allocation v1 vT) :=
  mapAlloc v1 _ (fun _ _ => @inleft _ Err) _ a.

  (* Recovers the specification corresponding to a code block
     as a Prop *)

  Ltac extractSAT func :=
    let sc := fresh "sc" in
    simple refine (let sc : Vector.t (some type) _ := _ in _);
    [shelve | getScope func | idtac];
    exact (genSAT sc func).

  Ltac breakStore :=
    repeat
      match goal with
      | a : _ * _ |- _ => simpl in a; destruct a
      | |- forall _ : _, _ => intro; simpl in * |-
      end.
      
  (* A starter to preface a proof attempt on a Prop extracted via
     extractSAT *)
  Ltac simplify :=
    repeat
      (match goal with
      | |- ?p              => unfold p
      | a : _ * _ |- _     => simpl in a; destruct a
      | |- forall _ : _, _ => intro
      | |- exists _ : _, _ => eapply ex_intro
      | |- _ /\ _          => constructor
      | |- _ = _           => constructor 
      | _                  => simpl in *
      end; repeat autounfold).

End CodeSemantics.

Module StandardSemantics := CodeSemantics StandardWord StandardConsts StandardWordOps.