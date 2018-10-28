Require Import Verse.
Require Import Verse.CryptoLib.sha2.

Import NArith.
Import Nat.
Require Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Set Implicit Arguments.

(** * SHA2 hashing algorithm.

We can now give a common iterator for both the sha512 and sha256
algorithm. It is implemented as a module parameterised over the
configuration module.

 *)

Section SIGMA.

  Variable w : nat.
  Variable r0 r1 r2 : nat.

  Section Code.
    
    Variable v : VariableT.

    Definition SIGMA' (x t M : v (word w)) :=
      [ REMEMBER x; REMEMBER M;
          t ::=  x >*> (r2 - r1); t ::=^ x;
          t ::=>*>     (r1 - r0); t ::=^ x;
          t ::=>*>     r0       ;
          CLAIM x HAD x' ; t HAS t' IN
                t' = (XorW (XorW (RotR r0 x') (RotR r1 x')) (RotR r2 x'));
          M ::=+ t;
          CLAIM x HAD x' ; M HAD m ; M HAS m' IN
                m' = numBinOp N.add m (XorW (XorW (RotR r0 x') (RotR r1 x')) (RotR r2 x'))             ].
    
  End Code.

  Import StandardSemantics.
  
  Definition toProve : Prop.
    extractSAT SIGMA'.
  Defined.

  Definition proof : toProve.
    time (
        unfold toProve;
        unfold genSAT;
        unfold SAT;
        unfold codeCheck;
        breakStore;
        lazy -[RotR ShiftR XorW AndW OrW NegW numBinOp N.add sub add pow];
        repeat econstructor).
  Abort.
    
End SIGMA.
Arguments SIGMA' _ _ _ _ [v] _ _ _.

Notation "V <+> W" := (numBinOp N.add V W)
                        (at level 50).

Module STEP (C : CONFIG).

  Import C.
  Section STEP.

    Definition Word := word WordSize.

    Variable r : nat.
    Variable rBoundPf : r < ROUNDS.

    Section Code.

      Variable v : VariableT.

      Variable M : v Word.

      Variable A B C D E F G H : v Word.
      Variable t tp temp : v Word.

      Definition K : constant Word :=  Vector.nth_order KVec rBoundPf.

      Definition STEP : code v :=
        let sigma r0 r1 s x :=
            [ t ::= x >*> (r1 - r0); t    ::=^ x;
              t ::=>*>    r0       ; tp   ::=  x >> s;
              t ::=^ tp            ; temp ::=+ t
            ]%list in
        let sigma0 := sigma r00 r01 s0 A in
        let sigma1 := sigma r10 r11 s1 E in
        let CH :=
            [ tp ::=~ E;
              tp ::=& G;
              t ::= E [&] F; t ::=^ tp; temp ::=+ t] in
        let MAJ :=
            [ t  ::=  B [|] C;
              t  ::=& A;
              tp ::=  B [&] C;
              t  ::=| tp
            ] in
        
          REMEMBER (H, M, A, B, C, D, E, F, G, H) ++
          [ temp ::= H [+] K ; temp ::=+ M ]
          ++ CH ++  sigma1        (* temp = H + K + M + CH e f g + σ₁(e) *)
          ++ [ CLAIM H HAD h ; M HAD m ; E HAD e ; F HAD f ; G HAD g IN
                     Val temp = h <+> K <+> m <+>
                                  XorW (AndW e f) (AndW (NegW e) g) <+>
                                  XorW (XorW (RotR r10 e) (RotR r11 e)) (ShiftR s1 e) ]
          ++ [ D ::=+ temp ]
          ++ sigma0               (* temp = H + K + M + CH e f g + σ₁(e) + σ₀(a) *)
          ++ [ CLAIM H HAD h ; M HAD m ; E HAD e ; F HAD f ; G HAD g ; A HAD a IN
                     Val temp = h <+> K <+> m <+>
                                  XorW (AndW e f) (AndW (NegW e) g) <+>
                                  XorW (XorW (RotR r10 e) (RotR r11 e)) (ShiftR s1 e) <+>
                                  XorW (XorW (RotR r00 a) (RotR r01 a)) (ShiftR s0 a) ]
          ++ MAJ
          ++ [ H ::= temp [+] t ] (* h =  temp + MAJ a b c *)
          ++ [ CLAIM H HAD h ; A HAD a ; B HAD b ; C HAD c IN
                     Val H = Val temp <+>
                                 XorW (XorW (AndW a b) (AndW a c)) (AndW b c) ].
(*

*)
    End Code.

    Import StandardSemantics.
    Definition toProve : Prop.

      extractSAT STEP.
      
    Defined.

    Definition proof : toProve.
      time (
      unfold toProve;
      unfold genSAT;
      unfold SAT;
      unfold codeCheck;
      breakStore;
      lazy -[RotR ShiftR XorW AndW OrW NegW numBinOp N.add sub add pow K];
      repeat econstructor).
    Abort.
    
  End STEP.
  
End STEP.

Module SHA2 (C : CONFIG).

  Import C.
  Definition Word  := word WordSize.
  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE bigE Word.

  Section Program.

    Variable v : VariableT.
    Arguments v [k] _.



    (** ** Program variables.

        We begin by defining the program variables. Recall that, the
        standard idiom of verse is to declare the parameters, local
        variables, and register variables in that order.

     *)

    (** *** Parameters

        SHA2 hashes are Merkel-Damgrad hash. Hence it needs only the
        hash of the previous blocks to process the current block. Thus
        there is only one parameter for the hash function namely the
        hash of the previous block.

     *)

    Variable hash : v Hash.

    Definition parameters : Declaration := [ Var hash ]%vector.

    (** *** Local variables.

        We keep the current block in a set of local variables. The
        advantage of this is that on a register rich machine all of
        them could be allocated in registers and thus could be faster.

     *)

    Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : v Word.

    Definition message_variables
      := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]%vector.

    Definition locals : Declaration := Vector.map Var message_variables.

    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.



    (** ** The state and temporary variables.

        We choose to put them in registers as there are the variables
        that are frequently used.

     *)


    Variable a b c d e f g h : v Word.
    Variable t tp temp       : v Word.

    Definition state_variables := [ a ; b ; c ; d ; e ; f ; g ; h ]%vector.

    Definition registers : Declaration :=
      Vector.map Var (Vector.append state_variables [ t ; tp ; temp]%vector).


    Definition STATE : VarIndex v HASH_SIZE Word := varIndex state_variables.
    Definition LOAD_STATE : code v := loadCache hash STATE.


  (** * The hash transformation.

      The hashing algorithm transforms a state consisting of
      [HASH_SIZE] many [Word]s into [ROUNDS] many rounds. Each round
      uses a message word that is scheduled for that particular
      round. This section builds code towards implementing these.

   *)


    Section HashTransformation.

      (* The hash transformation is parameterised over the round [r]
      *)

      Variable r : nat.
      Variable rBoundPf : r < ROUNDS.

      Definition SigmaR := SIGMA' WordSize.
      Arguments SigmaR _ _ _ [v] _ _ _.
      (* ** Message scheduling.

         Although the message scheduling requires [ROUNDS] many
         values, we only need to keep track of a window of 16 values.
         This is because each the rth step requires only the rth
         message word and the subsequent message schedule requries
         only the previous 16 messages.

       *)

      Definition M : v Word.
        verse (@W (r mod BLOCK_SIZE) _).
      Defined.

      (** This defines M(r - j) *)
      Definition MM (j : nat) : v Word.
        verse (@W ((r + 16 - j) mod BLOCK_SIZE) _).
      Defined.

      (**

   The message schedule [m₁₆ = m₀ + m₋₇ + Σ₀ (m₋₁₅) + Σ₁ (m₋₂) ],
   requires computing the sigma functions of the form

   [Σ (x) = RotR(x, r0) ⊕ RotR(x, r1) ⊕ RotR(x, r2)]

   These functions can be implemented using a single temporary
   variable by updating them using the following telescopic values.

   [ RotR(x, r2 - r1) ]

   [ RotR(x, r2 - r1) ⊕ x]

   [ RotR(x, r2 - r0) ⊕ RotR(x, r1 - r0) ⊕ x]

   [ RotR(x, r2) ⊕ RotR(x, r1) ⊕ Rot(x, r0)]

   At each step the temporary variables need to be rotated and then
   xord by x. This message schedule is give by the following code.

       *)

      Definition SIGMA (r0 r1 r2 : nat)(x rM : v Word) :=
        [ REMEMBER x; REMEMBER rM;
          t ::=  x >*> (r2 - r1); t ::=^ x;
          t ::=>*>     (r1 - r0); t ::=^ x;
          t ::=>*>     r0       ;
          CLAIM x HAD x' ; t HAS t'
                             IN
                t' = (XorW (XorW (RotR r0 x') (RotR r1 x')) (RotR r2 x'));
          rM ::=+ t;
          CLAIM x HAD x' ; rM HAD m ; rM HAS m'
                                       IN
                m' = numBinOp N.add m (XorW (XorW (RotR r0 x') (RotR r1 x')) (RotR r2 x'))       
        ].

      Definition SCHEDULE :=
      let SIGMA0 := SIGMA R00 R01 R02 (MM 15) M in
      let SIGMA1 := SIGMA R10 R11 R12 (MM 2) M in
      [ M ::=+ MM 7 ] ++ SIGMA0 ++ SIGMA1.
(*      
      Definition SCHEDULE :=
        let SIGMA0 := SigmaR R00 R01 R02 (MM 15) t M in
        let SIGMA1 := SigmaR R10 R11 R12 (MM 2)  t M in
        [ M ::=+ MM 7 ] ++ SIGMA0 ++ SIGMA1.
*)
      (** ** Individual rounds.

      The state of the hash function is kept track of in the set of
      variables a-h, and in the rth round the update is given by

       *)



      (**

<< a' = t1 + t2

b' = a

c' = b

d' = c

e' = d + t1

f' = e

g' = f

h' = g

>>

where

<<

t1 = h + k + m + SIGB1 e + CH e f g

t2 = SIGB0 a + MAJ a b c

>>


       *)

      (** So in each round we compute the following

<<

temp = h + k + m + σ₁(e) + CH(e,f,g)

d += temp;

h = temp + σ₀(a) + MAJ(a,b,c); >>

       *)


      Definition ST (i : nat) : v Word.
        verse(
            let rp  := r mod HASH_SIZE in
            let idx := i + (16 - rp) in
            @STATE (idx mod HASH_SIZE) _).
      Defined.

      Definition K : constant Word :=  Vector.nth_order KVec rBoundPf.

      Definition STEP : code v :=
        let A := ST 0 in
        let B := ST 1 in
        let C := ST 2 in
        let D := ST 3 in
        let E := ST 4 in
        let F := ST 5 in
        let G := ST 6 in
        let H := ST 7 in
        let sigma r0 r1 s x :=
            [ t ::= x >*> (r1 - r0); t    ::=^ x;
              t ::=>*>    r0       ; tp   ::=  x >> s;
              t ::=^ tp            ; temp ::=+ t
            ]%list in
        let sigma0 := sigma r00 r01 s0 A in
        let sigma1 := sigma r10 r11 s1 E in
        let CH :=
            [ tp ::=~ E;
              tp ::=& G;
              t ::= E [&] F; t ::=^ tp; temp ::=+ t] in
        let MAJ :=
            [ t  ::=  B [|] C;
              t  ::=& A;
              tp ::=  B [&] C;
              t  ::=| tp
            ] in
        [ temp ::= H [+] K ; temp ::=+ M ]
          ++ CH ++  sigma1        (* temp = H + K + M + CH e f g + σ₁(e) *)
          ++ [ D ::=+ temp ]
          ++ sigma0               (* temp = H + K + M + CH e f g + σ₁(e) + σ₀(a) *)
          ++ MAJ
          ++ [ H ::= temp [+] t ]. (* h =  temp + MAJ a b c *)

      Definition UPDATE_ITH (i : nat) (pf : i < HASH_SIZE) : code v.
        verse ([ @STATE i _ ::=+ hash [- i -]]).
      Defined.

      Definition UPDATE : code v
        := foreach (indices hash) UPDATE_ITH ++ moveBackCache hash STATE.


      Definition Round : code v :=
        if leb r (ROUNDS - BLOCK_SIZE - 1) then STEP ++ SCHEDULE else STEP.
      
    End HashTransformation.

    Definition ALL_ROUNDS : code v := iterate Round.
    Definition sha2 : Iterator Block v :=
      {|
        setup   := LOAD_STATE;
        process := fun block => (LOAD_BLOCK block
                                         ++ ALL_ROUNDS
                                         ++ UPDATE);
        finalise := [ ]
      |}.
  End Program.

  Import StandardSemantics.

  Generalizable All Variables.

  Set Implicit Arguments.

  Fixpoint swapScope t (v : GenVariableT t) n (vT : Vector.t (some t) n) typ C {struct vT} :
    (scoped v vT (typ -> C)) -> (typ -> scoped v vT C) :=
    match vT with
    | []%vector                       => id
    | ((existT _ _ ty) :: vTt)%vector => fun s x vty => swapScope _ _ _ 
                                                                  (s vty) x
    end.

  Definition swapGScope (t : kind -> Type) n (vT : Vector.t (some t) n) typ (C : GenVariableT t -> Type) :
    (forall v, scoped v vT (typ -> C v)) -> (typ -> forall v, scoped v vT (C v)) :=
    fun f => fun t v => (swapScope v vT (C v) (f v) t).

  Arguments swapGScope [t n] _ [typ] _ _ /. 

  Ltac mapTyOf xt :=
    match xt with
    | _ ?y -> ?z => refine ((fun p => (((existT _ _ y) :: fst p, snd p))) _)%vector; mapTyOf z
    | ?x         => exact ([]%vector, x)
    end.

  (* Extract the scope out of a generic function *)
  Ltac getScope x := let xt := type of (x ProxyVar) in mapTyOf xt.

  Ltac rearrScope x :=
    let scp := fresh "scp" in
    let sc  := fresh "sc"  in
    let typ := fresh "typ" in
    let rx  := fresh "rx"  in
    simple refine (let scp : (Vector.t (some type) _ * Type) := _ in _);
    [shelve | getScope x | idtac];
    simple refine (let sc : Vector.t (some type) _ := _
                   in _);
    [shelve | exact (fst scp) | idtac]; simpl in *; 
    let nx := fresh "nx" in
    tryif
      pose (nx := swapGScope sc _ x)
    then
      let t := fresh "t" in
      match type of nx with
      | ?T -> _ => refine (fun t : T => _)
      end;
      let nxn := fresh "nxn" in
      pose (nxn := nx t);
      simpl in nxn;
      rearrScope nxn
    else
      exact x (*(@genSAT _ sc x)*).

  Ltac parametrize x :=
    repeat
      match type of x with
      | GenVariableT _ -> _ => extractSAT x
      | ?T -> _ => let t := fresh "t" in
                   refine (forall t : T, _ : Prop);
                   parametrize (x t)
      end.

  Ltac exParamProp x :=
    let tmp := fresh "tmp" in
    simple refine (let tmp : _ := _ in _);
    [shelve | rearrScope x | idtac];
    simpl in tmp; parametrize tmp.
    
  Definition toProve : Prop.
    exParamProp SIGMA.
  Defined.

  Definition proof : toProve.
    time (
        unfold toProve;
        unfold genSAT;
        unfold SAT;
        unfold codeCheck;
        breakStore;
        lazy -[RotR ShiftR XorW AndW OrW NegW numBinOp N.add sub add pow K];
        repeat econstructor).
  Abort.
End SHA2.

(*
   72 sec  - SIGMA, hand-scope-manipulated, without trailing add and claim
   term    - SIGMA, exParamScope, without trailing add and clean
   hang    - SIGMA, hand-scope-manipulated, with trailing add and claim
   666 sec - STEP, taken-out, no scope manipulation, with one remember and one end claim
   679 sec - STEP, taken-out, no scope manipulation, with one remember and one end claim
             simplify uses cbv instead of simpl (same output)
 *)