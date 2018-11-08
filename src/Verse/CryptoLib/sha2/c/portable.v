Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Require Import Verse.Semantics.StandardSemantics.
Import Nat.
Require Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

(** * SHA2 hashing algorithm.

We give a common iterator for both the sha512 and sha256 algorithm. It
is implemented as a module parameterised over the configuration
module.

*)
Module SHA2 (C : CONFIG).

  Import C.
  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE bigE Word.


  (** Some helper inequalities *)
  Hint Resolve NPeano.Nat.lt_0_succ.
  Definition zltBlockSize : 0 < BLOCK_SIZE.
    unfold BLOCK_SIZE. eauto.
  Defined.


  Definition nonZeroBlockSize : BLOCK_SIZE <> 0.
    unfold BLOCK_SIZE. eauto.
  Defined.



  Section Program.

    Variable v : VariableT.
    Arguments v [k] _.



    (** ** Program variables.

        The standard idiom of verse is to declare the parameters,
        local variables, and register variables in that order.

     *)

    (** *** Parameters

        SHA2 hashes are Merkel-Damgrad hash. The block iterator is
        only expected to compress the blocks and issues like padding
        is to be handled separately by the calling function.  Hence
        the iterator only needs the hash of the previous blocks to
        continue processing blocks. Thus there is only one parameter
        for the hash function namely the hash of the previous block.
     *)

    Variable hash : v Hash.

    Definition parameters : Declaration := [ Var hash ]%vector.

    (** *** Local variables.

        We keep the current block in a set of local variables. When
        compiling the resulting C code to a register rich machine, all
        of them could be allocated in registers and thus could be
        faster.

     *)

    Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : v Word.

    Definition message_variables
      := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]%vector.
    Definition locals : Declaration := Vector.map Var message_variables.
    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.

    (** * Message scheduling *)

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


    (** * Message scheduling.

        The block [w0,...,w15] is expanded to a message schedule
        [m(r)] given by the recurrence equation.

        [ m(r) = m(r - 16) + m(r - 7) + σ₀ m(r - 15) + σ₁ m(r - 2) ]

        where the σ₀ and σ₁ functions are of the form.


        [ σ(x) = RotR(x, r0) ⊕ RotR(x, r1) ⊕ ShiftR(x, s)]
        *)

    Section MessageSchedule.

      (** We give the message schedule calculation for the ith message
          index. Since the recurrence relation governing m(r) refers
          only to BLOCK_SIZE many previous values, rather than computing
          the sequence m(r) in separate variables we reuse the [w]
          varaibles by placing m(r) in [w(r mod BLOCK_SIZE)] *)


      Variable idx   : nat.
      Variable idxPf : idx < BLOCK_SIZE.


      (** Function to increment message index *)
      Definition nextIdx : { sIdx | sIdx < BLOCK_SIZE } :=
        if idx =? 15 then exist _ 0 zltBlockSize
        else let sIdx := S idx in
             exist _
                   (sIdx mod BLOCK_SIZE)
                   (NPeano.Nat.mod_upper_bound sIdx BLOCK_SIZE nonZeroBlockSize)
      .

      (* Alternate definitions:  For some reason these are slower *)

      (*
      Definition nextIdx : { sIdx | sIdx < BLOCK_SIZE } :=
        let sIdx := S idx in
        exist _
              (sIdx mod BLOCK_SIZE)
              (NPeano.Nat.mod_upper_bound sIdx BLOCK_SIZE nonZeroBlockSize).

      Definition nextIdx : { sIdx | sIdx < BLOCK_SIZE } :=
        match idx with
        | 15 => exist _ 0 zltBlockSize
        | _  => let sIdx := S idx in
                exist _
                      (sIdx mod BLOCK_SIZE)
                      (NPeano.Nat.mod_upper_bound sIdx BLOCK_SIZE nonZeroBlockSize)
        end.

        *)


      Definition M  := W idx idxPf.

      (** We capture m(idx - j) using this variable *)
      Definition MM (j : nat) : v Word.
        verse (W ((idx + 16 - j) mod BLOCK_SIZE) _).
      Defined.


      (** We now give the code for updating the message M with the value
          of the appropriate sigma function.
       *)
      Definition sigma (r0 r1 s : nat)(x : v Word) :=
        [ temp ::= x >*> r1; tp ::= x >*> r0;
          temp ::=^ tp;      tp ::= x >> s;
          temp ::=^ tp; M ::=+ temp
        ]%list.

      Definition SCHEDULE :=
        let sigma0 := sigma r00 r01 s0 (MM 15) in
        let sigma1 := sigma r10 r11 s1 (MM 2) in
        [ M ::=+ MM 7 ] ++ sigma0 ++ sigma1.

      (** This completes the code for message scheduling *)
    End MessageSchedule.

    Lemma correctnessNextIdx : forall n, proj1_sig (nextIdx n) = S n mod BLOCK_SIZE.
      intro n.
      do 16 (destruct n; trivial).
    Qed.


    (** * Sha2 round.

      The Sha2 hash function keeps track of a state in the variables
      a-h, and updates the state according to the equation.


      <<
      a' = t1 + t2
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
      t1 = h + k + m + 𝚺₁(e) + CH e f g
      t2 = 𝚺₀(a) + MAJ a b c
      >>

      where the 𝚺 functions are of the form
      𝚺 (x) = RotR(x , r0) ^ RotR(x,r1) ^ RotR(x,r2)
      We capture the state as a record of variables.

     *)

    Record State := { A : v Word;
                      B : v Word;
                      C : v Word;
                      D : v Word;
                      E : v Word;
                      F : v Word;
                      G : v Word;
                      H : v Word;
                      mIdx      : nat;
                      mIdxProof : mIdx < BLOCK_SIZE;
                     }.

    (** The starting state *)
    Definition state0 : State:=
      {| A := a;
         B := b;
         C := c;
         D := d;
         E := e;
         F := f;
         G := g;
         H := h;
         mIdx := 0;
         mIdxProof := zltBlockSize;
       |}.


    (** Instead of using different variables for each round we just
        update the state by permuting elements
     *)

    Definition newState (s : State):=
      match nextIdx  (mIdx s) with
        | exist _ r rpf =>
          {|
            A := H s;
            B := A s;
            C := B s;
            D := C s;
            E := D s;
            F := E s;
            G := F s;
            H := G s;
            mIdx := r;
            mIdxProof := rpf
          |}
      end.

    Definition Sigma r0 r1 r2 (x : v Word) :=
      [ temp ::= x >*> (r2 - r1); temp ::=^ x;
        temp ::=>*> (r1 - r0);    temp ::=^ x;
        temp ::=>*> r0
      ]%list.

    Definition Sigma0 (s : State) := Sigma R00 R01 R02 (A s).
    Definition Sigma1 (s : State) := Sigma R10 R11 R12 (E s).


    (** The CH and the MAJ functions are also defined computing their result
        into the temp variable temp
     *)
    Definition CH (s : State) : code v:=
            [ tp ::=~ E s;
              tp ::=& G s;
              temp ::= E s [&] F s; temp ::=^ tp
            ]%list.

    Definition MAJ (s : State) : code v :=
      [ temp  ::=  B s [|] C s;
        temp  ::=& A s;
        tp    ::=  B s [&] C s;
        temp  ::=| tp
      ].

    (**
       We now give the code for computing a single round given the
       state s and the round constant K
     *)
    Definition STEP (s : State) (K : constant Word) : code v :=
      let M : v Word := W (mIdx s) (mIdxProof s) in
      [ t ::= H s [+] K  ;  t ::=+ M ]
        ++ CH s        (* temp = CH e f g *)
        ++ [ t ::=+ temp ]
        ++  Sigma1 s   (* temp =  σ₁(e)   *)
        ++ [ t ::=+ temp ]
        ++ [ D s ::=+ t ]
        ++ Sigma0 s    (* temp =  σ₀(a) *)
        ++ [ t ::=+ temp ]
        ++ MAJ s       (* temp = MAJ a b c *)
        ++ [ H s ::= temp [+] t ] (* h =  t + MAJ a b c *)
    .

    Definition STEP_AND_SCHEDULE s K :=
      STEP s K ++ SCHEDULE (mIdx s) (mIdxProof s).

    Section GenerateRounds.
      Variable genCode : State -> constant Word -> code v.
      Fixpoint generateRounds (s : State) (Ks : list (constant Word))
               : code v * State
        := match Ks with
           | k :: ks =>
             let cde := genCode s k in
             let (cdeRest, stp) := generateRounds (newState s) ks in
             (cde ++ cdeRest, stp)
           | [ ] => ([ ],s)
           end.
    End GenerateRounds.


    Fixpoint splitAt {A}(n : nat)(l : list A) : list A * list A :=
      match l,n with
      | x::xs, S m => match splitAt m xs with
                        (ys,zs) => (x :: ys, zs)
                      end

      | _      , _ => ([ ],l)
      end.

    Definition ALL_ROUNDS :=
      let Ks := Vector.to_list KVec in
      let (KsInit, KsLast) := splitAt (ROUNDS - BLOCK_SIZE)  Ks in
      let (cd1, state1) := generateRounds STEP_AND_SCHEDULE state0 KsInit in
      let (cd2,_) := generateRounds STEP state1 KsLast in
      cd1 ++ cd2.


    Definition UPDATE_ITH (i : nat) (pf : i < HASH_SIZE) : code v.
      verse ([STATE i _ ::=+ hash [- i -]]).
    Defined.

    Definition UPDATE : code v
      := foreach (indices hash) UPDATE_ITH ++ moveBackCache hash STATE.

    Definition sha2 : iterator Block v :=
      {|
        setup   := LOAD_STATE;
        process := fun block => (LOAD_BLOCK block
                                         ++ ALL_ROUNDS
                                         ++ UPDATE);
        finalise := [ ]
      |}.
  End Program.
End SHA2.
