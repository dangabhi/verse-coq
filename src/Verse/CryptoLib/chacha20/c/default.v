(**

An implementation of ChaCha20 stream cipher in verse.

*)

Require Import Verse.
Require Import Verse.Arch.C.
Require Import Verse.CryptoLib.ChaCha20.Common.
Require Vector.
Import VectorNotations.
Close Scope vector_scope.

Module Internal.

  Section ChaCha20.

    Variable progvar  : VariableT.
    Arguments progvar [k] _.

    (* The chacha20 round function takes the key, iv, and the counter *)
    Variable key      : progvar Key.
    Variable iv       : progvar IV.
    Variable ctrRef   : progvar (Array 1 hostE Counter).
    Definition parameters : Declaration
      := [Var key; Var iv; Var ctrRef].

  (* We do not have local stack variables *)
    Definition stack : Declaration    := [].

    (**
       Besides we have the following in registers

       1. The 4x4 state matrix in x0,...,x16
       2. A register copy of the counter
       3. A temporary register
   *)

    Variable x0  x1  x2  x3
             x4  x5  x6  x7
             x8  x9  x10 x11
             x12 x13 x14 x15 : progvar Word.
    Variable ctr             : progvar Counter.
    Variable Temp            : progvar Word.

    Definition stateVars := [ x0; x1; x2; x3;
                              x4; x5; x6; x7;
                              x8; x9; x10; x11;
                              x12; x13; x14; x15
                            ]%vector.

    Definition registers := List.map Var (Vector.to_list stateVars ++  [ctr; Temp]).

    (** It is useful to have a uniform way to index the state variables. *)

    Definition X : VarIndex progvar 16 Word := varIndex stateVars.




    (**
       The chach20 quarter round. It is either used on the columns of
       the matrix or the diagonals.
     *)

    Definition QROUND (a b c d : progvar Word) : code progvar.
      verse [ a ::=+ b; d ::=^ a; d ::=<*< 16;
              c ::=+ d; b ::=^ c; b ::=<*< 12;
              a ::=+ b; d ::=^ a; d ::=<*< 8;
              c ::=+ d; b ::=^ c; b ::=<*< 12
          ].
    Defined.

    (** Chacha20 is a stream cipher where each block is processed by
        xoring the block with the state matrix obtained after the
        Chacha20 state transformation. The state is first initialised as
        follows.
     *)
    Definition INITSTATE : code progvar.
      verse [
          x0  ::== C0         ; x1  ::== C1         ; x2  ::== C2         ; x3  ::== C3;
          x4  ::== key[- 0 -] ; x5  ::== key[- 1 -] ; x6  ::== key[- 2 -] ; x7 ::== key[- 3 -];
          x8  ::== key[- 4 -] ; x9  ::== key[- 5 -] ; x10 ::== key[- 6 -] ; x11 ::== key[- 7 -];
          x12 ::== ctr        ; x13 ::== iv[- 0 -]  ; x14 ::== iv[- 1 -]  ; x15 ::== iv[- 2 -]
        ].
    Defined.

    (** A double round consists of 4-Quarter round on the columns of the
        matrix followed by 4-Quarter rounds on the diagonals

     *)

    (** Finally we do 20 rounds i.e. 10 double rounds to get the chacha20
        state transformation
     *)
    Definition ROUND20 : code progvar :=
      let colRound := List.concat [ QROUND x0 x4 x8   x12;
                                    QROUND x1 x5 x9   x13;
                                    QROUND x2 x6 x10  x14;
                                    QROUND x3 x7 x11  x15
                                  ] in
      let diagRound := List.concat [ QROUND x0 x5 x10 x15;
                                     QROUND x1 x6 x11 x12;
                                     QROUND x2 x7 x8  x13;
                                     QROUND x3 x4 x9  x14
                                   ] in
      let doubleRound := colRound ++ diagRound
      in List.concat (List.repeat doubleRound 10).


    Definition UPDATE : code progvar.
      verse [
          x0  ::=+ C0         ; x1  ::=+ C1         ; x2  ::=+ C2         ; x3  ::=+ C3;
          x4  ::=+ key[- 0 -] ; x5  ::=+ key[- 1 -] ; x6  ::=+ key[- 2 -] ; x7  ::=+ key[- 3 -];
          x8  ::=+ key[- 4 -] ; x9  ::=+ key[- 5 -] ; x10 ::=+ key[- 6 -] ; x11 ::=+ key[- 7 -];
          x12 ::=+ ctr        ; x13 ::=+ iv[- 0 -]  ; x14 ::=+ iv[- 1 -]  ; x15 ::=+ iv[- 2 -]
        ].

    Defined.

    (** The code that computes the chacha20 key stream into the state matrix *)

    Definition COMPUTE_STREAM := List.concat [ INITSTATE; ROUND20; UPDATE].

    Definition XORBLOCK (B : progvar Block)(i : nat) (_ : i < 16)
      : code progvar.
      verse [ Temp ::== B[- i -]; Temp ::=^ X i _; MOVE Temp TO B[- i -] ].
    Defined.

    Definition LoadCounter : code progvar.
      verse [ ctr ::== ctrRef[- 0 -] ].
    Defined.
    Definition StoreCounter : code progvar.
      verse [ MOVE ctr TO ctrRef[- 0 -] ].
    Defined.

    Definition ChaCha20Iterator : iterator Block progvar :=
      {| setup := LoadCounter;
         process := fun blk =>
                      COMPUTE_STREAM
                        ++ foreach (indices blk) (XORBLOCK blk)
                        ++ [ ctr ::=+ Ox "00:00:00:01"];
         finalise := StoreCounter
      |}.


  End ChaCha20.

  (** Let us allocate the registers.  *)

  Definition regVars
    := (- cr Word "x0",  cr Word "x1",  cr Word "x2",  cr Word "x3",
          cr Word "x4",  cr Word "x5",  cr Word "x6",  cr Word "x7",
          cr Word "x8",  cr Word "x9",  cr Word "x10", cr Word "x11",
          cr Word "x12", cr Word "x13", cr Word "x14", cr Word "x15",
          cr Counter "ctr", cr Word "Tmp"
       -).



  Definition chacha20 (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Block fname parameters stack registers.
    assignRegisters regVars.
    statements ChaCha20Iterator.
  Defined.

End Internal.

(*

This is the function that prints the code on the standard output given a function name
for the c-code.

*)

Require Import Verse.Extraction.Ocaml.
Definition implementation (fp cfunName : string) : unit := writeProgram (C fp) (Internal.chacha20 cfuncName).
