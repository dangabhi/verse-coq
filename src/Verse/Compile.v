Require Import Arch.
Require Import Error.
Require Import PrettyPrint.
Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
Require Import Vector.
Import VectorNotations.

Set Implicit Arguments.

(** * Compilation.

This module exposes code to compile verse programs to machine code. We
begin by defining the errors that can arise when code fragments are
compiled.

 *)

Inductive CompileError : Prop :=
| UnsupportedInstruction : forall {v : VariableT}, instruction v  -> CompileError
| UnsupportedType        : forall {k : kind}, type k -> CompileError
| UnavailableRegister    : forall {reg : VariableT}{k : kind}{ty : type k}, reg k ty -> CompileError
| UnsupportedLocalArray  : type memory -> CompileError.

(**

Compilation is parameterised by the architecture, the frame
management associated with the architecture and the code generator.

*)
Module Compiler (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  (* Internal module to hide local variables *)
  Module Internal.


    (** First we given a function to compile a list of instructions *)
    Section CompileInstructions.

      Let liftInstructionError
          {X : Type}
          {i : instruction  A.machineVar}
          (action : X  + { ~ A.supportedInst i } ) : X + { CompileError }
        := match action with
           | {- x -} => {- x -}
           | error _ => error (UnsupportedInstruction i)
           end.


      Definition compileInstructions insts :=
        let emitter := fun i => liftInstructionError (C.emit i) in
        C.sequenceInstructions <$> merge (List.map emitter insts).


    End CompileInstructions.

    Local Definition Allocation {n} (l : Vector.t (some type) n) :=
      allocation A.machineVar l * F.frameState + { CompileError }.

    Local Definition liftTypeError
          {X : Type}
          {k : kind}
          {ty : type k}
          (action : X + { ~ A.supportedType ty}) : X + { CompileError }
      := match action  with
         | {- x -} => {- x -}
         | error _ => error (UnsupportedType ty)
         end.

    Definition iterateFrame name ty := liftTypeError (F.iterateFrame name ty).

    (** Generate a frame with the given set of parameters or die trying *)
    Fixpoint params {n} s0 (l : Vector.t (some type) n) : Allocation l :=
      match l with
      | []           => {- (emptyAllocation A.machineVar, s0) -}
      | (existT _ _ ty :: rest)
        => a1 <- liftTypeError (F.addParam s0 ty);
             let (v, s1) := a1
             in a2 <- params s1 rest;
                  let (vs,s2) := a2
                  in {- ((v,vs), s2) -}
      end.

    (** Generate a frame with the given set of stack varaibles or die trying *)
    Fixpoint stacks {n} s0 (l : Vector.t (some type) n) : Allocation l :=
      match l with
      | []           => {- (emptyAllocation A.machineVar, s0) -}
      | (existT _ memory ty :: _) => error (UnsupportedLocalArray ty)
      | (existT _ direct ty :: rest)
        => a1 <- liftTypeError (F.stackAlloc s0 ty);
             let (v, s1) := a1
             in a2 <- stacks s1 rest;
                  let (vs,s2) := a2
                  in {- ((v,vs), s2) -}
      end.

    Fixpoint registers {n} {l : Vector.t (some type) n} : F.frameState ->
                             allocation A.register l -> Allocation l  :=
      match l with
      | []          => fun s0 _  => {- (emptyAllocation A.machineVar, s0) -}
      | (existT _ memory ty :: _) => fun _ _ => error (UnsupportedLocalArray ty)
      | (existT _ direct ty :: tys)
        => fun s0 (rs : allocation A.register (existT _ _ ty :: tys)) =>
             let (r,rest) := rs in
             match F.useRegister s0 r with
             | Some s1 => restAlloc <- registers s1 rest;
                            let (a,finalState) := restAlloc
                            in {- ((A.embedRegister r, a), finalState) -}
             | None    => error (UnavailableRegister r)
             end

      end.

    Section Function.
      Variable BODY : VariableT -> Type.
      Variable startState : F.frameState.

      (** Its parameters and stack variables *)
      Variable nP nS nR : nat.

      Variable parameterTypes : Vector.t (some type) nP.
      Variable stackTypes : Vector.t (some type) nS.

      Variable registerTypes : Vector.t (some type) nR.

      (** Its register variables *)
      Variable registerVariables : allocation A.register registerTypes.


      Let BodyType v := scoped v parameterTypes
                               (scoped v stackTypes
                                       (scoped v registerTypes (BODY v))
                               ).


      Definition fillVars (functionBody : forall v, BodyType v) :=
        pA <- params startState parameterTypes;
          let (pVars, paramState) := pA in
          lA <- stacks paramState stackTypes;
            let (sVars, stackState) := lA in
            rA <- registers stackState registerVariables;
              let (rVars, finalState) := rA in
              let code := fill rVars
                               (fill sVars
                                     (fill pVars (functionBody A.machineVar))
                               ) in
              {- (F.description finalState, code) -}.



    End Function.


    Let wrap descr (code : Doc + {CompileError}) := C.makeFunction descr <$> code.

    Definition compile {nP nL nR} name (pts : Vector.t (some type) nP)
                                       (lts : Vector.t (some type) nL)
                                       (rts : Vector.t (some type) nR) regs f
      := let state := F.emptyFrame name
         in result <- fillVars code state pts lts rts regs f;
              let (descr, code) := result  in wrap descr (compileInstructions code).

    Definition compileIterator {nP nL nR} ty name (pts : Vector.t (some type) nP)
                                       (lts : Vector.t (some type) nL)
                                       (rts : Vector.t (some type) nR) regs iterF
      := S <- iterateFrame name ty;
           let (iterVars, state) := S in
           let (codeV, countV)  := iterVars
           in result <- @fillVars (iterator ty) state nP nL nR pts lts rts regs iterF;
                let (descr, iF) := result in
                let setupCode       := compileInstructions (setup iF) in
                let iterationCode   := compileInstructions (process iF codeV) in
                let finaliseCode    := compileInstructions (finalise iF) in
                let body            := s <- setupCode; i <-  iterationCode; f <- finaliseCode;
                                         {- vcat [s; C.loopWrapper codeV countV i; f] -} in
                wrap descr body.

    Arguments compile [nP nL nR] _ _ _ [rts] _ _.
    Arguments compileIterator [nP nL nR] _ _ _ _ [rts] _ _.

  End Internal.

  Import Internal.
  Ltac function s p l r := simple refine (@compile _ _ _ s _ _ _ _ _);
                           [> shelve | shelve | shelve | declare p |  declare l | declare r | idtac | idtac ].
  Ltac iterator i s p l r := simple refine (@compileIterator _ _ _ i s _ _ _ _ _);
                             [> shelve | shelve | shelve | declare p |  declare l | declare r | idtac | idtac ].

End Compiler.
