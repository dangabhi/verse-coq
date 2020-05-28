Require Import Verse.Target.
Require Import Verse.Target.C.CodeGen.

Module Compile := Target.CodeGen (C.CodeGen.Config).
Definition variables := Compile.variables.


(** * Auto allocation.

Since C can be seen as a machine with infinitely many registers, we
give an auto allocation for parameters and local variables. The down
side of this process is that we end up with meaningless variable names
in the generated code.


 *)

Require Import Verse.Target.C.Ast.
Import Expr.
Require Verse.Scope.
Require Vector.
Import Vector.VectorNotations.

(* begin hide *)
Module Internals.

  Definition mkVar (alk : nat) {k} (ty : type k) : variables k ty
    := match ty as ty0 in type k0 return variables k0 ty0 with
       | uint8_t    => cvar2exp (cVar uint8_t alk)
       | uint16_t   => cvar2exp (cVar uint16_t alk)
       | uint32_t   => cvar2exp (cVar uint32_t alk)
       | uint64_t   => cvar2exp (cVar uint64_t alk)
       | array sz t  => cvar2exp (cVar (array sz t) alk)
       | ptrToArray sz t => let ptrVar := @bPtr sz t in
                           let ctrVar := cTr in
                           (cvar2exp ptrVar, cvar2exp ctrVar)
       end.

  Definition mkQVar (alk : nat) s : TypeSystem.qualified variables s :=
    mkVar alk (projT2 s).

  Fixpoint calloc (alk : nat) {n} (st :  Scope.type C.Ast.c_type_system n)
    : Scope.allocation variables st * nat
    := match st as st0 return Scope.allocation variables st0 * nat with
         | [] => (tt, alk)
         | qty  :: qts
           => let (xs, used) := calloc (S alk) qts  in
             ((mkQVar alk qty , xs), used)
         end.

End Internals.
Require Import Verse.
Require Import Verse.Error.

(* end hide *)

Require Import Verse.
Import Scope.

Notation Function name func
  := ( let level0 := Scope.Cookup.specialise func in
       let (pvs, level1) := unNestDelimited level0 in
       let lvs := infer level1 in
       let pvt := recover (Compile.targetTypes pvs) in
       let lvt := recover (Compile.targetTypes lvs) in
       let (pA,n0) := Internals.calloc 0 pvt in
       let (lA,_) := Internals.calloc n0 lvt in
       Compile.function name pvs lvs
                        pvt     lvt
                        eq_refl eq_refl
                        pA      lA
     )
       (only parsing).


Notation Iterator name memty ifunc
  := ( let memtyTgt : TypeSystem.typeOf c_type_system TypeSystem.memory
           := recover (TypeSystem.Types.compile Compile.Config.typeCompiler memty) in
       let level0 := Cookup.specialise ifunc in
       let (pvs, level1) := unNestDelimited level0 in
       let lvs := infer level1 in
       let pvt := recover (Compile.targetTypes pvs) in
       let lvt := recover (Compile.targetTypes lvs) in
       let (pA,n0) := Internals.calloc 0 pvt in
       let (lA,n1) := Internals.calloc n0 lvt in
       let streamVar := Internals.mkVar n1 (Compile.Config.streamOf memtyTgt) in
       Compile.iterativeFunction name memty
                                 pvs lvs
                                 memtyTgt eq_refl
                                 streamVar
                                 pvt     lvt
                                 eq_refl eq_refl
                                 pA      lA
     )
       (only parsing).

Require Export Verse.Target.C.Ast.
Require Export Verse.Target.C.Pretty.
