Require Import Verse.Monoid.
Require Import Verse.TypeSystem.

Class Interface {ltypes} line `{Monoid line}
                (v : Variables.U ltypes)
  := {
      mtypes       : typeSystem;
      variables    : Variables.U mtypes;
      typeCompiler : TypeSystem.compiler ltypes mtypes;

      Var : forall {k} {ty : typeOf ltypes k},
            v _ ty -> Variables.result variables
                                       (typeTrans typeCompiler ty)
            (* This cannot use Universe.inject as if the typeCompiler
               is a true compiler, a Var map would not be possible at
               all!
            *)
    }.
