(* begin hide *)
Require Verse.Language.Ast.
Require Import Verse.Syntax.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.Ast.
Require Import List.
Require Import Omega.
Import ListNotations.

Set Implicit Arguments.
Generalizable Variables All.

(* end hide *)


(** * Utility functions.

When working with verse we often need to write repetitive coding
patterns. This section documents some helper functions to facilitate
refactoring such code. Once can think of such helpers as "assembler
macros" and one of the advantage of using a DSL is that such "macros"
can be implemented in the host language; coq in this case.

 *)


(* begin hide *)

Module Internal.
  Section Helper.

    Variable b : nat.

    Definition ithIndex i : list { i | i < b} :=
      match lt_dec i b with
      | left pf => [exist _ i pf]
      | right _ => []
      end.


    Fixpoint loopover i :=
      (match i with
       | 0   => []
       | S j => loopover j
       end ++ ithIndex i)%list.

  End Helper.

  Definition loop b := loopover b b.

(*  TODO: Prove the correctness of loop

      1. That the list is in increasing order
      2. That all elements < b are in the list.

 *)

End Internal.
Import Internal.

Section Utils.

  Variable tyD : typeC TypeDenote.

  (* end hide *)
  Section Looping.

    (** ** Looping.

     Verse supports bounded loops, i.e. loops that unfold into code.
     A loop for us is parameterised by two quantities, a program
     variable [v] and a bound [b]. A loop index is a some [i < b].

     *)
    Variable v : VariableT.
    Variable b : nat.

    (**

       The [foreach] function is the most general looping function. It
       takes as input a list of loop indices and executes (in
       sequence) its body for each of these indices

     *)

    Definition foreach (ixs : list {ix | ix < b})
               (f : forall ix, ix < b -> code v)
      := let mapper := fun ix => match ix with
                                 | exist _ i pf => f i pf
                                 end
         in List.concat (List.map mapper ixs).


    (** The code fragment [iterate f] executes the commands [f 0, f 1,
      ... f (b - 1)] in sequence.  Note that the program variable type
      v and the bound b are both implicit argument that is infered
      from the input argument [f].
     *)
    Definition iterate   := foreach (loop b).

    (** Similar to [iterate] but does in the reverse order *)
    Definition iterate_reverse := foreach (List.rev (loop b)).

  End Looping.

  Arguments foreach [v b] _ _.
  Arguments iterate   [v b] _.
  Arguments iterate_reverse [v b] _.

  Section ArrayUtils.

    (** ** Looping over array indices.

A common coding pattern is where we need to perform some action on all
the elements in an array. We now give functions and types that
simplify such looping over all the indices of the array. Let [A] be an
array variable, then the function [indices A] gives such a list in
increasing order starting from 0. We can then use [foreach] function
defined above to actually loop over these indices using the idiom
[foreach (indices A) doSomethingWithIndex]. The net result is an
unrolled loop that does some computation on every index of A. If one
wants to perform such a loop in the reverse order on can use the
function [indices_reversed] instead of [indices].

     *)



    Variable v : VariableT.
    Variable b : nat.
    Variable e : endian.
    Variable ty : type direct.



    (**
     This function returns the list of valid indices of an array
     variable. The indices are given starting from [0] to [b -
     1]. Mostly used in conjunction with [foreach].

     *)

    Definition indices (arr : v (array b e ty)) :  list (Indices arr)
      := loop b.


    (** This function is similar to indices but gives the indices in the
      reverse order.  *)
    Definition indices_reversed (arr : v (array b e ty)) := List.rev (indices arr).



    (** ** Indexing variables uniformly.

Programming with arrays is convenient because it gives a uniform way
to index elements which together with functions like [foreach], and
[indices], gives concise representation of repetitive coding
pattern. However, array indexing involves a memory operation which is
much slower than using registers. A technique that is often uses is to
"cache" the array in a set of registers [r0,r1...], and use this
registers instead.  But now we loose the ability to index the elements
uniformly which makes it tedious to write code that could otherwise be
handled conveniently using macros like [foreach].


The indexing problem is to give a uniform way to index a sequence of
program variables [v0,v1,...] using their position in the list as the
index. We solve this indexing problem as follows: We define the
function [varIndex] that takes a vector of variables [v_0,v_1...] and
returns the indexing function into the variables [v_0,...], i.e. the
indexing function takes an index [i] and returns the [i]th variable
[v_i].

     *)

    Require Vector.

    Definition VarIndex := forall i, i < b  -> @v direct ty.

    Definition varIndex (regs : Vector.t (@v direct ty) b)
      : VarIndex := fun _ pf  => Vector.nth_order regs pf.

    (**

One important use case for uniform indexing is the caching of arrays
into a sequence of registers. We now give some helper functions
that load and store arrays into their register cache.

     *)

    (** This macro loads the array to the corresponding chached variables *)
    Definition loadCache (arr : v (array b e ty)) (ch : VarIndex) : code v :=
      foreach (indices arr)
               (fun i pf => let ix := exist _ i pf in
                            let arrI := index arr ix in
                            let chI := var (ch i pf) in
                            [ inst (assign (assign2 nop chI arrI)) ]
      ).

    (**

      This macro moves back the cached values to the given array. In
      essence this macro uses the move instruction on all the cached
      variables. This has the following consequence.

      1. The values stored in the cached variables are clobbered at
         the end, which and hence should not be used subsequently.

      2. This macro moves all the cached values back into their
n         respective positions in the array. If only few of the cached
         variables are updated since caching, it might be more
         efficient to just move those explicitly.

     *)

    Definition moveBackCache (arr : v (array b e ty)) (ch : VarIndex)  : code v :=
      foreach (indices arr)
              (fun i pf => let ix := exist _ i pf in
                           [ inst (moveTo arr ix (ch i pf)) ]).

    (**
      This function is similar [moveCacheBack], except that it
      preserves the values in the cache variables. The cached
      variables can then be reused in the rest of the program.
     *)
    Definition backupCache  (arr : v (array  b e ty)) (ch : VarIndex) : code v :=
      foreach (indices arr)
              (fun i pf => let ix := exist _ i pf in
                           let arrI := index arr ix in
                           let chI := var (ch i pf) in
                           [ inst (assign (assign2 nop arrI chI)) ]
              ).



  End ArrayUtils.
End Utils.

  (* begin hide *)
  Arguments varIndex  [v b ty] _ _ _.
  Arguments loadCache [tyD v b e ty] _ _.
  Arguments moveBackCache [tyD v b e ty] _ _.
  Arguments backupCache [tyD v b e ty] _ _.
  Arguments indices [v b e ty] _.
  (* end hide *)
