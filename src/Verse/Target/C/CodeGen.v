(* begin hide *)
Require Import Verse.Language.Types.
Require Import Verse.Monoid.Semantics.
Require Import Verse.TypeSystem.
Require Import Verse.Target.
Require Import Verse.Target.C.Ast.
Require Import Verse.Error.
Require Import Verse.Nibble.
Require        Verse.Scope.
Require Import List.
Import ListNotations.
Require Vector.
Import Vector.VectorNotations.
Require Import Verse.Ast.


(* end hide *)

(** * Target configuration for Portable C.

This module exposes a target configuration module for the C language
for use in generating portable C code. We start with definition some
helper functions and types and wrap it inside an Internal module so
that it is not available outside.

*)

Module Internals.

  Import Verse.Target.C.Ast.Expr.

  (** ** Target variables are not [cvar].

    We finally want the code to be pretty printed and hence the
    variable used in the final C code should be of type
    [cvar]. However, a stream in C is represented by a pointer and a
    counter and hence require two [cvars]. Thus we will be using the
    following variable in the target configuration for C.

    The inner match is sufficient to make coq's type checker happy but
    the advantage of this outer match is that it clearly says that the
    variable for a [direct] type is just a [cvar].  This makes writing
    the instruction translations easier.

   *)

  Definition variables : Variables.U c_type_system
    := fun k (ty : C.Ast.type k) =>
         match k with
         | direct => cvar ty
         | _      => match ty with
                    | ptrToArray n ty0 => (cvar ty * cvar uint64_t)%type
                    | _                => cvar ty
                    end
         end.
  Definition blockPtr : expr * expr -> expr := fst.
  Definition counter  : expr * expr -> expr := snd.

  (** Generates a list of declarations variables. For stream types it
     generates declaration for the associated pointer and the counter
     variables *)

  Fixpoint decl {k}{ty} : variables k ty ->  list declaration
   := match ty with
      | ptrToArray _ _
        => fun u => [ declare (ty:=ty)       (blockPtr u);
                      declare (ty:=uint64_t) (counter u)
                    ]
      | _ => fun u =>  [ declare (ty:=ty) u]
      end%list.

  (* begin hide *)
  Fixpoint trExpr {ty} (e : Ast.expr variables ty) : expr :=
    match e with
    | Ast.cval   c     => verse_const ty c
    | Ast.valueOf le   => match le with
                         | Ast.var v => v
                         | @Ast.deref _ _ _ b endn arr (exist _ i _) =>
                           let arrI := match b with
                                       | 1 => ptrDeref arr (* array[1] = pointer *)
                                       | _ => index arr i
                                       end in
                           match endn with
                           | hostE => arrI
                           | _     => convert_from endn ty arrI
                           end
                         end
    | Ast.binOp o e0 e1 => app o [trExpr e0; trExpr e1]
    | Ast.uniOp o e0 =>
      match o with
      | rotL n => rotateL ty (trExpr e0 , n)
      | rotR n => rotateR ty (trExpr e0, n)
      | x      => app x [trExpr e0]
      end
    end.

  Definition trAssign {ty} (le : Ast.lexpr variables ty) (ex : Ast.expr variables ty) :=
    let endianConversion endn cex :=
        match endn, cex with
        | hostE, _                            => cex
        | _, _                                => convert_to endn ty cex
        end in

    match le with
    | Ast.var v => C.Ast.assign v (trExpr ex)
    | @Ast.deref _ _ _ _ endn arr (exist _ i _)
      => C.Ast.assign (index arr i) (endianConversion endn (trExpr ex))
    end.

  (** This definition is giving some warning in terms of implicits please check *)
  Definition trInst ty (inst : Ast.instruction variables ty) : C.Ast.statement + {TranslationError}
    := let getCOP n (o : Ast.op n)
           := match o with
              | rotL _ | rotR _ => error (CouldNotTranslateBecause inst UpdatesNotForRotatesInC)
              | o => {- o -}
              end in
       let handleUpdate le (func : expr -> C.Ast.statement) :=
           match le with
           | Ast.var v => {- func v -}
           | @Ast.deref _ _ _ _ endn arr (exist _ i _)
             => match endn with
               | hostE => {- func (index arr i) -}
               | _     => error (CouldNotTranslateBecause inst UpdatesNeedHostEndian)
               end
           end
       in
       match inst with
       | assign le ex     => {- trAssign le ex -}
       | binopUpdate le o vex
         => co <- getCOP 2 o;
             handleUpdate le (fun lhs => C.Ast.update lhs co (Vector.map trExpr [vex]))
       | uniopUpdate le o
         =>  co <- getCOP 1 o;
              handleUpdate le (fun lhs => C.Ast.update lhs co [])
       | Ast.moveTo le v      => {- trAssign le (Ast.valueOf (Ast.var v)) -}
       | _                    => error (CouldNotTranslateBecause inst ExplicitClobberNotInC)
      end.


  (* end hide *)
  Definition trStatement (s : statement variables) :=
    let single x := cons x nil in
    match s with
    | existT _ ty inst => single <$> trInst ty inst
    end.

End Internals.

Module Config <: CONFIG.

  Definition statement   := C.Ast.statement.
  Definition programLine := Ast.line.

  Instance target_semantics : semantics (list C.Ast.statement + {TranslationError})
    := {| types :=  c_type_system;
          variables := Internals.variables;
          denote   := Internals.trStatement
       |}.

  Definition targetTs := TypeSystem.result types.
  Definition trType (ty : Types.type direct) : typeOf targetTs direct
    := let couldNotError := error (CouldNotTranslate ty)
       in match ty with
          | Word8  => {- uint8_t  -}
          | Word16 => {- uint16_t -}
          | Word32 => {- uint32_t -}
          | Word64 => {- uint64_t -}
          | _ => couldNotError
          end.

  Definition trConst (ty : Types.type direct)
    : Types.const ty -> constOf targetTs (trType ty)
    := match ty with
       | word n =>
         match n as n0
               return Types.const (word n0)
                      -> constOf targetTs (trType (word n0))
         with
         | 0 | 1 | 2 | 3  => fun x => Vector.to_list (Nibble.fromBv x)
         | _ => fun x : _ => error (CouldNotTranslate x)
         end
       | multiword _ _  => fun x => error (CouldNotTranslate x)
       end.

  Definition trOp (ty : Types.type direct) n
             : operator verse_type_system ty n ->
               operator targetTs (trType ty) n
    := fun op : Types.op n =>
          match trType ty as ty0
                return if ty0 then Types.op n else Empty_set + {TranslationError} with
          | error e => error e
          | _       => op
          end.

  Definition typeCompiler : TypeSystem.compiler verse_type_system types
    := verseTranslation trType trConst trOp.

  Definition streamOf {k}(block : type k)
    : typeOf c_type_system memory
    := let sz := match block with
                 | array b _ | ptrToArray b _ => b
                 | _ => 1
                 end in
       let ty0 := match block in type k0 return type direct with
                  | array _ t | ptrToArray _ t => t
                  | t => t
                  end in
       ptrToArray sz ty0.

  Definition dereference {k}{ty : type k}
    : variables  memory (streamOf ty) -> variables k ty
    :=  match ty with
       | ptrToArray b t => fun x => x (* this branch is not really used *)
       | _ => fun x => Expr.ptrDeref (Internals.blockPtr x)
       end.

  Definition mapOverBlocks {block : type memory}
             (stream : variables memory (streamOf block))
             (body : list statement)
             : list statement
    := (let cond := Expr.gt_zero (Internals.counter stream) in
        let actualBody :=  body ++
                                [ C.Ast.increment (Internals.blockPtr stream);
                                  C.Ast.decrement (Internals.counter stream)]

        in [ whileLoop cond (Braces actualBody) ]
       )%list.


  Fixpoint allocToList {n} (st : Scope.type types n)
    :  Scope.allocation variables st -> list declaration :=
    match st as st0 return Scope.allocation variables st0 -> list declaration
    with
    | []      => fun _   => nil
    | _ :: xs => fun arg =>
                   let this := Internals.decl (fst arg) in
                   let rest := allocToList xs (snd arg) in
                   (this ++ rest)%list
    end.

  Arguments allocToList [n st].

  Definition makeFunction (name : Set) (fname : name)(fsig : funSig types variables)
             (body : list statement)
    := let ps := params (allocToList (Target.parameters fsig)) in
       let ls := List.map declareStmt (allocToList (Target.locals fsig)) in
       let rs := List.map declareStmt (allocToList (Target.registers fsig)) in
       function fname ps (Braces (ls ++ rs ++ body))%list.

End Config.
