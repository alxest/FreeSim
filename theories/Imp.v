(** * The Imp language  *)

(* begin hide *)
(* From Coq Require Import *)
(*      Arith.PeanoNat *)
(*      Lists.List *)
(*      Strings.String *)
(*      Morphisms *)
(*      Setoid *)
(*      RelationClasses. *)

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(* From ITree Require Import *)
(*      ITree *)
(*      ITreeFacts *)
(*      Events.MapDefault *)
(*      Events.StateFacts. *)

(* Import Monads. *)
(* Import MonadNotation. *)
(* Local Open Scope monad_scope. *)
(* Local Open Scope string_scope. *)

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.

Set Implicit Arguments.
(* end hide *)

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function call exists only as a statement *)
Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| Skip                           (* ; *)
| CallFun1 (x : var) (f : gname) (args : list expr) (* x = f(args), call by name *)
| CallFun2 (f : gname) (args : list expr)           (* f(args) *)
| CallPtr1 (x : var) (p : expr) (args : list expr)  (* x = f(args), by pointer*)
| CallPtr2 (p : expr) (args : list expr)            (* f(args) *)
| CallSys1 (x : var) (f : gname) (args : list expr) (* x = f(args), system call *)
| CallSys2 (f : gname) (args : list expr)           (* f(args) *)
| Expr (e : expr)                                   (* expression e *)
| AddrOf (x : var) (X : gname)         (* x = &X *)
| Load (x : var) (p : expr)            (* x = *p *)
| Store (p : expr) (v : expr)          (* *p = v *)
| Cmp (x : var) (a : expr) (b : expr)  (* memory accessing equality comparison *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var; (* disjoint with fn_params *)
  fn_body : stmt
}.

(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable/function *)
Variant GlobEnv : Type -> Type :=
| GetPtr (x: gname) : GlobEnv val
| GetName (p: val) : GlobEnv gname.

Section Denote.

  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
  Context {HasGlobVar: GlobEnv -< eff}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : eventE -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => Ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?
    end.

  (** Denotation of statements *)
  Definition while (step : itree eff (unit + val)) : itree eff val :=
    ITree.iter (fun _ => step) tt.

  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_exprs (es : list expr) (acc : list val) : itree eff (list val) :=
    match es with
    | [] => Ret acc
    | e :: s =>
      v <- denote_expr e;; denote_exprs s (acc ++ [v])
    end.

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);; Ret Vundef
    | Seq a b =>
      denote_stmt a;; denote_stmt b
    | If i t e =>
      v <- denote_expr i;; `b: bool <- (is_true v)?;;
      if b then (denote_stmt t) else (denote_stmt e)
    | Skip => Ret Vundef

    | CallFun1 x f args =>
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef
    | CallFun2 f args =>
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallPtr1 x e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef
    | CallPtr2 e args =>
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (String.string_dec f "load" || String.string_dec f "store" || String.string_dec f "cmp")
      then triggerUB
      else
        eval_args <- denote_exprs args [];;
        trigger (Call f (eval_args↑));; Ret Vundef

    | CallSys1 x f args =>
      eval_args <- denote_exprs args [];;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef
    | CallSys2 f args =>
      eval_args <- denote_exprs args [];;
      trigger (Syscall f eval_args top1);; Ret Vundef

    | Expr e => v <- denote_expr e;; Ret v

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      v <- trigger (Call "load" (p↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef
    | Cmp x ae be =>
      a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);; Ret Vundef

    end.

End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA.t}.
  Definition effs := GlobEnv +' ImpState +' Es.

  Definition handle_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : GlobEnv ~> (itree eff) :=
    fun _ e =>
      match e with
      | GetPtr X =>
        r <- (ge.(SkEnv.id2blk) X)?;; Ret (Vptr r 0)
      | GetName p =>
        match p with
        | Vptr n 0 => x <- (ge.(SkEnv.blk2id) n)?;; Ret (x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{eventE -< eff} (ge: SkEnv.t) : itree (GlobEnv +' eff) ~> (itree eff) :=
    interp (case_ (handle_GlobEnv ge) ((fun T e => trigger e) : eff ~> itree eff)).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{eventE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add x v le, tt)
      end.

  Definition interp_ImpState {eff} `{eventE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState ModSem.pure_state).

  Definition interp_imp ge le (itr : itree effs val) :=
    interp_ImpState (interp_GlobEnv ge itr) le.

  Fixpoint init_lenv xs : lenv :=
    match xs with
    | [] => []
    | x :: t => (x, Vundef) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc: lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | x :: part, v :: argt =>
      init_args part argt (alist_add x v acc)
    | _, _ => None
    end
  .

  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree Es val :=
    match (init_args f.(fn_params) args []) with
    | Some iargs =>
      '(_, retv) <- (interp_imp ge (iargs++(init_lenv f.(fn_vars))) (denote_stmt f.(fn_body)));; Ret retv
    | None => triggerUB
    end
  .

End Interp.

(* ========================================================================== *)
(** ** Program *)

(** program components *)
Definition progVars := list (gname * val).
Definition progFuns := list (gname * function).

(** Imp program *)
Record program : Type := mk_program {
  prog_vars : progVars;
  prog_funs : progFuns;
}.

(**** ModSem ****)
Module ImpMod.
Section MODSEM.

  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable m: program.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem (ge: SkEnv.t) : ModSem.t := {|
    ModSem.fnsems :=
      List.map (fun '(fn, f) => (fn, cfun (eval_imp ge f))) m.(prog_funs);
    ModSem.mn := mn;
    ModSem.initial_mr := ε;
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun ge => (modsem ge);
    Mod.sk :=
      (List.map (fun '(vn, vv) => (vn, Sk.Gvar vv)) m.(prog_vars)) ++
      (List.map (fun '(fn, _) => (fn, Sk.Gfun)) m.(prog_funs));
  |}.

End MODSEM.
End ImpMod.
