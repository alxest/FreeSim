Require Import HoareDef MutHeader MutGImp MutG0 SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HTactics.
Require Import TODO.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Context `{Σ: GRA.t}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = (ε, tt↑)>>) /\
      (<<TGT: mrps_tgt0 = (ε, tt↑)>>)
  .

  Theorem correct:
    forall ge, ModSemPair.sim MutG0.GSem (MutGImp.GSem ge).
  Proof.
    econstructor 1 with (wf:=wf); et; ss.
    econs; ss. init. unfold cfun.
    unfold gF.
    unfold MutGImp.gF.
    Local Opaque vadd.
    steps.
    rewrite unfold_eval_imp.
    eapply Any.downcast_upcast in _UNWRAPN. des.
    unfold unint in *. destruct v; clarify; ss.
  Admitted.

End SIMMODSEM.
