From Paco Require Import paco.
From Ordinal Require Import Ordinal.
Require Import Classical.
Require Import Wellfounded.
From compcert Require Import Coqlib Events Globalenvs Smallstep Behaviors.

Set Implicit Arguments.


(* For mixed simulation *)
Section DETERMINISM.
  Definition single_events_at (L: semantics) (s:L.(state)) : Prop :=
    forall t s', Step L s t s' -> (length t <= 1)%nat.

  Record receptive_at (L: semantics) (s: state L) : Prop :=
    Receptive_at {
        sr_at_receptive: forall t1 s1 t2,
          Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
        sr_at_traces:
        single_events_at L s
      }.

  Record determinate_at (L: semantics) (s: state L): Prop :=
    Determinate_at {
        sd_at_determ: forall t1 s1 t2 s2,
          Step L s t1 s1 -> Step L s t2 s2 ->
          match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
        sd_at_traces:
        single_events_at L s;
        sd_at_initial_determ: forall s2,
          initial_state L s -> initial_state L s2 -> s = s2;
        sd_at_final_nostep: forall r,
          final_state L s r -> Nostep L s;
        sd_at_final_determ: forall r1 r2,
          final_state L s r1 -> final_state L s r2 -> r1 = r2
      }.

  Definition dstep (L: semantics) ge :=
    (fun s1 t s2 => determinate_at L s1 /\ step L ge s1 t s2).
End DETERMINISM.
Notation " 'DStep' L " := (dstep L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'DStar' L " := (star (dstep L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'DPlus' L " := (plus (dstep L) (globalenv L)) (at level 1) : smallstep_scope.

Section DETERMINATE.
  Variable L: semantics.
  Hypothesis DETERM: determinate L.

  Lemma determinate_determinate_at (s: L.(state))
    :
    determinate_at L s.
  Proof.
    econstructor.
    { eapply sd_determ; eauto. }
    { intros t s' STEP. eapply sd_traces; eauto. }
    { intros s2 INIT0 INIT1. eapply sd_initial_determ; eauto. }
    { eapply sd_final_nostep; eauto. }
    { eapply sd_final_determ; eauto. }
  Qed.

  Lemma determinate_step_dstep (s s': L.(state)) t
        (STEP: Step L s t s')
    :
    DStep L s t s'.
  Proof.
    split; auto. eapply determinate_determinate_at.
  Qed.

  Lemma determinate_star_dstar (s s': L.(state)) t
        (STAR: Star L s t s')
    :
    DStar L s t s'.
  Proof.
    induction STAR.
    { econstructor 1. }
    { econstructor 2; eauto. eapply determinate_step_dstep; eauto. }
  Qed.

  Lemma determinate_plus_dplus (s s': L.(state)) t
        (PLUS: Plus L s t s')
    :
    DPlus L s t s'.
  Proof.
    inv PLUS. econstructor; eauto.
    eapply determinate_step_dstep; eauto.
    eapply determinate_star_dstar; eauto.
  Qed.
End DETERMINATE.


Section RECEPTIVE.
  Variable L: semantics.
  Hypothesis RECEPTIVE: receptive L.

  Lemma receptive_receptive_at (s: L.(state))
    :
    receptive_at L s.
  Proof.
    econstructor.
    { eapply sr_receptive; eauto. }
    { intros t s' STEP. eapply sr_traces; eauto. }
  Qed.
End RECEPTIVE.



(* Free Simulation *)
Section FREESIM.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis public_preserved:
    forall id, Senv.public_symbol (symbolenv L1) id = Senv.public_symbol (symbolenv L2) id.

Variant __freesim
          (r: Ord.t -> Ord.t -> state L1 -> state L2 -> Prop)
          (g: Ord.t -> Ord.t -> state L1 -> state L2 -> Prop):
  Ord.t -> Ord.t -> state L1 -> state L2 -> Prop :=
| _freesim_source_tau
    i1 i2 s1 s2 i1' s1'
    (STEP: Step L1 s1 E0 s1')
    (SIM: g i1' i2 s1' s2)
  :
  __freesim r g i1 i2 s1 s2
| _freesim_source_stuck
    i1 i2 s1 s2
    (NOFINAL: forall r, ~ final_state L1 s1 r)
    (NOSTEP: Nostep L1 s1)
  :
  __freesim r g i1 i2 s1 s2
| _freesim_target_step
    i1 i2 s1 s2
    (NOSTUCK: (exists r, final_state L2 s2 r) \/ (exists t s2', Step L2 s2 t s2'))
    (TARGET: forall s2' t (STEP: Step L2 s2 t s2'),
        (t = E0 /\ exists i2', g i1 i2' s1 s2') \/
          (exists i1' i2' s1', Plus L1 s1 t s1' /\ g i1' i2' s1' s2'))
    (FINAL: forall r (FINAL: final_state L2 s2 r), exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r)
  :
  __freesim r g i1 i2 s1 s2
| _freesim_progress
    i1 i2 s1 s2 i1' i2'
    (ORD1: Ord.lt i1' i1)
    (ORD2: Ord.lt i2' i2)
    (SIM: r i1' i2' s1 s2)
  :
  __freesim r g i1 i2 s1 s2
.

Lemma __freesim_mon (r0 r1 g0 g1: Ord.t -> Ord.t -> state L1 -> state L2 -> Prop)
      (LER: forall i1 i2 s1 s2, r0 i1 i2 s1 s2 -> r1 i1 i2 s1 s2)
      (LEG: forall i1 i2 s1 s2, g0 i1 i2 s1 s2 -> g1 i1 i2 s1 s2):
  forall i1 i2 s1 s2, __freesim r0 g0 i1 i2 s1 s2 -> __freesim r1 g1 i1 i2 s1 s2.
Proof.
  intros. inv H.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto. intros.
    exploit TARGET; eauto. intros. destruct H as [[? [? ?]]|[? [? [? [? ?]]]]].
    + left. split; auto. eexists. eauto.
    + right. eexists _, _, _. split; eauto.
  - econstructor 4; eauto.
Qed.

Definition _freesim r i1 i2 s1 s2 :=
  forall g (FIX: forall i1 i2 s1 s2, __freesim r g i1 i2 s1 s2 -> g i1 i2 s1 s2),
    g i1 i2 s1 s2.

Lemma _freesim_ind r P
      (IND: forall i1 i2 s1 s2, __freesim r P i1 i2 s1 s2 -> P i1 i2 s1 s2):
  forall i1 i2 s1 s2, _freesim r i1 i2 s1 s2 -> P i1 i2 s1 s2.
Proof. intros. eapply H. intros. eapply IND. eauto. Qed.

Lemma _freesim_fold r:
  forall i1 i2 s1 s2, __freesim r (_freesim r) i1 i2 s1 s2 -> _freesim r i1 i2 s1 s2.
Proof.
  intros. unfold _freesim. intros. eapply FIX.
  eapply __freesim_mon; [| |eapply H]; eauto.
  intros. eapply H0. intros. eapply FIX. eauto.
Qed.

Lemma _freesim_unfold r:
  forall i1 i2 s1 s2, _freesim r i1 i2 s1 s2 -> __freesim r (_freesim r) i1 i2 s1 s2.
Proof.
  eapply _freesim_ind.
  intros. eapply __freesim_mon; [| |eapply H]; eauto.
  eapply _freesim_fold.
Qed.

Lemma _freesim_mon: monotone4 _freesim.
Proof.
  intros i1 i2 s1 s2 r0 r1 H LE. revert i1 i2 s1 s2 H.
  eapply _freesim_ind. intros. eapply _freesim_fold.
  eapply __freesim_mon; eauto.
Qed.
#[local] Hint Resolve _freesim_mon: paco.

Definition freesim := paco4 _freesim bot4.
Arguments freesim: clear implicits.

Lemma freesim_ind P
      (IND: forall i1 i2 s1 s2, __freesim freesim (fun i1 i2 s1 s2 => P i1 i2 s1 s2 /\ freesim i1 i2 s1 s2) i1 i2 s1 s2 -> P i1 i2 s1 s2):
  forall i1 i2 s1 s2, freesim i1 i2 s1 s2 -> P i1 i2 s1 s2.
Proof.
  intros. cut (P i1 i2 s1 s2 /\ freesim i1 i2 s1 s2).
  { intros [? ?]. auto. }
  punfold H. induction H using _freesim_ind. split.
  { eapply IND. eapply __freesim_mon; [..|eapply H]; auto.
    intros. pclearbot. auto. }
  { pfold. eapply _freesim_fold. eapply __freesim_mon; [..|eapply H]; auto.
    intros. destruct H0. punfold H1. }
Qed.

Lemma not_safe_freesim r i1 i2 s1 s2
      (NSAFE: ~ safe L1 s1):
  _freesim r i1 i2 s1 s2.
Proof.
  apply not_all_ex_not in NSAFE. destruct NSAFE as [s1' NSAFE].
  apply not_all_ex_not in NSAFE. destruct NSAFE as [STAR NSAFE].
  remember E0. revert Heqt s2 NSAFE. induction STAR; intros; subst.
  - apply _freesim_fold. eapply _freesim_source_stuck; intros.
    + intros FINAL. eapply NSAFE. left. eauto.
    + intros t s1' STEP. eapply NSAFE. right. eauto.
  - apply Eapp_E0_inv in Heqt. destruct Heqt. subst.
    apply _freesim_fold. eapply _freesim_source_tau; eauto.
Qed.

Lemma freesim_target_dstar r i1 i2 s1 s2 s2'
      (STEPS: DStar L2 s2 E0 s2')
      (SIM: _freesim r i1 i2 s1 s2'):
  _freesim r i1 i2 s1 s2.
Proof.
  remember E0. revert Heqt. induction STEPS; auto. intros. subst.
  eapply Eapp_E0_inv in Heqt. destruct Heqt as [? ?]. subst.
  destruct H as [DET STEP]. eapply _freesim_fold. eapply _freesim_target_step; eauto.
  { intros. left. exploit DET.(sd_at_determ); [eapply STEP|eapply STEP0|..].
    intros [TR EQ]. inv TR. exploit EQ; auto. intros. subst.
    split; auto. eexists. eapply IHSTEPS; eauto.
  }
  { intros. exfalso. exploit sd_at_final_nostep; eauto. }
Qed.

Lemma tau_step_follow_dstar L s0 s1 s2 t
      (STEP: Step L s0 E0 s1)
      (STAR: DStar L s0 t s2)
      (NNIL: t <> E0):
  DStar L s1 t s2.
Proof.
  inv STAR; [intuition|].
  destruct H as [DET STEP1].
  exploit DET.(sd_at_determ); [eapply STEP|eapply STEP1|..].
  intros [TR EQ]. inv TR. exploit EQ; auto.
  intros. subst. auto.
Qed.

Lemma event_step_follow_dstar L s0 s1 s2 t1 t2
      (STEP: Step L s0 t1 s1)
      (STAR: DStar L s0 (t1 ** t2) s2)
      (NNIL: Datatypes.length t1 = 1%nat):
  DStar L s1 t2 s2.
Proof.
  inv STAR.
  { symmetry in H1. eapply Eapp_E0_inv in H1.
    destruct H1. subst. simpl in NNIL. auto with *. }
  destruct H as [DET STEP1].
  exploit DET.(sd_at_determ); [eapply STEP|eapply STEP1|..].
  intros [TR EQ]. destruct t1; simpl in NNIL; [lia|].
  destruct t1; simpl in NNIL; [|lia].
  assert (exists e', t0 = e'::nil). { inv TR; eauto. }
  destruct H as [? ?]. subst. inv H1.
  exploit EQ; eauto. intros. subst. eauto.
Qed.

Lemma dstep_step_match L s2 t' s2' t'' s2'':
  DStep L s2 t' s2' -> Step L s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (symbolenv L) t' t'').
Proof.
  intros. destruct H as [DET STEP].
  exploit DET.(sd_at_determ); [eapply STEP|eapply H0|..].
  intros [TR EQ]. destruct t'.
  { subst. inv TR. left. split; auto. }
  { right. split; auto. { intros _H; inv _H. }
    split; auto. inv TR; auto; intro _H; inv _H. }
Qed.

Section ADEQUACY.
  Lemma freesim_step:
    forall i1 i2 s1 s2,
      freesim i1 i2 s1 s2 -> safe L1 s1 ->
      (forall r, final_state L2 s2 r ->
                 exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r) /\
        (forall s2' t, Step L2 s2 t s2' -> exists i1' i2', exists s1', Star L1 s1 t s1' /\ freesim i1' i2' s1' s2')
  .
  Proof.
    intros i1 i2. revert i1.
    induction i2 using (well_founded_induction Ord.lt_well_founded).
    intros i1 s1 s2 SIM SAFE. revert H SAFE.
    induction SIM using freesim_ind; intros. inv H.
    { destruct SIM as [IH SIM]. exploit IH.
      { intros. exploit H0; eauto. }
      { unfold safe. intros. eapply SAFE; eauto. econstructor 2; eauto. }
      { intros [FINH STEPH]. split; intros.
        { exploit FINH; eauto. intros [? [? ?]].
          eexists. split; [|eauto]. econstructor 2; eauto. }
        { exploit STEPH; eauto. intros [? [? [? [? ?]]]].
          eexists _, _, _. split; [|eauto]. econstructor 2; eauto. } } }
    { exploit SAFE.
      { eapply star_refl. }
      { intros [[? ?]|[? [? ?]]].
        { exfalso. eapply NOFINAL. eauto. }
        { exfalso. eapply NOSTEP; eauto. } } }
    { split.
      { intros. exploit FINAL; eauto. }
      { intros. exploit TARGET; eauto.
        intros [[? [? [? ?]]]|[? [? [? [? [? ?]]]]]].
        { subst. eexists _, _, _. split; [|eauto]. eapply star_refl. }
        { eexists _, _, _. split; [|eauto]. eapply plus_star; eauto. } } }
    { eapply H0; eauto. }
  Qed.

  Lemma freesim_star:
    forall s2 t s2', Star L2 s2 t s2' ->
    forall i1 i2 s1 b, freesim i1 i2 s1 s2 -> safe_along_behavior L1 s1 (behavior_app t b) ->
    exists i1' i2', exists s1', Star L1 s1 t s1' /\ freesim i1' i2' s1' s2'.
  Proof.
    intros s2 t s2' STAR. induction STAR; intros.
    { eexists _, _, _. split; [eapply star_refl|]; eauto. }
    subst. exploit freesim_step; eauto.
    { eapply safe_along_safe; eauto. }
    intros [? ?]. exploit H3; eauto. intros [? [? [? [? ?]]]].
    exploit IHSTAR; eauto.
    { eapply star_safe_along; eauto.
      rewrite behavior_app_assoc. eauto. }
    intros [? [? [? [? ?]]]]. eexists _, _, _. split; eauto.
    eapply star_trans; eauto.
  Qed.

  Lemma freesim_progress:
    forall i1 i2 s1 s2, freesim i1 i2 s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t s2', Step L2 s2 t s2').
  Proof.
    intros i1 i2. revert i1.
    induction i2 using (well_founded_induction Ord.lt_well_founded).
    intros i1 s1 s2 SIM SAFE. revert H SAFE.
    induction SIM using freesim_ind; intros. inv H.
    { destruct SIM as [IH SIM]. exploit IH; auto.
      unfold safe. intros. eapply SAFE; eauto. econstructor 2; eauto. }
    { exfalso. exploit SAFE.
      { eapply star_refl. }
      { intros [[? ?]|[? [? ?]]].
        { exfalso. eapply NOFINAL. eauto. }
        { exfalso. eapply NOSTEP; eauto. } } }
    { eauto. }
    { eapply H0; eauto. }
  Qed.

  Lemma forever_silent_coinduction_principle L (P: state L -> Prop)
        (COIND: forall s (IN: P s), exists s', Plus L s E0 s' /\ P s'):
    forall s (IN: P s), Forever_silent L s.
  Proof.
    cut (forall s0 (UPTO: exists s1, Star L s0 E0 s1 /\ P s1),
          exists s1, Step L s0 E0 s1 /\ (exists s2, Star L s1 E0 s2 /\ P s2)).
    { intros SCOIND.
      cut (forall s0 (UPTO: exists s1, Star L s0 E0 s1 /\ P s1), Forever_silent L s0).
      { intros. eapply H. eexists. split; eauto. eapply star_refl. }
      cofix COINDHYP. intros s0 SIN.
      eapply SCOIND in SIN. destruct SIN as [s1 [STEP IN]].
      econstructor; [eapply STEP|]. eapply COINDHYP. eauto.
    }
    intros. destruct UPTO as [s1 [SATR H]].
    eapply COIND in H. destruct H as [s' [PLUS H]].
    exploit star_plus_trans; eauto. intros. inv H0.
    symmetry in H3. eapply Eapp_E0_inv in H3. destruct H3. subst.
    eexists. split; eauto.
  Qed.

  Lemma freesim_forever_silent:
    forall i1 i2 s1 s2,
      Forever_silent L2 s2 -> freesim i1 i2 s1 s2 -> safe L1 s1 ->
      Forever_silent L1 s1.
  Proof.
    cut (forall s1 (IN: (fun s1 => exists i1 i2 s2, Forever_silent L2 s2 /\ freesim i1 i2 s1 s2 /\ safe L1 s1) s1), Forever_silent L1 s1).
    { intros. eapply H. eexists _, _, _. split; eauto. }
    eapply forever_silent_coinduction_principle.
    intros s1 [i1 [i2 [s2 [SILENT [SIM SAFE]]]]].
    revert i2 s2 SIM SILENT SAFE.
    induction i1 using (well_founded_induction Ord.lt_well_founded).
    intros. revert H SILENT SAFE.
    induction SIM using freesim_ind; intros. inv H.
    { destruct SIM as [IH SIM]. eexists. split.
      { eapply plus_one. eauto.  }
      { eexists _, _, _. split; eauto. split; eauto.
        unfold safe. intros. eapply SAFE. econstructor 2; eauto. } }
    { exfalso. exploit SAFE; [eapply star_refl|]. intros [[? ?]|[? [? ?]]].
      { eapply NOFINAL; eauto. }
      { eapply NOSTEP; eauto. } }
    { inv SILENT. exploit TARGET; eauto.
      intros [[? [? [? ?]]]|[? [? [? [? [? ?]]]]]].
      { exploit H3; eauto. }
      { eexists. split; eauto. eexists _, _, _. split; eauto.
        split; eauto. unfold safe. intros.
        eapply SAFE. eapply plus_star in H2. eapply star_trans; eauto. } }
    { eapply H0; eauto. }
  Qed.

  Lemma freesim_forever_reactive:
    forall i1 i2 s1 s2 T,
      Forever_reactive L2 s2 T -> freesim i1 i2 s1 s2 -> safe_along_behavior L1 s1 (Reacts T) ->
      Forever_reactive L1 s1 T.
  Proof.
    cofix COINDHYP; intros. inv H.
    destruct (freesim_star H2 (Reacts T0) H0) as [i' [s1' [A [B C]]]]; eauto.
    econstructor; eauto. eapply COINDHYP; eauto. eapply star_safe_along; eauto.
  Qed.

  Lemma freesim_state_behaves:
    forall i1 i2 s1 s2 beh2,
      freesim i1 i2 s1 s2 -> state_behaves L2 s2 beh2 ->
      exists beh1, state_behaves L1 s1 beh1 /\ behavior_improves beh1 beh2.
  Proof.
    intros. destruct (classic (safe_along_behavior L1 s1 beh2)).
    - (* 1. Safe along *)
      exists beh2; split; [idtac|apply behavior_improves_refl].
      inv H0.
      + (* termination *)
        assert (Terminates t r = behavior_app t (Terminates E0 r)).
        simpl. rewrite E0_right; auto.
        rewrite H0 in H1.
        exploit freesim_star; eauto.
        intros [i' [s1' [A [B C]]]].
        exploit freesim_step; eauto.
        eapply safe_along_safe. eapply star_safe_along; eauto.
        intros [? ?]. exploit H4; eauto.
        intros [s1'' [D E]].
        econstructor. eapply star_trans; eauto. traceEq. auto.
      + (* silent divergence *)
        assert (Diverges t = behavior_app t (Diverges E0)).
        simpl. rewrite E0_right; auto.
        rewrite H0 in H1.
        exploit freesim_star; eauto.
        intros [i' [s1' [A [B C]]]].
        econstructor. eauto. eapply freesim_forever_silent; eauto.
        eapply safe_along_safe. eapply star_safe_along; eauto.
      + (* reactive divergence *)
        econstructor. eapply freesim_forever_reactive; eauto.
      + (* goes wrong *)
        assert (Goes_wrong t = behavior_app t (Goes_wrong E0)).
        simpl. rewrite E0_right; auto.
        rewrite H0 in H1.
        exploit freesim_star; eauto.
        intros [i' [s1' [A [B C]]]].
        exploit freesim_progress; eauto. eapply safe_along_safe. eapply star_safe_along; eauto.
        intros [[r FIN] | [t' [s2' STEP2]]].
        elim (H4 _ FIN).
        elim (H3 _ _ STEP2).

    - (* 2. Not safe along *)
      exploit not_safe_along_behavior; eauto.
      intros [t [s1' [PREF [STEPS [NOSTEP NOFIN]]]]].
      exists (Goes_wrong t); split.
      econstructor; eauto.
      right. exists t; auto.
  Qed.

  Record free_simulation: Prop := {
      freesim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
      freesim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
                    exists i1 i2, exists s1', initial_state L1 s1' /\ freesim i1 i2 s1' s2;
      freesim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
    }.

  Theorem free_simulation_behavior_improves:
    free_simulation ->
    forall beh2, program_behaves L2 beh2 ->
    exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.
  Proof.
    intros S beh2 H. inv H.
    - (* L2's initial state is defined. *)
      destruct (classic (exists s1, initial_state L1 s1)) as [[s1 INIT] | NOINIT].
      + (* L1's initial state is defined too. *)
        exploit (freesim_match_initial_states S); eauto. intros [i1 [i2 [s1' [INIT1' SIM]]]].
        exploit freesim_state_behaves; eauto. intros [beh1 [A B]].
        exists beh1; split; auto. econstructor; [|eauto]. eauto.
      + (* L1 has no initial state *)
        exists (Goes_wrong E0); split.
        apply program_goes_initially_wrong.
        intros; red; intros. elim NOINIT; exists s0; auto.
        apply behavior_improves_bot.
    - (* L2 has no initial state *)
      exists (Goes_wrong E0); split.
      apply program_goes_initially_wrong.
      intros; red; intros.
      exploit (freesim_initial_states_exist S); eauto. intros [s2 INIT2].
      elim (H0 s2); auto.
      apply behavior_improves_refl.
  Qed.

  Corollary free_simulation_same_safe_behavior:
    free_simulation ->
    (forall beh, program_behaves L1 beh -> not_wrong beh) ->
    (forall beh, program_behaves L2 beh -> program_behaves L1 beh).
  Proof.
    intros. exploit free_simulation_behavior_improves; eauto.
    intros [beh' [A B]]. destruct B.
    congruence.
    destruct H2 as [t [C D]]. subst. elim (H0 (Goes_wrong t)). auto.
  Qed.
End ADEQUACY.


Section REPLAY.
  Variable index: Type.
  Variable order: index -> index -> Prop.
  Hypothesis order_wf: well_founded order.

  Variant _bsim
          (r: index -> state L1 -> state L2 -> Prop)
          (i: index) (s1: state L1) (s2: state L2): Prop :=
    | bsim_intro
        (SIM: forall t s2' (STEP: Step L2 s2 t s2') (SAFE: safe L1 s1),
          exists i' s1',
            (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
            /\ r i' s1' s2')
        (FINAL: forall r (SAFE: safe L1 s1) (FINAL: final_state L2 s2 r),
            exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r)
        (PROGRESS: forall (SAFE: safe L1 s1),
            (exists r, final_state L2 s2 r) \/ (exists t, exists s2', Step L2 s2 t s2')).

  Lemma _bsim_mon: monotone3 _bsim.
  Proof.
    intros i s1 s2 r0 r1 H LE. inv H. econstructor; eauto.
    intros. exploit SIM; eauto. intros [i' [s1' [STEPS H]]].
    eexists _, _. split; eauto.
  Qed.
  #[local] Hint Resolve _bsim_mon: paco.
  Definition bsim := paco3 _bsim bot3.

  Definition embed_stsim (r: index -> state L1 -> state L2 -> Prop)
             (i1 i2: Ord.t) (s1: state L1) (s2: state L2): Prop :=
    exists i, r i s1 s2 /\ Ord.le (Ord.from_wf order_wf i) i1 /\ Ord.le (Ord.from_wf order_wf i) i2.

  Lemma embed_stsim_mon r0 r1 (LE: r0 <3= r1):
    embed_stsim r0 <4= embed_stsim r1.
  Proof. intros. destruct PR as [i [SIM H]]. eexists. eauto. Qed.

  Lemma freesim_replay_bsim r:
    embed_stsim (_bsim r) <4= _freesim (embed_stsim r).
  Proof.
    intros i_src i_tgt s1 s2 [i [SIM [SRC TGT]]]. inv SIM.
    destruct (classic (safe L1 s1)) as [SAFE|NSAFE].
    2:{ eapply not_safe_freesim; eauto. }
    eapply _freesim_fold. eapply _freesim_target_step; eauto.
    intros. exploit SIM0; eauto. intros [i' [s1' [STEPS SIM]]].
    cut (Plus L1 s1 t s1' \/ s1 = s1' /\ t = E0 /\ order i' i).
    { intros [PLUS|[ST [TR ORD]]].
      { right. eexists _, _, _. split; [eapply PLUS|].
        eapply _freesim_fold. eapply _freesim_progress.
        { eapply Ord.S_lt. }
        { eapply Ord.S_lt. }
        { eexists. split; [eauto|]. split; [reflexivity|reflexivity]. } }
      { subst. left. split; [auto|]. eexists.
        eapply _freesim_fold. eapply _freesim_progress.
        { eapply Ord.lt_le_lt; [|eapply SRC].
          eapply Ord.lt_from_wf; eauto. }
        { eapply Ord.lt_le_lt; [|eapply TGT].
          eapply Ord.lt_from_wf; eauto. }
        { eexists. split; [eauto|]. split; [reflexivity|reflexivity]. } } }
    { destruct STEPS as [PLUS|[STAR ORD]]; auto.
      inv STAR; auto. left. econstructor; eauto. }
  Qed.

  Lemma freesim_imply_replayable F
        (REPLAY: forall r, embed_stsim (F r) <4= _freesim (embed_stsim r))
        (MON: monotone3 F):
    embed_stsim (paco3 F bot3) <4= freesim.
  Proof.
    pcofix CIH. intros. pfold. eapply _freesim_mon.
    { eapply REPLAY. eapply embed_stsim_mon; [|apply PR].
      intros. punfold PR0. }
    intros. right. eapply CIH. eapply embed_stsim_mon; [|apply PR0].
    intros. pclearbot. auto.
  Qed.

  Lemma bsim_imply_freesim: embed_stsim bsim <4= freesim.
  Proof.
    apply freesim_imply_replayable; auto with paco. apply freesim_replay_bsim.
  Qed.

  Variant _fdsim
          (r: index -> state L1 -> state L2 -> Prop)
          (i: index) (s1: state L1) (s2: state L2): Prop :=
    | fdsim_intro
        (SIM: forall t s1',
            Step L1 s1 t s1' ->
            exists i' s2',
              (DPlus L2 s2 t s2' \/ (DStar L2 s2 t s2' /\ order i' i))
              /\ r i' s1' s2')
        (FINAL: forall r, final_state L1 s1 r -> determinate_at L2 s2 /\ final_state L2 s2 r)
        (RECEPTIVE: receptive_at L1 s1).

  Lemma _fdsim_mon: monotone3 _fdsim.
  Proof.
    intros i s1 s2 r0 r1 SIM LE. inv SIM. econstructor; eauto.
    intros. exploit SIM0; eauto. intros [i' [s2' [STEPS SIM]]].
    eexists _, _. split; eauto.
  Qed.

  Definition _xsim
          (r: index -> state L1 -> state L2 -> Prop)
          (i: index) (s1: state L1) (s2: state L2): Prop :=
    _bsim r i s1 s2 \/ _fdsim r i s1 s2.

  Lemma _xsim_mon: monotone3 _xsim.
  Proof.
    intros i s1 s2 r0 r1 [BSIM|FSIM] LE.
    { left. eapply _bsim_mon; eauto. }
    { right. eapply _fdsim_mon; eauto. }
  Qed.
  #[local] Hint Resolve _xsim_mon: paco.
  Definition xsim := paco3 _xsim bot3.

  Variant _fsim
          (r: index -> state L1 -> state L2 -> Prop)
          (i: index) (s1: state L1) (s2: state L2): Prop :=
    | fsim_intro
        (SIM: forall t s1',
            Step L1 s1 t s1' ->
            exists i' s2',
              (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
              /\ r i' s1' s2')
        (FINAL: forall r, final_state L1 s1 r -> final_state L2 s2 r).

  Lemma _fsim_mon: monotone3 _fsim.
  Proof.
    intros i s1 s2 r0 r1 SIM LE. inv SIM. econstructor; eauto.
    intros. exploit SIM0; eauto. intros [i' [s2' [STEPS SIM]]].
    eexists _, _. split; eauto.
  Qed.
  #[local] Hint Resolve _fsim_mon: paco.
  Definition fsim := paco3 _fsim bot3.

  Lemma freesim_replay_fdsim r:
    embed_stsim (_fdsim r) <4= _freesim (embed_stsim r).
  Proof.
    intros i_src i_tgt s1 s2 [i [SIM [SRC TGT]]]. inv SIM.
    destruct (classic (exists t s1', Step L1 s1 t s1')) as [[t_ex [s1_ex STEPEX]]|NOSTEP].
    { clear FINAL. exploit SIM0; eauto.
      intros [i' [s2' [STEPS H]]].
      cut ((DStar L2 s2 t_ex s2' /\ t_ex <> E0) \/ (DPlus L2 s2 t_ex s2' /\ t_ex = E0) \/ s2 = s2' /\ t_ex = E0 /\ order i' i).
      { intros [[STAR NNIL]|[[PLUS NIL]|[ST [TR ORD]]]].
        { assert (SIM: forall t s1' (STEP: Step L1 s1 t s1') (NNIL: t <> E0),
                   exists s2' i', DStar L2 s2 t s2' /\ r i' s1' s2').
          { intros. exploit SIM0; eauto. intros [? [? [STEPS0]]].
            eexists _, _. split; [|eauto]. destruct STEPS0 as [PLUS|[? ?]]; auto.
            eapply plus_star; auto. }
          clear STEPS SIM0. revert NNIL STEPEX SIM. induction STAR; [intuition|]; intros.
          eapply _freesim_fold. apply _freesim_target_step; eauto.
          { inv H0. eauto. }
          { intros. exploit dstep_step_match; eauto.
            intros [[? [? ?]]|[NNIL0 [NNIL1 TR]]]; subst.
            { left. split; auto. eexists.
              eapply IHSTAR; eauto. intros.
              exploit SIM; eauto. intros [? [? [? ?]]].
              eexists _, _. split; [|eauto]. eapply tau_step_follow_dstar; eauto. }
            { right. exploit sr_at_traces; eauto. intros LEN.
              destruct t1, t2; simpl.
              { inv TR. exfalso. auto. }
              { exfalso. auto. }
              2:{ rewrite app_length in LEN. exfalso. simpl in LEN. lia. }
              destruct t1; [|simpl in LEN; lia].
              exploit sr_at_receptive; eauto.
              { rewrite E0_right. eapply match_traces_preserved; eauto. }
              intros [s1' STEPSRC]. exploit SIM; eauto. intros [? [? [? ?]]].
              exploit event_step_follow_dstar; [eapply STEP|..].
              { rewrite E0_right. eauto. }
              { inv TR; eauto. }
              intros. eexists _, _, _. split.
              { eapply plus_one; eauto. }
              eapply freesim_target_dstar; eauto.
              eapply _freesim_fold. eapply _freesim_progress.
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
              { eexists. split; eauto. split; reflexivity. } } }
          { inv H0. intros. exfalso. exploit sd_at_final_nostep; eauto. } }
        { inv PLUS. symmetry in H2.
          eapply Eapp_E0_inv in H2. destruct H2 as [? ?]. subst.
          destruct H0 as [DET STEP].
          eapply _freesim_fold. eapply _freesim_target_step; eauto.
          { intros. exploit DET.(sd_at_determ); [eapply STEP|eapply STEP0|..].
            intros [TR EQ]. inv TR. exploit EQ; auto. intros. subst.
            right. eexists _, _, _. split; [eapply plus_one; eauto|].
            eapply freesim_target_dstar; eauto.
            eapply _freesim_fold. eapply _freesim_progress; eauto.
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
            { eexists. split; eauto. split; reflexivity. } }
          { intros. exfalso. exploit sd_at_final_nostep; eauto. } }
        { subst. eapply _freesim_fold. eapply _freesim_source_tau; eauto.
          eapply _freesim_fold. eapply _freesim_progress.
          { eapply Ord.lt_le_lt; [|eapply SRC].
            eapply Ord.lt_from_wf; eauto. }
          { eapply Ord.lt_le_lt; [|eapply TGT].
            eapply Ord.lt_from_wf; eauto. }
          { eexists. split; [eauto|]. split; [reflexivity|reflexivity]. } } }
      { destruct STEPS as [PLUS|[STAR ORD]]; auto.
        { destruct t_ex; auto. left. split; [|intro _H; inv _H].
          eapply plus_star. auto. }
        destruct t_ex; auto.
        { inv STAR; auto. symmetry in H2.
          eapply Eapp_E0_inv in H2. destruct H2 as [? ?]. subst.
          right. left. split; auto. econstructor; eauto. }
        { left. split; auto. intro _H. inv _H. } } }
    destruct (classic (exists rv, final_state L1 s1 rv)) as [[rv FIN]|STUCK].
    { exploit FINAL; eauto. intros [DETERM FIN2].
      eapply _freesim_fold. apply _freesim_target_step.
      { eauto. }
      { intros. exfalso. exploit sd_at_final_nostep; eauto. }
      { intros. eexists _. split; [eapply star_refl|].
        eapply sd_at_final_determ in FIN2; eauto. subst. eauto. } }
    { apply not_safe_freesim. intros SAFE.
      exploit SAFE; [eapply star_refl|]. intros [H|H]; eauto. }
  Qed.

  Lemma freesim_replay_xsim r:
    embed_stsim (_xsim r) <4= _freesim (embed_stsim r).
  Proof.
    intros. cut (embed_stsim (_bsim r) x0 x1 x2 x3 \/ embed_stsim (_fdsim r) x0 x1 x2 x3).
    { intros [BSIM|FSIM].
      - eapply freesim_replay_bsim; eauto.
      - eapply freesim_replay_fdsim; eauto. }
    { destruct PR as [i [[FSIM|BSIM] [SRC TGT]]].
      - left. eexists _. eauto.
      - right. eexists _. eauto. }
  Qed.

  Lemma xsim_imply_freesim: embed_stsim xsim <4= freesim.
  Proof.
    apply freesim_imply_replayable; auto with paco. apply freesim_replay_xsim.
  Qed.

  Lemma freesim_replay_fsim
        (DETERM: determinate L2)
        (RECEPTIVE: receptive L1)
        r:
    embed_stsim (_fsim r) <4= _freesim (embed_stsim r).
  Proof.
    intros. eapply freesim_replay_fdsim.
    eapply embed_stsim_mon; [|eapply PR]. intros.
    inv PR0. econstructor; intros.
    { exploit SIM; eauto. intros [? [? [[? | [? ?]] ?]]].
      { eexists _, _. split; eauto.
        left. eapply determinate_plus_dplus; eauto. }
      { eexists _, _. split; eauto.
        right. split; auto. eapply determinate_star_dstar; eauto. } }
    { split; auto. eapply determinate_determinate_at; eauto. }
    { eapply receptive_receptive_at; eauto. }
  Qed.

  Lemma fsim_imply_freesim
        (DETERM: determinate L2)
        (RECEPTIVE: receptive L1):
    embed_stsim fsim <4= freesim.
  Proof.
    apply freesim_imply_replayable; auto with paco. apply freesim_replay_fsim; eauto.
  Qed.

  Variant _efsim
          (r: index -> state L1 -> state L2 -> Prop)
          (i: index) (s1: state L1) (s2: state L2): Prop :=
    | efsim_intro
        (SIM: forall t s1',
            Step L1 s1 t s1' ->
            exists i' s1'' s2' ,
              (Star L1 s1' E0 s1'') /\
                (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
              /\ r i' s1'' s2')
        (FINAL: forall r, final_state L1 s1 r -> final_state L2 s2 r).

  Lemma _efsim_mon: monotone3 _efsim.
  Proof.
    intros i s1 s2 r0 r1 SIM LE. inv SIM. econstructor; eauto.
    intros. exploit SIM0; eauto. intros [i' [s1'' [s2' [STAR [STEPS SIM]]]]].
    eexists _, _, _. split; eauto.
  Qed.
  #[local] Hint Resolve _efsim_mon: paco.
  Definition efsim := paco3 _efsim bot3.

  Lemma freesim_replay_efsim
        (DETERM: determinate L2)
        (RECEPTIVE: receptive L1)
        r:
    embed_stsim (_efsim r) <4= _freesim (embed_stsim r).
  Proof.
    intros.
    cut (embed_stsim (_fsim (fun i s1 s2 => exists s1', Star L1 s1 E0 s1' /\ r i s1' s2)) x0 x1 x2 x3).
    { intros H. eapply freesim_replay_fsim in H; eauto.
      clear PR. induction H using _freesim_ind. inv H.
      { eapply _freesim_fold. eapply _freesim_source_tau; eauto. }
      { eapply _freesim_fold. eapply _freesim_source_stuck; eauto. }
      { eapply _freesim_fold. eapply _freesim_target_step; eauto. }
      destruct SIM as [i [[s1' [STAR SIM]] [SRC TGT]]].
      remember E0. revert s2 Heqt SIM. induction STAR; intros; subst.
      { eapply _freesim_fold. eapply _freesim_progress; eauto. eexists. split; eauto. }
      { eapply Eapp_E0_inv in Heqt. destruct Heqt as [? ?]; subst.
        eapply _freesim_fold. eapply _freesim_source_tau; eauto. } }
    { eapply embed_stsim_mon; [|eapply PR]. intros.
      inv PR0. econstructor; eauto. intros.
      exploit SIM; eauto. intros [? [? [? [? [? ?]]]]].
      eexists _, _. split; eauto. }
  Qed.

  Lemma efsim_imply_freesim
        (DETERM: determinate L2)
        (RECEPTIVE: receptive L1): embed_stsim efsim <4= freesim.
  Proof.
    apply freesim_imply_replayable; auto with paco. apply freesim_replay_efsim; eauto.
  Qed.

End REPLAY.

Section ADEQUACY_ALTS.
  Lemma forward_to_free_simulation:
    forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
    free_simulation.
  Proof.
    intros FS L1_receptive L2_determinate. destruct FS as [index order match_states FS].
    econstructor.
    - (* initial states exist *)
      intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2 [A B]]].
      exists s2; auto.
    - (* initial states *)
      intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
      assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
      eexists (Ord.from_wf (fsim_order_wf FS) i), _, _.
      split; eauto. eapply fsim_imply_freesim; eauto.
      eexists. split; [|split; reflexivity].
      clear H H0 A. revert i s1 s2 B. pcofix CIH; intros.
      pfold. econstructor.
      { intros. exploit fsim_simulation; eauto.
        intros [? [? [? ?]]]. eexists _, _. split; eauto. }
      { intros. eapply fsim_match_final_states; eauto. }
    - (* symbols preserved *)
      exact (fsim_public_preserved FS).
  Qed.

  Theorem forward_simulation_behavior_improves_alt:
    forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
    forall beh2, program_behaves L2 beh2 ->
    exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.
  Proof.
    intros. eapply free_simulation_behavior_improves; eauto.
    eapply forward_to_free_simulation; eauto.
  Qed.

  Lemma backward_to_free_simulation:
    backward_simulation L1 L2 ->
    free_simulation.
  Proof.
    intros BS. destruct BS as [index order match_states BS].
    econstructor.
    - (* initial states exist *)
      intros. exploit (bsim_initial_states_exist BS); eauto.
    - (* initial states *)
      intros. exploit (bsim_match_initial_states BS); eauto. intros [i [s2' [A B]]].
      eexists (Ord.from_wf (bsim_order_wf BS) i), _, s2'.
      split; eauto. eapply bsim_imply_freesim; eauto.
      eexists. split; [|split; reflexivity].
      clear s1 H H0 A. revert i s2' s2 B. pcofix CIH; intros.
      pfold. econstructor.
      { intros. exploit bsim_simulation; eauto.
        intros [? [? [? ?]]]. eexists _, _. split; eauto. }
      { intros. eapply bsim_match_final_states; eauto. }
      { intros. eapply bsim_progress; eauto. }
    - (* symbols preserved *)
      intros. apply (bsim_public_preserved BS).
  Qed.

  Theorem backward_simulation_behavior_improves_alt:
    backward_simulation L1 L2 ->
    forall beh2, program_behaves L2 beh2 ->
    exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.
  Proof.
    intros. eapply free_simulation_behavior_improves; eauto.
    eapply backward_to_free_simulation; eauto.
  Qed.
End ADEQUACY_ALTS.

End FREESIM.
