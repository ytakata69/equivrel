(*
 * Usage: You may need "make equiv.vo" before
 * using this file.
 * In vscode, you may also need to add
 * "coqtop.args": [ "-Q", "/path/to/this/dir", "" ]
 * to settings.json.
 *)

Require Export equiv stack.

(* Rules of RPDS A and PDS A' *)

Section RPDS_to_PDS.

Local Open Scope type_scope.  (* for '*' *)

Parameter ruleA :
  Q -> Phi -> Q -> Com -> Prop.

Definition ruleA'_premise phi1 phi2 phi3 :=
    composable phi1 phi2 /\
    composableT phi2 phi3 /\
    is_equiv_rel phi3.

Inductive ruleA'
  : Q' -> Phi -> Q' -> Com' -> Prop :=
  | ruleA'_skip :
    forall q1 phi2 phi1 q2 phi3,
    ruleA q1 phi3 q2 skip ->
    ruleA'_premise phi1 phi2 phi3 ->
    ruleA' (q1, phi2) phi1
           (q2, compositionT phi2 phi3) skip'
  | ruleA'_pop :
    forall q1 phi2 phi1 q2 phi3,
    ruleA q1 phi3 q2 pop ->
    ruleA'_premise phi1 phi2 phi3 ->
    ruleA' (q1, phi2) phi1
           (q2, composition phi1 (compositionT phi2 phi3)) pop'
  | ruleA'_push :
    forall q1 phi2 phi1 q2 phi3 j,
    ruleA q1 phi3 q2 (push j) ->
    ruleA'_premise phi1 phi2 phi3 ->
    ruleA' (q1, phi2) phi1
           (q2, phi_to_Phi_eq_j j phi3) (push' (compositionT phi2 phi3)).

(* Transitions between configurations *)

Definition freshness_p_on_moveA (theta' theta : Theta) z (u : Stack) :=
  forall i,
  (exists j, theta' i = theta j) \/ theta' i = z \/
    Forall (not_contain (theta' i)) u.

Inductive moveA
  : Config -> Config -> Prop :=
  | MoveA :
    forall phi com z zth u q1 q2 theta theta',
    ruleA q1 phi q2 com ->
    is_equiv_rel phi ->
    (theta, z, theta') |= phi ->
    freshness_p_on_moveA theta' theta z ((z, zth) :: u) ->
    moveA (q1, theta,  ((z, zth) :: u))
          (q2, theta', update_stack ((z, zth) :: u) theta' com).

Inductive moveA'
  : Config' -> Config' -> Prop :=
  | MoveA' :
    forall q1 q2 z u com',
    ruleA' q1 z q2 com' ->
    moveA' (q1, (z :: u))
           (q2, update_stack' (z :: u) com').

(* freshness_p on stack *)

Axiom updater_must_exist :
  forall theta e phi u,
    (theta, e) |= phi -> is_equiv_rel phi ->
  exists theta',
    (theta, e, theta') |= phi /\
    freshness_p_on_moveA theta' theta e u.

(* accepting configurations *)

Parameter acceptingA :
  Q -> Phi (* over (X i)'s only *) -> Prop.

Definition Acc_A (c : Config) : Prop :=
  match c with
  | (p, theta, u) => u = nil /\
    exists phi,
    is_simpl_rel phi /\
    acceptingA p phi /\ theta |= phi
  end.

Definition acceptingA' (q : Q') : Prop :=
  let (p, phi) := q in
  acceptingA p (lat phi).

(* Lemmas *)

(* freshness_p_on_moveA *)

Lemma substack_keeps_freshness_p_on_moveA :
  forall theta theta' z a u1 u2,
  freshness_p_on_moveA theta' theta z (u1 ++ (a :: u2)) ->
  freshness_p_on_moveA theta' theta z (u1 ++ u2).
Proof.
  intros theta theta' z a u1 u2.
  unfold freshness_p_on_moveA.
  intros Hfrs i.
  destruct (Hfrs i) as [H | [H | H]].
  - (* exists j, theta' i = theta j -> ... *)
  left. exact H.
  - (* theta' i = z *)
  right. left. exact H.
  - (* Forall (not_contain (theta' i)) ... -> ... *)
  right. right.
  generalize H.
  apply (Forall_sublist _ a).
Qed.

(* weak_freshness_p *)

Lemma update_has_weak_freshness_p :
  forall th1 theta theta' z phi u,
  (theta, z, theta') |= phi ->
  freshness_p_on_moveA theta' theta z ((z, th1) :: u) ->
  weak_freshness_p th1 z theta theta'.
Proof.
  intros th1 theta theta' z phi u.
  intros Hphi Hfrs_m.
  unfold weak_freshness_p.
  intros i j.
  intros H.

  unfold freshness_p_on_moveA in Hfrs_m.
  destruct (Hfrs_m j) as [Hf | [Hf | Hf]].
  - (* exists m, theta' j = theta m -> ... *)
  destruct Hf as [m Hf].
  left.
  exists m.
  rewrite H.
  exact Hf.
  - (* theta' j = z -> ... *)
  right.
  rewrite H.
  exact Hf.
  - (* Forall (not_contain (theta' j)) ((z, th1) :: u) -> ... *)
  rewrite Forall_forall in Hf.
  assert (Hin : In (z, th1) ((z, th1) :: u)).
  { apply in_eq. }
  assert (Hf' := Hf (z, th1) Hin).
  unfold not_contain in Hf'.
  apply Hf' in H.
  contradiction.
Qed.

(* moveA *)

Local Lemma keeping_freshness_p_when_skip :
  forall theta theta' zth z u phi,
  (theta, z, theta') |= phi ->
  is_proper_stack ((z, zth) :: u) ->
  freshness_p_on_moveA theta' theta z ((z, zth) :: u) ->
  forall d1 d2 th1 th2,
  In (d1, th1) ((z, zth) :: u) ->
  In (d2, th2) u ->
  freshness_p_on_triple (bot, theta)  (d1, th1) (d2, th2) ->
  freshness_p_on_triple      (z, zth) (d1, th1) (d2, th2) ->
  freshness_p_on_triple (bot, theta') (d1, th1) (d2, th2).
Proof.
  intros theta theta' zth z u phi.
  intros Htst Hproper Hfrs_m.
  intros d1 d2 th1 th2.
  intros Hth1 Hth2.
  unfold freshness_p_on_triple.
  unfold freshness_p.
  intros [H1 H2].
  intros [Hz1 Hz2].

  unfold is_proper_stack in Hproper.
  rewrite Forall_forall in Hproper.
  assert (Hin : In (z, zth) ((z, zth) :: u)).
  { apply in_eq. }
  assert (Hp := Hproper (z, zth) Hin).
  simpl in Hp.
  clear Hin.
  destruct Hp as [zi EQz].

  unfold freshness_p_on_moveA in Hfrs_m.

  split.
  - (* forall i j, th i = theta' j -> exists l, th2 i = th1 l *)
  intros i j EQth2.
  destruct (Hfrs_m j) as [H | [H | H]];
  clear Hfrs_m.
  + (* exists m, theta' j = theta m -> ... *)
  destruct H as [m H].
  apply (H1 i m).
  rewrite EQth2.
  exact H.
  + (* theta' j = z -> ... *)
  apply (Hz1 i zi).
  rewrite EQth2.
  rewrite H.
  exact EQz.
  + (* Forall (not_contain (theta' j)) ((z, zth) :: u) -> ... *)
  rewrite Forall_forall in H.
  assert (Hin : In (d2, th2) ((z, zth) :: u)).
  { apply in_cons. apply Hth2. }
  assert (H' := H (d2, th2) Hin).
  unfold not_contain in H'.
  apply H' in EQth2.
  contradiction.

  - (* forall j, d2 = theta' j -> exists l, d2 = th1 l *)
  intros j EQd2.
  destruct (Hfrs_m j) as [H | [H | H]];
  clear Hfrs_m.
  + (* exists m, theta' j = theta m -> ... *)
  destruct H as [m H].
  apply (H2 m).
  rewrite EQd2.
  exact H.
  + (* theta' j = z -> ... *)
  apply (Hz2 zi).
  rewrite EQd2.
  rewrite H.
  exact EQz.
  + (* Forall (not_contain (theta' j)) ((z, zth) :: u) -> ... *)
  assert (Hin : In (d2, th2) ((z, zth) :: u)).
  { apply in_cons. apply Hth2. }
  assert (Hp := Hproper (d2, th2) Hin).
  simpl in Hp.
  destruct Hp as [m EQd2th2].
  rewrite EQd2th2 in EQd2.
  rewrite Forall_forall in H.
  assert (H' := H (d2, th2) Hin).
  unfold not_contain in H'.
  apply H' in EQd2.
  contradiction.
Qed.


Lemma moveA_keeps_freshness_p_when_skip :
  forall theta theta' zth z u phi,
  (theta, z, theta') |= phi ->
  is_proper_stack ((z, zth) :: u) ->
  freshness_p_on_moveA theta' theta z ((z, zth) :: u) ->
  freshness_p_on_stack theta  ((z, zth) :: u) ->
  freshness_p_on_stack theta' ((z, zth) :: u).
Proof.
  intros theta theta' zth z u phi.
  intros Hphi Hproper Hfrs_m Hfrs_s.
  unfold freshness_p_on_stack.
  unfold freshness_p_on_stack in Hfrs_s.
  apply Forall3_cons.
  - (* Forall2 ... ((z, zth) :: u) *)
  apply Forall2_cons.
  + (* Forall ... u *)
  apply Forall_forall.
  intros [d1 th1] H1.
  (* freshness_p_on_triple (, update ...) (z, zth) (d1, th1) *)
  apply (keeping_freshness_p_when_skip theta theta' zth z u phi);
  auto.
  * (* In (z, zth) ((z, zth) :: u) *)
  apply in_eq.
  * (* freshness_p_on_triple (, theta) (z, zth) (d1, th1) *)
  inversion Hfrs_s as [| x1 l1 Hfor2 Hfor3 [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor3.
  inversion Hfor2 as [| x1 l1 Hfor Hfor2' [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor2 Hfor2'.
  rewrite Forall_forall in Hfor.
  apply Hfor.
  exact H1.
  * (* freshness_p_on_triple (z, zth) (z, zth) (d1, th) *)
  unfold freshness_p_on_triple.
  unfold freshness_p.
  split.
  -- intros i j Hth1. now exists j.
  -- intros j Hd1. now exists j.

  + (* Forall2 ... u *)
  induction u as [| [d1 th1] u IHu].
  { apply Forall2_nil. }
  apply Forall2_cons.
  * (* Forall ... u *)
  apply Forall_forall.
  intros [d2 th2] H2.
  (* freshness_p_on_triple (, update ...) (d1, th1) (d2, th2) *)
  apply (keeping_freshness_p_when_skip theta theta' zth z ((d1, th1) :: u) phi);
  auto.
  -- apply in_cons. apply in_eq.
  -- apply in_cons. exact H2.
  -- (* freshness_p_on_triple (, theta) (d1, th1) (d2, th2) *)
  inversion Hfrs_s as [| x1 l1 Hfor2 Hfor3 [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor3.
  inversion Hfor2 as [| x1 l1 Hfor Hfor2' [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor2 Hfor.
  inversion Hfor2' as [| x1 l1 Hfor Hfor2 [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor2 Hfor2'.
  rewrite Forall_forall in Hfor.
  apply Hfor.
  exact H2.
  -- (* freshness_p_on_triple (z, zth) (d1, th1) (d2, th2) *)
  inversion Hfrs_s as [| x1 l1 Hfor2 Hfor3 [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor2.
  inversion Hfor3 as [| x1 l1 Hfor2 Hfor3' [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor3 Hfor3'.
  inversion Hfor2 as [| x1 l1 Hfor Hfor2' [EQx1 EQl1]].
  clear x1 EQx1 l1 EQl1 Hfor2 Hfor2'.
  rewrite Forall_forall in Hfor.
  apply Hfor.
  exact H2.

  * (* Forall2 ... u *)
  apply IHu.
  -- now apply (substack_is_proper_stack (d1, th1) ((z, zth) :: nil)).
  -- now apply (substack_keeps_freshness_p_on_moveA _ _ _ (d1,th1) ((z,zth)::nil)).
  -- now apply (Forall3_sublist _ (d1, th1) ((bot,theta)::(z,zth)::nil)).

  - (* Forall3 ... ((z, zth) :: u) *)
  now apply (Forall3_sublist _ (bot, theta) nil).
Qed.

Lemma moveA_keeps_freshness_p :
  forall q theta u q' theta' u',
  moveA (q, theta, u) (q', theta', u') ->
  is_proper_stack u ->
  freshness_p_on_stack theta u ->
  freshness_p_on_stack theta' u'.
Proof.
  intros q theta u q' theta' u'.
  intros HmA Hprop Hfresh.
  inversion HmA as [phi com z zth uu q1 q2 th1 th2
    HrA Heq_phi Hphi Hfrs_m [EQq1 EQth1 EQu] [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 q2 EQq2 th2 EQth2.

  assert (Hskip: freshness_p_on_stack theta' u).
  { rewrite<- EQu.
  apply (moveA_keeps_freshness_p_when_skip theta theta' _ _ _ phi);
  try rewrite EQu; auto; now rewrite<- EQu.
  }

  case_eq com;
  [intros Hcom | intros Hcom | intros j Hcom];
  rewrite Hcom in EQu';
  rewrite Hcom in HrA;
  clear com Hcom;
  unfold update_stack in EQu'.
  - (* com = pop -> ... *)
  apply (substack_keeps_freshness_p _ (z, zth) nil).
  unfold app.
  rewrite EQu.
  exact Hskip.
  - (* com = skip -> ... *)
  rewrite EQu.
  exact Hskip.
  - (* com = push -> ... *)
  apply push_keeps_freshness_p.
  rewrite EQu.
  exact Hskip.
Qed.

Lemma moveA_keeps_proper_stack :
  forall q theta u q' theta' u',
  moveA (q, theta, u) (q', theta', u') ->
  is_proper_stack u ->
  is_proper_stack u'.
Proof.
  intros q theta u q' theta' u'.
  intros HmA Hproper.
  inversion HmA as [phi com z zth uu q1 q2 th1 th2
    HrA Heq_phi Hphi Hfrs_m [EQq1 EQth1 EQu] [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 q2 EQq2 th2 EQth2.

  case_eq com;
  [intros Hcom | intros Hcom | intros j Hcom];
  rewrite Hcom in EQu';
  rewrite Hcom in HrA;
  clear com Hcom;
  unfold update_stack in EQu'.
  - (* com = pop -> ... *)
  unfold is_proper_stack.
  unfold is_proper_stack in Hproper.
  rewrite<- EQu in Hproper.
  inversion Hproper as [| x l Hz Hproper_u' [EQx EQl]].
  apply Hproper_u'.
  - (* com = skip -> ... *)
  rewrite EQu.
  exact Hproper.
  - (* com = push -> ... *)
  unfold is_proper_stack.
  apply Forall_cons.
  { exists j; reflexivity. }
  unfold is_proper_stack in Hproper.
  rewrite<- EQu in Hproper.
  exact Hproper.
Qed.

(* Theorem on bisimilarity *)

Section Bisimilarity.

Variables q q' : Q.
Variable  theta : Theta.
Variable  phi : Phi.
Variable  u : Stack.
Variable  v : Stack'.

Hypothesis Hfresh : freshness_p_on_stack theta u.
Hypothesis Hproper : is_proper_stack u.
Hypothesis Hu_last : last u (d_0, theta_0) = (d_0, theta_0).
Hypothesis Heq_phi : is_equiv_rel phi.
Hypothesis Heq_v : Forall is_equiv_rel v.

Lemma bisimilar_1 :
  forall theta' u',
    moveA (q, theta, u) (q', theta', u') ->
    config_R_config' (q, theta, u) ((q, phi), v) ->
  exists phi' v',
    moveA' ((q, phi), v) ((q', phi'), v') /\
    config_R_config' (q', theta', u') ((q', phi'), v').
Proof.
  intros theta' u'.
  intros HmA HR.
  inversion HmA as [phi3 com z zth uu q1 q2 th1 th2
    HrA Heq_phi3 Hphi3 Hfrs_m [EQq1 EQth1 EQu] [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 q2 EQq2 th2 EQth2.
  assert (Hfresh': freshness_p_on_stack theta' u).
  { rewrite<- EQu.
  rewrite<- EQu in Hproper.
  rewrite<- EQu in Hfresh.
  now apply (moveA_keeps_freshness_p_when_skip theta theta' _ _ _ phi3). }

  case_eq v.
  { (* v = nil -> ... *)
  intro EQv.
  rewrite EQv in HR.
  apply config_R_nil_nil_1 in HR as Hu_nil.
  rewrite Hu_nil in EQu.
  discriminate EQu.
  }
  (* v = phi1 :: vv -> ... *)
  intros phi1 vv EQv.

  inversion HR as [q1 theta1 u1 phi' v1 HsR [EQq1 EQth1 EQu1] [EQphi' EQv1]].
  clear q1 EQq1 theta1 EQth1 u1 EQu1;
  clear phi' EQphi' v1 EQv1.
  inversion HsR
  as [th2 phi' Hphi EQth2 Hu_nil |
      th2 th1 d1 phi' phi1' u1 v1 Hphi HsR1 EQth2 EQu1 EQphi' EQv1].
  { (* nil = u -> ... *)
  rewrite<- EQu in Hu_nil;
  discriminate Hu_nil.
  }
  (* ((d1, th1) :: u1) = u -> ... *)
  clear th2 EQth2 phi' EQphi'.
  rewrite<- EQu in EQu1.
  injection EQu1; clear EQu1.
  intros EQu1 EQth1 EQd1.
  rewrite EQu1 in HsR1; clear u1 EQu1.
  rewrite EQd1 in Hphi; clear d1 EQd1.
  rewrite EQv in EQv1.
  injection EQv1; clear EQv1.
  intros EQv1 EQphi1'.
  rewrite EQv1 in HsR1; clear v1 EQv1.
  rewrite EQphi1' in HsR1; clear phi1' EQphi1'.

  (* composable phi1 phi *)
  assert (Hphi_1: composable phi1 phi).
  { inversion HsR1
  as [th2 phi1' Hphi1 EQth2 EQuu EQphi1' EQvv |
     th2 th1' d1 phi' phi1' uu1 vv1 Hphi' HsR2 EQth2 EQuu1 EQphi' EQvv1].
  -- (* nil = vv -> ... *)
  now apply (double_models_means_composable theta_0 th1 theta d_0 z).
  -- (* (phi1' :: vv1) = vv -> ... *)
  now apply (double_models_means_composable th1' th1 theta d1 z).
  }

  (* weak_freshness_p th1 z theta theta' *)
  assert (Hwfrs: weak_freshness_p th1 z theta theta').
  { apply (update_has_weak_freshness_p th1 theta theta' z phi3 uu);
  now try rewrite EQth1. }

  (* composableT phi phi3 *)
  assert (Hphi_3: composableT phi phi3).
  { now apply (double_models_means_composableT th1 theta theta' z). }

  case_eq com.
  - (* com = pop -> ... *)
  intros Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (composition phi1 (compositionT phi phi3)).
  exists (update_stack' v pop').
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  now apply ruleA'_pop.

  + (* config_R_config' ... *)
  unfold update_stack in EQu'.
  unfold update_stack.
  rewrite<- EQu' in HmA.

  unfold update_stack'.
  apply Config_R_config'.

  destruct vv as [| phi0 vv].

  * (* vv = nil -> ... *)
  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |].
  clear th1' EQth1' phi1' EQphi1' EQvv.
  rewrite<- EQuu in EQu.
  rewrite<- EQuu in HsR1.
  rewrite<- EQuu in HmA.

  rewrite<- EQu in Hu_last.
  unfold last in Hu_last.
  injection Hu_last.
  intros EQth1' EQz.
  rewrite EQth1' in EQth1.

  unfold freshness_p_on_moveA in Hfrs_m.

  apply Stack_R_stack'_nil.
  apply (meanings_of_composition theta_0 th1 theta' d_0 z);
  auto.
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite EQv.
  apply in_eq.
  -- (* freshness_p theta_0 d_0 th1 theta' *)
  unfold freshness_p.
  rewrite EQth1.
  split.
  ++ intros i j H.
  exists i.
  reflexivity.
  ++ intros j H.
  apply proper_bottom.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta' z).

  * (* vv = phi0 :: vv -> ... *)
  inversion HsR1
  as [| th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
        EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  clear th1' EQth1' phi1' EQphi1' phi0' EQphi0' EQvv.

  apply Stack_R_stack'_cons;
  auto.
  apply (meanings_of_composition th0 th1 theta' d0 z);
  auto.
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite EQv.
  apply in_eq.
  -- (* freshness_p th0 d0 th1 theta' *)
  rewrite<- EQu in Hfresh'.
  rewrite<- EQuu in Hfresh'.
  unfold freshness_p_on_stack in Hfresh'.
  apply Forall3_hd3 in Hfresh'.
  unfold freshness_p_on_triple in Hfresh'.
  rewrite EQth1.
  exact Hfresh'.
  -- (* (th1, z, theta') |= compositionT ... *)
  now apply meanings_of_compositionT with theta.

  - (* com = skip -> ... *)
  intros Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (compositionT phi phi3).
  exists (update_stack' v skip').
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  now apply ruleA'_skip.

  + (* config_R_config' ... *)
  rewrite EQu in EQu'.
  unfold update_stack in EQu'.
  unfold update_stack.
  rewrite<- EQu' in HmA.
  clear u' EQu'.
  rewrite<- EQth1.

  unfold update_stack'.
  apply Config_R_config'.

  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |
      th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
      EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  * (* nil = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1' EQvv.

  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply meanings_of_compositionT with theta.
  -- (* stack_R_stack' th1 nil phi1 nil *)
  now apply Stack_R_stack'_nil.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta').
  -- (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  now apply Stack_R_stack'_cons.

  - (* com = push j -> ... *)
  intros j Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (phi_to_Phi_eq_j j phi3).
  exists (update_stack' v (push' (compositionT phi phi3))).
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  now apply ruleA'_push.

  + (* config_R_config' ... *)
  rewrite EQu in EQu'.
  unfold update_stack in EQu'.
  unfold update_stack.
  rewrite<- EQu' in HmA.
  clear u' EQu'.
  rewrite<- EQth1.

  unfold update_stack'.
  apply Config_R_config'.

  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |
      th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
      EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  * (* nil = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1' EQvv.

  apply Stack_R_stack'_cons.
  -- (* (theta', theta' j, theta') |= phi_to_Phi_eq_j ... *)
  now apply theta_models_phi_to_Phi_eq_j with z theta.
  -- (* stack_R_stack' theta' ((z, th1) :: nil) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply meanings_of_compositionT with theta.
  ++ (* stack_R_stack' th1 nil phi1 nil *)
  now apply Stack_R_stack'_nil.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (theta', theta' j, theta') |= phi_to_Phi_eq_j ... *)
  now apply theta_models_phi_to_Phi_eq_j with z theta.
  -- (* stack_R_stack' theta' ((z, th1) :: ...) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta').
  ++ (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  now apply Stack_R_stack'_cons.
Qed.

Lemma bisimilar_2 :
  forall phi' v',
    moveA' ((q, phi), v) ((q', phi'), v') ->
    config_R_config' (q, theta, u) ((q, phi), v) ->
  exists theta' u',
    moveA (q, theta, u) (q', theta', u') /\
    config_R_config' (q', theta', u') ((q', phi'), v').
Proof.
  intros phi' v'.
  intros HmA' HR.

  inversion HmA' as [q1 q2 phi1 vv com'
    HrA' [EQq1 EQv] [EQq2 EQv']].
  clear q1 EQq1 q2 EQq2.

  case_eq u.
  { (* u = nil -> ... *)
  intro EQu.
  rewrite EQu in HR.
  apply config_R_nil_nil_2 in HR as Hv_nil.
  rewrite Hv_nil in EQv.
  discriminate EQv.
  }
  (* u = (z, th1) :: uu -> ... *)
  intros [z th1] uu EQu.

  inversion HR as [q1 theta1 u1 phi'' v1 HsR [EQq1 EQth1 EQu1] [EQphi'' EQv1]].
  clear q1 EQq1 theta1 EQth1 u1 EQu1;
  clear phi'' EQphi'' v1 EQv1.
  inversion HsR
  as [th2 phi'' Hphi EQth2 Hu_nil |
      th2 th1' d1 phi'' phi1' u1 v1 Hphi HsR1 EQth2 EQu1 EQphi'' EQv1].
  { (* nil = u -> ... *)
  rewrite EQu in Hu_nil;
  discriminate Hu_nil.
  }
  (* ((d1, th1) :: u1) = u -> ... *)
  clear th2 EQth2 phi'' EQphi''.
  rewrite EQu in EQu1.
  injection EQu1; clear EQu1.
  intros EQu1 EQth1 EQd1.
  rewrite EQu1 in HsR1; clear u1 EQu1.
  rewrite EQd1 in Hphi; clear d1 EQd1.
  rewrite EQth1 in HsR1.
  rewrite EQth1 in Hphi; clear th1' EQth1.
  rewrite<- EQv in EQv1.
  injection EQv1; clear EQv1.
  intros EQv1 EQphi1'.
  rewrite EQv1 in HsR1; clear v1 EQv1.
  rewrite EQphi1' in HsR1; clear phi1' EQphi1'.

  inversion HrA' as
  [q1 phi'' phi1' q2 phi3 HrA HrAp
   [EQq1 EQphi''] EQphi1' [EQq2 EQphi'] Hcom'
   | q1 phi'' phi1' q2 phi3 HrA HrAp
   [EQq1 EQphi''] EQphi1' [EQq2 EQphi'] Hcom'
   | q1 phi'' phi1' q2 phi3 j' HrA HrAp
   [EQq1 EQphi''] EQphi1' [EQq2 EQphi'] Hcom'
   ];
  clear q1 EQq1 q2 EQq2 phi'' EQphi'' phi1' EQphi1';
  rewrite<- Hcom' in EQv';
  rewrite<- Hcom' in HrA';
  clear com' Hcom';
  destruct HrAp as [Hphi_1 [Hphi_3 P3eq]];
  assert (H' := composableT_implies_models_phi
    phi phi3 th1 theta z Hphi Hphi_3);
  assert (H := updater_must_exist
    theta z phi3 u H' P3eq);
  destruct H as [theta' [Hphi3 Hfrs_m]];
  exists theta';

  (* Hfresh': freshness_p_on_stack theta' u *)
  rewrite EQu in Hproper;
  rewrite EQu in Hfresh;
  rewrite EQu in Hfrs_m;
  apply (moveA_keeps_freshness_p_when_skip theta theta' _ _ _ phi3)
  in Hfresh as Hfresh';
  auto;

  (* weak_freshness_p th1 z theta theta' *)
  assert (Hwfrs := update_has_weak_freshness_p th1 theta theta' z phi3 uu
    Hphi3 Hfrs_m).

  - (* com' = skip' -> ... *)
  exists (update_stack u theta' skip).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with phi3.

  + (* config_R_config' ... *)
  rewrite<- EQv' in HmA'.
  clear v' EQv'.

  unfold update_stack.
  unfold update_stack'.
  apply Config_R_config'.

  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |
      th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
      EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  * (* nil = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1' EQvv.

  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply meanings_of_compositionT with theta.
  -- (* stack_R_stack' th1 nil phi1 nil *)
  now apply Stack_R_stack'_nil.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta').
  -- (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  now apply Stack_R_stack'_cons.

  - (* com' = pop' -> ... *)
  exists (update_stack u theta' pop).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with phi3.

  + (* config_R_config' ... *)
  unfold update_stack' in EQv'.
  rewrite<- EQv' in HmA'.
  clear v' EQv'.

  unfold update_stack.
  unfold update_stack'.
  apply Config_R_config'.

  destruct uu as [| [d0 th0] uu].

  * (* uu = nil -> ... *)
  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |].
  clear th1' EQth1' phi1' EQphi1' EQuu.
  rewrite<- EQvv in EQv.
  rewrite<- EQvv in HsR1.
  rewrite<- EQvv in HmA'.
  clear vv EQvv.

  rewrite EQu in Hu_last.
  unfold last in Hu_last.
  injection Hu_last.
  intros EQth1 EQz.

  apply Stack_R_stack'_nil.
  apply (meanings_of_composition theta_0 th1 theta' d_0 z);
  auto.
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite<- EQv.
  apply in_eq.
  -- (* freshness_p theta_0 d_0 th1 theta' *)
  unfold freshness_p.
  rewrite EQth1.
  split.
  ++ intros i j H.
  exists i.
  reflexivity.
  ++ intros j H.
  apply proper_bottom.
  -- (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta' z).

  * (* uu = (d0, th0) :: uu -> ... *)
  inversion HsR1
  as [| th1' th0' d0' phi1' phi0 uu' vv' Hphi1 HsR2
        EQth1' [EQd0' EQth0' EQuu] EQphi1' EQvv].
  clear th1' EQth1' th0' EQth0' d0' EQd0' phi1' EQphi1' EQuu.

  apply Stack_R_stack'_cons;
  auto.
  apply (meanings_of_composition th0 th1 theta' d0 z);
  auto.
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite<- EQv.
  apply in_eq.
  -- (* freshness_p th0 d0 th1 theta' *)
  unfold freshness_p_on_stack in Hfresh'.
  apply Forall3_hd3 in Hfresh'.
  unfold freshness_p_on_triple in Hfresh'.
  exact Hfresh'.
  -- (* (th1, z, theta') |= compositionT ... *)
  now apply meanings_of_compositionT with theta.

  - (* com' = push' phi4 -> ... *)
  exists (update_stack u theta' (push j')).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with phi3.

  + (* config_R_config' ... *)
  rewrite<- EQv' in HmA'.
  clear v' EQv'.

  unfold update_stack.
  unfold update_stack'.
  apply Config_R_config'.

  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |
      th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
      EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  * (* nil = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1' EQvv.

  apply Stack_R_stack'_cons.
  -- (* (theta', theta' j', theta') |= phi_to_Phi_eq_j ... *)
  now apply theta_models_phi_to_Phi_eq_j with z theta.
  -- (* stack_R_stack' theta' ((z, th1) :: nil) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply meanings_of_compositionT with theta.
  ++ (* stack_R_stack' th1 nil phi1 nil *)
  now apply Stack_R_stack'_nil.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (theta', theta' j, theta') |= phi_to_Phi_eq_j ... *)
  now apply theta_models_phi_to_Phi_eq_j with z theta.
  -- (* stack_R_stack' theta' ((z, th1) :: ...) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi phi3 *)
  now apply (meanings_of_compositionT th1 theta theta').
  ++ (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  now apply Stack_R_stack'_cons.
Qed.

End Bisimilarity.

(* accepting configurations *)

Lemma accepting_configs_satisfy_R :
  forall q q' theta phi u v,
  config_R_config' (q, theta, u) ((q', phi), v) ->
  Acc_A (q, theta, u) <-> v = nil /\ acceptingA' (q', phi).
Proof.
  intros q q' theta phi u v.
  intros HR.
  split.
  - (* Acc_A c -> v = nil /\ acceptingA' c' *)
  intros H.
  unfold Acc_A in H.
  destruct H as [EQu H].
  destruct H as [phi1 [Hsimpl [HA Hphi1]]].
  rewrite EQu in HR.
  clear u EQu.
  inversion HR as [q1 theta1 u phi2 v1
    HsR [EQq1 EQth1 EQu] [EQq EQphi2 EQv1]].
  clear q1 EQq1 theta1 EQth1 u EQu phi2 EQphi2 v1 EQv1.
  inversion HsR as [theta1 phi2
    Hphi EQth1 EQnil EQphi2 EQv |].
  clear theta1 EQth1 phi2 EQphi2 EQnil.
  rewrite<- EQq.
  unfold acceptingA'.
  split; auto.
  rewrite (lat_phi_eq_simpl_phi _ _ _ _ _ Hphi1 Hphi).
  apply HA.
  - (* v = nil /\ acceptingA' c' -> Acc_A c *)
  intros [EQv HA'].
  rewrite EQv in HR.
  clear v EQv.
  inversion HR as [q1 theta1 u1 phi2 v
    HsR [EQq1 EQth1 EQu1] [EQq EQphi2 EQv]].
  clear q1 EQq1 theta1 EQth1 u1 EQu1 phi2 EQphi2 v EQv.
  inversion HsR as [theta1 phi2
    Hphi EQth1 EQu EQphi2 EQnil |].
  clear theta1 EQth1 phi2 EQphi2 EQnil.
  rewrite<- EQq.
  unfold Acc_A.
  split; auto.
  exists (lat phi).
  split; [| split].
  + apply lat_is_simpl_rel.
  + unfold acceptingA' in HA'.
  rewrite<- EQq in HA'.
  apply HA'.
  + apply (models_phi_implies_models_lat_phi _ _ _ _ Hphi).
Qed.

End RPDS_to_PDS.
