(*
 * Usage: You may need "make equiv.vo" before
 * using this file.
 * In vscode, you may also need to add
 * "coqtop.args": [ "-Q", "/path/to/this/dir", "" ]
 * to settings.json.
 *)

Require Export equiv stack.

(* Rules of RPDA A and PDA A' *)

Section RPDA_to_PDA.

Local Open Scope type_scope.  (* for '*' *)

Parameter Sigma : Set.  (* finite alphabet *)

Parameter ruleA :
  Q -> Sigma -> Tst -> Q -> Asgn -> Com -> Prop.

Definition ruleA'_premise phi1 phi2 phi3 tst asgn :=
    composable phi1 phi2 /\
    composableT phi2 phi3 /\
    Phi_tst_asgn tst asgn phi3 /\
    is_equiv_rel phi3.

Inductive ruleA'
  : Q' -> Sigma -> Phi -> Q' -> Com' -> Prop :=
  | ruleA'_skip :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn skip ->
    ruleA'_premise phi1 phi2 phi3 tst asgn ->
    ruleA' (q1, phi2) a phi1
           (q2, compositionT phi2 phi3) skip'
  | ruleA'_pop :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn pop ->
    ruleA'_premise phi1 phi2 phi3 tst asgn ->
    ruleA' (q1, phi2) a phi1
           (q2, composition phi1 (compositionT phi2 phi3)) pop'
  | ruleA'_push :
    forall q1 phi2 a phi1 q2 phi3 tst asgn j,
    ruleA q1 a tst q2 asgn (push j) ->
    ruleA'_premise phi1 phi2 phi3 tst asgn ->
    ruleA' (q1, phi2) a phi1
           (q2, phi_to_Phi_eq_j j phi3) (push' (compositionT phi2 phi3)).

(* Transitions between configurations *)

Definition freshness_p_on_moveA (tst : Tst) (asgn : Asgn) d (u : Stack) :=
  (forall xi, tst xi <> true) -> (exists i, asgn i = true) ->
    Forall (not_contain d) u.

Inductive moveA
  : Config -> Sigma -> D -> Config -> Prop :=
  | MoveA :
    forall tst asgn com z zth u q1 q2 a d theta theta',
    ruleA q1 a tst q2 asgn com ->
    (theta, d, z) |= tst ->
    theta' = update theta asgn d ->
    freshness_p_on_moveA tst asgn d ((z, zth) :: u) ->
    moveA (q1, theta,  ((z, zth) :: u)) a d
          (q2, theta', update_stack ((z, zth) :: u) theta' com).

Inductive moveA'
  : Config' -> Sigma -> Config' -> Prop :=
  | MoveA' :
    forall q1 q2 a z u com',
    ruleA' q1 a z q2 com' ->
    moveA' (q1, (z :: u)) a
           (q2, update_stack' (z :: u) com').

(* Lemmas *)

(* freshness_p_on_moveA *)

Lemma updater_must_exist :
  forall theta e tst asgn th u phi phi3,
    (th, e, theta) |= phi ->
    Phi_tst_asgn tst asgn phi3 ->
    is_equiv_rel phi3 ->
    composableT phi phi3 ->
  exists d,
    (theta, d, e) |= tst /\
    freshness_p_on_moveA tst asgn d u.
Proof.
  intros theta e tst.
  intros asgn th u phi phi3.
  intros Hphi Hphi3 P3eq Hcom.
  destruct P3eq as [_ P3sym _].
  destruct (tst_is_empty_or_not tst)
  as [Htst_empty | Htst_not_empty].
  - (* tst_empty -> ... *)
  destruct (stack_has_outside_data theta e u)
  as [d [Hde [Hth Hu]]].
  exists d.
  unfold freshness_p_on_moveA.
  split; auto.
  (* (theta, d, e) |= tst *)
  unfold models.
  unfold Theta_D_D_models_Tst.
  split.
  * (* forall i, theta i = d <-> tst (inl i) = true *)
  split.
  -- intros H. apply Hth in H. contradiction.
  -- intros H. apply Htst_empty in H. contradiction.
  * (* e = d <-> tst (inr top) = true *)
  split.
  -- intros H. symmetry in H. apply Hde in H. contradiction.
  -- intros H. apply Htst_empty in H. contradiction.
  - (* tst_not_empty *)
  destruct Htst_not_empty as [xi Htst].
  unfold models in Hphi.
  unfold two_Theta_D_models_Phi in Hphi.
  destruct Hphi as [_ H11 _ _ H12].
  unfold Phi_tst_asgn in Hphi3.
  destruct Hphi3 as [H3 _].
  unfold composableT in Hcom.
  destruct Hcom as [Hc1 Hc2].
  unfold composable in Hc1.
  assert (H3' := H3 xi Htst).
  unfold models.
  unfold Theta_D_D_models_Tst.
  case_eq xi.
  + (* xi = inl n -> ... *)
  intros i Hxi.
  exists (theta i).
  split.
  * (* (theta, d, e) |= tst *)
  rewrite Hxi in H3'.
  split.
  -- (* forall j, theta j = theta i <-> tst (inl j) = true *)
  intros j.
  rewrite H11.
  rewrite Hc1.
  rewrite (H3' (inl j)).
  unfold X_.
  split; apply P3sym.
  -- (* e = theta i <-> tst (inr top) = true *)
  split.
  ++ intros He.
  apply (H3' (inr top)).
  unfold X_.
  rewrite<- Hc2.
  rewrite<- H12.
  symmetry.
  exact He.
  ++ intros Ht.
  symmetry.
  rewrite H12.
  rewrite Hc2.
  apply (H3' (inr top)).
  exact Ht.
  * (* freshness_p_on_moveA ... *)
  unfold freshness_p_on_moveA.
  intros H.
  apply H in Htst.
  contradiction.
  + (* xi = inr top -> ... *)
  intros t Hxi.
  destruct t.
  rewrite Hxi in H3'.
  rewrite Hxi in Htst.
  exists e.
  split.
  * (* (theta, d, e) |= tst *)
  split.
  -- (* forall i, theta i = e <-> tst (inl i) = true *)
  intros i.
  rewrite H12.
  rewrite Hc2.
  rewrite (H3' (inl i)).
  unfold X_.
  split; apply P3sym.
  -- (* e = e <-> tst (inr top) = true *)
  rewrite Htst.
  split; auto.
  * (* freshness_p_on_moveA ... *)
  unfold freshness_p_on_moveA.
  intros H.
  apply H in Htst.
  contradiction.
Qed.

Lemma substack_keeps_freshness_p_on_moveA :
  forall tst asgn d a u1 u2,
  freshness_p_on_moveA tst asgn d (u1 ++ (a :: u2)) ->
  freshness_p_on_moveA tst asgn d (u1 ++ u2).
Proof.
  intros tst asgn d a u1 u2.
  unfold freshness_p_on_moveA.
  intros Hfrs Htst Hasgn.
  assert (Hfrs' := Hfrs Htst Hasgn).
  generalize Hfrs'.
  apply (Forall_sublist _ a).
Qed.

(* weak_freshness_p *)

Lemma update_has_weak_freshness_p :
  forall th1 theta z d tst asgn u,
  (theta, d, z) |= tst ->
  freshness_p_on_moveA tst asgn d ((z, th1) :: u) ->
  weak_freshness_p th1 z theta (update theta asgn d).
Proof.
  intros th1 theta z d tst asgn u.
  intros Htst Hfrs_m.
  unfold weak_freshness_p.
  intros i j.
  intros H.
  unfold update in H.
  destruct (tst_is_empty_or_not tst)
  as [Htst_empty | Htst_not_empty].
  ++ (* tst_empty -> ... *)
  generalize dependent H.
  case_eq (asgn j); intros EQasgn H.
  ** (* asgn j = true -> ... *)
  apply ex_intro with (x := j) in EQasgn.
  assert (Hfrs_m' := Hfrs_m Htst_empty EQasgn).
  rewrite Forall_forall in Hfrs_m'.
  assert (Hzin : In (z, th1) ((z, th1) :: u)).
  { apply in_eq. }
  assert (Hm := Hfrs_m' (z, th1) Hzin).
  simpl in Hm.
  apply Hm in H.
  contradiction.
  ** (* asgn j = false -> ... *)
  left.
  exists j.
  exact H.
  ++ (* tst_not_empty -> ... *)
  clear Hfrs_m.
  unfold models in Htst.
  unfold Theta_D_D_models_Tst in Htst.
  destruct Htst as [Htst' Htst_top].
  destruct Htst_not_empty as [xi Htst_true].
  unfold freshness_p.
  case_eq xi.
  ** (* xi = inl n -> ... *)
  intros n EQxi.
  rewrite EQxi in Htst_true.
  rewrite<- Htst' in Htst_true.
  clear xi EQxi.
  left.
  generalize dependent H.
  case (asgn j); intro H.
  --- exists n.
  rewrite Htst_true.
  exact H.
  --- exists j.
  exact H.
  ** (* xi = inr top -> ... *)
  intros t EQxi.
  destruct t.
  rewrite EQxi in Htst_true.
  rewrite<- Htst_top in Htst_true.
  clear xi EQxi.
  generalize dependent H.
  case (asgn j); intro H.
  --- right.
  rewrite Htst_true.
  exact H.
  --- left. exists j.
  exact H.
Qed.

(* moveA *)

Local Lemma keeping_freshness_p_when_skip :
  forall theta zth d z u tst asgn,
  (theta, d, z) |= tst ->
  is_proper_stack ((z, zth) :: u) ->
  freshness_p_on_moveA tst asgn d ((z, zth) :: u) ->
  forall d1 d2 th1 th2,
  In (d1, th1) ((z, zth) :: u) ->
  In (d2, th2) u ->
  freshness_p_on_triple (bot, theta) (d1, th1) (d2, th2) ->
  freshness_p_on_triple     (z, zth) (d1, th1) (d2, th2) ->
  freshness_p_on_triple (bot, update theta asgn d) (d1, th1) (d2, th2).
Proof.
  intros theta zth d z u tst asgn.
  intros Htst Hproper Hfrs_m.
  intros d1 d2 th1 th2.
  intros Hth1 Hth2.
  unfold freshness_p_on_triple.
  unfold freshness_p.
  intros [H1 H2].
  intros [Hz1 Hz2].

  (* destruct Hfrs_m *)
  unfold freshness_p_on_moveA in Hfrs_m.
  destruct (tst_is_empty_or_not tst)
  as [Htst_empty | Htst_not_empty].

  - (* tst_empty -> ... *)
  unfold freshness_p_on_triple.
  unfold freshness_p.
  split.
  ** (* forall i j, th1 i = update ... -> ... *)
  intros i j.
  unfold update.
  case_eq (asgn j); intros EQasgn EQth2.
  +++ (* asgn j = true -> ... *)
  apply ex_intro with (x := j) in EQasgn.
  assert (Hfrs_m' := Hfrs_m Htst_empty EQasgn).
  rewrite Forall_forall in Hfrs_m'.
  assert (Hth2' : In (d2, th2) ((z, zth) :: u)).
  { apply in_cons. exact Hth2. }
  assert (Hm := Hfrs_m' (d2, th2) Hth2').
  simpl in Hm.
  apply Hm in EQth2.
  contradiction.
  +++ (* asgn j = false -> ... *)
  apply H1 with j.
  exact EQth2.
  ** (* forall j, d1 = update ... -> ... *)
  intros j.
  unfold update.
  case_eq (asgn j); intros EQasgn EQd2.
  +++ (* asgn j = true -> ... *)
  apply ex_intro with (x := j) in EQasgn.
  assert (Hfrs_m' := Hfrs_m Htst_empty EQasgn).
  rewrite Forall_forall in Hfrs_m'.
  assert (Hth2' : In (d2, th2) ((z, zth) :: u)).
  { apply in_cons. exact Hth2. }
  assert (Hm := Hfrs_m' (d2, th2) Hth2').
  simpl in Hm.
  (* destruct Hproper *)
  unfold is_proper_stack in Hproper.
  rewrite Forall_forall in Hproper.
  assert (Hprop2 := Hproper (d2, th2) Hth2').
  simpl in Hprop2.
  destruct Hprop2 as [i2 Hprop2].
  rewrite EQd2 in Hprop2.
  symmetry in Hprop2.
  apply Hm in Hprop2.
  contradiction.
  +++ (* asgn j = false -> ... *)
  apply H2 with j.
  exact EQd2.

  - (* tst_not_empty -> ... *)
  clear Hfrs_m.
  unfold models in Htst.
  unfold Theta_D_D_models_Tst in Htst.
  destruct Htst as [Htst' Htst_top].
  destruct Htst_not_empty as [xi Htst_true].
  case_eq xi.
  ** (* xi = inl n -> ... *)
  intros n EQxi.
  rewrite EQxi in Htst_true.
  rewrite<- Htst' in Htst_true.
  clear xi EQxi.

  split.
  --- (* forall i j, th1 i = update ... -> ... *)
  intros i j.
  unfold update.
  case (asgn j); intros EQth2.
  +++ (* asgn j = true -> ... *)
  apply H1 with n.
  rewrite Htst_true.
  exact EQth2.
  +++ (* asgn j = false -> ... *)
  apply H1 with j.
  exact EQth2.
  --- (* forall j, d1 = update ... -> ... *)
  intros j.
  unfold update.
  case (asgn j); intros EQd2.
  +++ (* asgn j = true -> ... *)
  apply H2 with n.
  rewrite Htst_true.
  exact EQd2.
  +++ (* asgn j = false -> ... *)
  apply H2 with j.
  exact EQd2.

  ** (* xi = inr top -> ... *)
  intros t EQxi.
  destruct t.
  rewrite EQxi in Htst_true.
  rewrite<- Htst_top in Htst_true.
  clear xi EQxi.

  (* destruct Hproper *)
  unfold is_proper_stack in Hproper.
  rewrite Forall_forall in Hproper.
  assert (Hzth: In (z, zth) ((z, zth) :: u)).
  { apply in_eq. }
  assert (Hpropz := Hproper (z, zth) Hzth).
  simpl in Hpropz.
  destruct Hpropz as [iz Hpropz].

  split.
  --- (* forall i j, th1 i = update ... -> ... *)
  intros i j.
  unfold update.
  case (asgn j); intros EQth2.
  +++ (* asgn j = true -> ... *)
  apply Hz1 with iz.
  rewrite EQth2.
  rewrite<- Htst_true.
  apply Hpropz.
  +++ (* asgn j = false -> ... *)
  apply H1 with j.
  exact EQth2.
  --- (* forall j, d1 = update ... -> ... *)
  intros j.
  unfold update.
  case (asgn j); intros EQd2.
  +++ (* asgn j = true -> ... *)
  apply Hz2 with iz.
  rewrite EQd2.
  rewrite<- Htst_true.
  apply Hpropz.
  +++ (* asgn j = false -> ... *)
  apply H2 with j.
  exact EQd2.
Qed.

Lemma moveA_keeps_freshness_p_when_skip :
  forall theta zth d z u tst asgn,
  (theta, d, z) |= tst ->
  is_proper_stack ((z, zth) :: u) ->
  freshness_p_on_moveA tst asgn d ((z, zth) :: u) ->
  freshness_p_on_stack theta ((z, zth) :: u) ->
  freshness_p_on_stack (update theta asgn d) ((z, zth) :: u).
Proof.
  intros theta zth d z u tst asgn.
  intros Htst Hproper Hfrs_m Hfrs_s.
  unfold freshness_p_on_stack.
  unfold freshness_p_on_stack in Hfrs_s.
  apply Forall3_cons.
  - (* Forall2 ... ((z, zth) :: u) *)
  apply Forall2_cons.
  + (* Forall ... u *)
  apply Forall_forall.
  intros [d1 th1] H1.
  (* freshness_p_on_triple (, update ...) (z, zth) (d1, th1) *)
  apply (keeping_freshness_p_when_skip _ zth _ z u tst asgn); auto.
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
  apply (keeping_freshness_p_when_skip _ zth _ z ((d1, th1) :: u) tst asgn);
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
  forall q theta u a d q' theta' u',
  moveA (q, theta, u) a d (q', theta', u') ->
  is_proper_stack u ->
  freshness_p_on_stack theta u ->
  freshness_p_on_stack theta' u'.
Proof.
  intros q theta u a d q' theta' u'.
  intros HmA Hprop Hfresh.
  inversion HmA as [tst asgn com z zth uu q1 q2 a' d' th1 th2
    HrA Htst EQth' Hfrs_m [EQq1 EQth1 EQu] EQa' EQd' [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 a' EQa' d' EQd' q2 EQq2 th2 EQth2.

  assert (Hskip: freshness_p_on_stack theta' u).
  { rewrite EQth'. rewrite<- EQu.
  apply moveA_keeps_freshness_p_when_skip with tst;
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
  forall q theta u a d q' theta' u',
  moveA (q, theta, u) a d (q', theta', u') ->
  is_proper_stack u ->
  is_proper_stack u'.
Proof.
  intros q theta u a d q' theta' u'.
  intros HmA Hproper.
  inversion HmA as [tst asgn com z zth uu q1 q2 a' d' th1 th2
    HrA Htst EQth' Hfrs_m [EQq1 EQth1 EQu] EQa' EQd' [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 a' EQa' d' EQd' q2 EQq2 th2 EQth2.
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
Variable  a : Sigma.

Hypothesis Hfresh : freshness_p_on_stack theta u.
Hypothesis Hproper : is_proper_stack u.
Hypothesis Hu_last : last u (d_0, theta_0) = (d_0, theta_0).
Hypothesis Heq_phi : is_equiv_rel phi.
Hypothesis Heq_v : Forall is_equiv_rel v.

Lemma bisimilar_1 :
  forall d theta' u',
    moveA (q, theta, u) a d (q', theta', u') ->
    config_R_config' (q, theta, u) ((q, phi), v) ->
  exists phi' v',
    moveA' ((q, phi), v) a ((q', phi'), v') /\
    config_R_config' (q', theta', u') ((q', phi'), v').
Proof.
  intros d theta' u'.
  intros HmA HR.
  inversion HmA as [tst asgn com z zth uu q1 q2 a' d' th1 th2
    HrA Htst EQth' Hfrs_m [EQq1 EQth1 EQu] EQa' EQd' [EQq2 EQth2 EQu']].
  clear q1 EQq1 th1 EQth1 a' EQa' d' EQd' q2 EQq2 th2 EQth2.
  assert (Hfresh': freshness_p_on_stack theta' u).
  { rewrite EQth'. rewrite<- EQu.
  rewrite<- EQu in Hproper.
  rewrite<- EQu in Hfresh.
  now apply moveA_keeps_freshness_p_when_skip with tst. }

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
  { rewrite EQth'.
  apply (update_has_weak_freshness_p th1 theta z d tst asgn uu);
  now try rewrite EQth1. }

  (* phi3 *)
  assert (HtstEQth' := conj Htst EQth').
  apply ex_intro with (x := d) in HtstEQth' .
  apply meanings_of_Phi_tst_asgn in HtstEQth'.
  destruct HtstEQth' as [phi3 [Heq_phi3 [Htst_phi3 Hphi3]]].

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
  now apply ruleA'_pop with (tst := tst) (asgn := asgn).

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
  now apply ruleA'_skip with (tst := tst) (asgn := asgn).

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
  now apply ruleA'_push with (tst := tst) (asgn := asgn).

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
    moveA' ((q, phi), v) a ((q', phi'), v') ->
    config_R_config' (q, theta, u) ((q, phi), v) ->
  exists d theta' u',
    moveA (q, theta, u) a d (q', theta', u') /\
    config_R_config' (q', theta', u') ((q', phi'), v').
Proof.
  intros phi' v'.
  intros HmA' HR.

  inversion HmA' as [q1 q2 a' phi1 vv com' HrA' [EQq1 EQv] EQa' [EQq2 EQv']].
  clear q1 EQq1 q2 EQq2 a' EQa'.

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
  [q1 phi'' a' phi1' q2 phi3 tst asgn HrA HrAp
   [EQq1 EQphi''] EQa' EQphi1' [EQq2 EQphi'] Hcom'
  |q1 phi'' a' phi1' q2 phi3 tst asgn HrA HrAp
   [EQq1 EQphi''] EQa' EQphi1' [EQq2 EQphi'] Hcom'
  |q1 phi'' a' phi1' q2 phi3 tst asgn j' HrA HrAp
   [EQq1 EQphi''] EQa' EQphi1' [EQq2 EQphi'] Hcom'];
  clear q1 EQq1 q2 EQq2 a' EQa' phi'' EQphi'' phi1' EQphi1';
  rewrite<- Hcom' in EQv';
  rewrite<- Hcom' in HrA';
  clear com' Hcom';
  destruct HrAp as [Hphi_1 [Hphi_3 [Htst_phi3 P3eq]]];
  assert (H := updater_must_exist
    theta z tst asgn th1 u phi phi3
    Hphi Htst_phi3 P3eq Hphi_3);
  destruct H as [d [Htst Hfrs_m]];

  (* EQth': theta' = update theta asgn d *)
  remember (update theta asgn d) as theta' eqn:EQth';

  (* Hfresh': freshness_p_on_stack theta' u *)
  rewrite EQu in Hproper;
  rewrite EQu in Hfresh;
  rewrite EQu in Hfrs_m;
  apply (moveA_keeps_freshness_p_when_skip theta th1 d z uu tst asgn
  Htst Hproper Hfrs_m)
  in Hfresh as Hfresh';
  rewrite<- EQth' in Hfresh';

  (* Hphi3: (theta, z, theta') |= phi3 *)
  assert (Htst_th' := conj Htst EQth');
  apply ex_intro with (x := d) in Htst_th';
  apply meanings_of_Phi_tst_asgn in Htst_th';
  destruct Htst_th' as [phi3' [P3'eq [Htst_phi3' Hphi3]]];
  apply (double_models_means_composableT th1 theta theta' z phi phi3'
    Hphi) in Hphi3 as Hphi_3';
  assert (EQphi3' := conj Hphi_3' Htst_phi3');
  apply (at_most_one_Phi_tst_asgn tst asgn phi phi3 phi3'
  (conj P3eq P3'eq) (conj Hphi_3 Htst_phi3)) in EQphi3';
  rewrite<- EQphi3' in Hphi3;
  clear phi3' EQphi3' P3'eq Htst_phi3' Hphi_3';

  (* weak_freshness_p th1 z theta theta' *)
  assert (Hwfrs := update_has_weak_freshness_p th1 theta z d tst asgn uu
    Htst Hfrs_m);
  rewrite<- EQth' in Hwfrs.

  - (* com' = skip' -> ... *)
  exists d.
  exists theta'.
  exists (update_stack u theta' skip).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with tst asgn.

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
  exists d.
  exists theta'.
  exists (update_stack u theta' pop).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with tst asgn.

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

  unfold freshness_p_on_moveA in Hfrs_m.

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
  exists d.
  exists theta'.
  exists (update_stack u theta' (push j')).
  rewrite EQu.
  split.
  + (* moveA ... *)
  now apply MoveA with tst asgn.

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

Section Start_config.

Variable q0 : Q.
Hypothesis EQth0 : theta_0 = theta_bot.
Hypothesis EQd0  : d_0 = bot.
Lemma start_configs_satisfy_R :
  config_R_config'
    (q0, theta_bot, ((bot, theta_bot) :: nil))
    ((q0, phi_zero), (phi_zero :: nil)).
Proof.
  assert (H: (theta_bot, bot, theta_bot) |= phi_zero).
  { unfold models.
  unfold two_Theta_D_models_Phi.
  unfold theta_bot.
  unfold phi_zero.
  now repeat split.
  }
  apply Config_R_config'.
  apply Stack_R_stack'_cons;
  [| apply Stack_R_stack'_nil];
  try rewrite EQth0;
  try rewrite EQd0;
  auto.
Qed.

End Start_config.

End RPDA_to_PDA.
