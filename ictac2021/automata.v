(*
 * Usage: You may need "make equiv.vo" before
 * using this file.
 * In vscode, you may also need to add
 * "coqtop.args": [ "-Q", "/path/to/this/dir", "" ]
 * to settings.json.
 *)

Require Import equiv.
Require Import Lists.List.

(* Rules of RPDA A and PDA A' *)

Local Open Scope type_scope.  (* for '*' *)

Parameter Sigma : Set.  (* finite alphabet *)

Parameter Q : Set.  (* finite control states *)
Definition Q' := Q * Phi.

Inductive Com :=
  | pop
  | skip
  | push (j : nat).
Inductive Com' :=
  | pop'
  | skip'
  | push' (phi : Phi).

Parameter ruleA :
  Q -> Sigma -> Tst -> Q -> Asgn -> Com -> Prop.

Inductive ruleA'
  : Q' -> Sigma -> Phi -> Q' -> Com' -> Prop :=
  | ruleA'_skip :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn skip ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, compositionT phi2 phi3) skip'
  | ruleA'_pop :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn pop ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, composition phi1 (compositionT phi2 phi3)) pop'
  | ruleA'_push :
    forall q1 phi2 a phi1 q2 phi3 tst asgn j,
    ruleA q1 a tst q2 asgn (push j) ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, phi_to_Phi_eq_j j phi3) (push' (compositionT phi2 phi3)).

(* Configurations and transitions between configurations *)

Definition Stack  := list (D * Theta).
Definition Stack' := list Phi.

Definition Config  := Q  * Theta * Stack.
Definition Config' := Q' * Stack'.

Definition update_stack (u : Stack) theta com :=
  match com with
  | pop =>
    match u with
     | cons _ u' => u'
     | nil => nil
     end
  | skip => u
  | push j => cons (theta j, theta) u
  end.

Definition update_stack' (u : Stack') com' :=
  match com' with
  | pop' =>
    match u with
     | cons _ u' => u'
     | nil => nil
     end
  | skip' => u
  | push' z => cons z u
  end.

Definition freshness_p_on_moveA (tst : Tst) d (u : Stack) :=
  let not_contain_d cell :=
     match cell with (_, theta) => forall i, theta i <> d end
  in (forall xi, tst xi <> true) ->
     Forall not_contain_d u.

Inductive moveA
  : Config -> Sigma -> D -> Config -> Prop :=
  | MoveA :
    forall tst asgn com z zth u q1 q2 a d theta theta',
    ruleA q1 a tst q2 asgn com ->
    (theta, d, z) |= tst ->
    theta' = update theta asgn d ->
    freshness_p_on_moveA tst d (cons (z, zth) u) ->
    moveA (q1, theta,  (cons (z, zth) u)) a d
          (q2, theta', update_stack (cons (z, zth) u) theta' com).

Inductive moveA'
  : Config' -> Sigma -> Config' -> Prop :=
  | MoveA' :
    forall q1 q2 a z u com',
    ruleA' q1 a z q2 com' ->
    moveA' (q1, (cons z u)) a
           (q2, update_stack' (cons z u) com').

Definition is_proper_stack (stack : Stack) :=
  let is_proper_cell cell :=
    match cell with (z, theta) => exists i, z = theta i end
  in Forall is_proper_cell stack.

(* Bisimulation relation between configs *)

Inductive stack_R_stack'
  : Theta -> Stack -> Phi -> Stack' -> Prop :=
  | Stack_R_stack'_nil :
    forall theta phi,
    (theta_bot, bot, theta) |= phi ->
    stack_R_stack' theta nil phi nil
  | Stack_R_stack'_cons :
    forall theta ptheta d phi pphi u v,
    (ptheta, d, theta) |= phi ->
    stack_R_stack' ptheta u pphi v ->
    stack_R_stack' theta (cons (d, ptheta) u) phi (cons pphi v).

Inductive config_R_config'
  : Config -> Config' -> Prop :=
  | Config_R_config' :
    forall q theta u phi v,
    stack_R_stack' theta u phi v ->
    config_R_config' (q, theta, u) ((q, phi), v).

(* freshness_p on stack *)

Inductive Forall2 {X : Type} (P : X -> X -> Prop)
  : list X -> Prop :=
  | Forall2_nil : Forall2 P nil
  | Forall2_cons x l :
    Forall (P x) l -> Forall2 P l -> Forall2 P (x :: l).

Inductive Forall3 {X : Type} (P : X -> X -> X -> Prop)
  : list X -> Prop :=
  | Forall3_nil : Forall3 P nil
  | Forall3_cons x l :
    Forall2 (P x) l -> Forall3 P l -> Forall3 P (x :: l).

Definition freshness_p_on_triple
  (p3 p2 p1 : D * Theta) :=
  match (p3, p2, p1) with
    ((_, th3), (_, th2), (d, th1))
    => freshness_p th1 d th2 th3
  end.

Definition freshness_p_on_stack theta stack :=
  Forall3 freshness_p_on_triple ((bot, theta) :: stack).

Example forall2_example_1 :
  Forall2 le (0 :: 1 :: 3 :: 8 :: nil).
Proof.
  repeat apply Forall2_cons;
  repeat apply Forall_cons;
  repeat (apply le_S; try apply le_n); auto;
  try apply Forall2_nil.
Qed.

(* Lemmas *)

(* Forall, Forall2, Forall3 *)

Lemma Forall_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall p (u1 ++ (a :: u2)) ->
  Forall p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor.
  inversion Hfor as [| x l Hpa Hfor' [EQx EQl]].
  exact Hfor'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor.
  inversion Hfor as [| x l Hpb Hfor' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall_cons; auto.
Qed.

Lemma Forall2_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall2 p (u1 ++ (a :: u2)) ->
  Forall2 p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor2.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  exact Hfor2'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor2.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall2_cons.
  + (* Forall ... *)
  apply Forall_sublist with a; auto.
  + (* Forall2 ... *)
  apply IHu1; auto.
Qed.

Lemma Forall3_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall3 p (u1 ++ (a :: u2)) ->
  Forall3 p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  exact Hfor3'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall3_cons.
  + (* Forall ... *)
  apply Forall2_sublist with a; auto.
  + (* Forall2 ... *)
  apply IHu1; auto.
Qed.

Lemma Forall2_hd2 {A : Type} :
  forall p (a : A) b u,
  Forall2 p (a :: b :: u) ->
  p a b.
Proof.
  intros p a b u H.
  inversion H as [| x l Hfor Hfor2 [EQx EQl]].
  clear x EQx l EQl H Hfor2.
  inversion Hfor as [| x l H Hfor' [EQx EQl]].
  exact H.
Qed.

Lemma Forall3_hd3 {A : Type} :
  forall p (a : A) b c u,
  Forall3 p (a :: b :: c :: u) ->
  p a b c.
Proof.
  intros p a b c u H.
  inversion H as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x EQx l EQl Hfor3' H.
  apply Forall2_hd2 with u.
  exact Hfor2.
Qed.
 
(* is_proper_stack *)

Lemma substack_is_proper_stack :
  forall a u1 u2,
  is_proper_stack (u1 ++ (a :: u2)) ->
  is_proper_stack (u1 ++ u2).
Proof.
  apply Forall_sublist.
Qed.

(* freshness_p_on_stack *)

Lemma substack_keeps_freshness_p_0 :
  forall theta d th u,
  freshness_p_on_stack theta ((d, th) :: u) ->
  freshness_p_on_stack th u.
Proof.
  intros theta d th u.
  unfold freshness_p_on_stack.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x l EQx EQl Hfor3.
  inversion Hfor3' as [| x l Hfor2' Hfor3 [EQx EQl]].
  clear x l EQx EQl Hfor3'.
  apply Forall3_cons; auto.
Qed.

Lemma substack_keeps_freshness_p :
  forall theta a u1 u2,
  freshness_p_on_stack theta (u1 ++ (a :: u2)) ->
  freshness_p_on_stack theta (u1 ++ u2).
Proof.
  intros theta a u1 u2.
  unfold freshness_p_on_stack.
  repeat rewrite app_comm_cons.
  apply Forall3_sublist.
Qed.

Lemma push_keeps_freshness_p :
  forall theta u z,
  freshness_p_on_stack theta u ->
  freshness_p_on_stack theta ((z, theta) :: u).
Proof.
  intros theta u z.
  unfold freshness_p_on_stack.
  intros H.
  apply Forall3_cons.
  - (* Forall2 ... ((z, theta) :: u) *)
  apply Forall2_cons.
  + (* Forall ... u *)
  apply Forall_forall.
  intros [d1 th1] Hth1.
  unfold freshness_p_on_triple.
  unfold freshness_p.
  split.
  * (* forall i j, th1 i = ... -> ... *)
  intros i j H1.
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  inversion Hfor2 as [EQu | x l Hfor Hfor2' EQx].
  -- (* u = nil -> ... *)
  rewrite<- EQu in Hth1.
  apply in_nil in Hth1.
  contradiction.
  -- (* u = x :: l -> ... *)
  exists j.
  exact H1.
  * (* forall j, d1 = ... -> ... *)
  intros j H1.
  exists j.
  exact H1.
  + (* Forall2 ... u *)
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  exact Hfor2.

  - (* Forall3 ... ((theta j, ) :: u) *)
  apply Forall3_cons.
  + (* Forall2 ... u *)
  induction u as [| [d1 th1] u IHu].
  * (* u = nil -> ... *)
  apply Forall2_nil.
  * (* u = (d1, th1) :: u -> ... *)
  apply Forall2_cons.
  -- (* Forall ... u *)
  apply Forall_forall.
  intros [d2 th2] Hth2.
  unfold freshness_p_on_triple.
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  clear x EQx l EQl Hfor2 Hfor2'.
  rewrite Forall_forall in Hfor.
  unfold freshness_p_on_triple in Hfor.
  apply (Hfor (d2, th2)).
  exact Hth2.
  -- (* Forall2 ... u *)
  apply IHu.
  apply (Forall3_sublist _ (d1, th1) ((bot, theta) :: nil)).
  unfold app.
  exact H.
  + (* Forall3 ... u *)
  apply (Forall3_sublist _ (bot, theta) nil).
  unfold app.
  exact H.
Qed.

(* freshness_p_on_moveA *)

Lemma substack_keeps_freshness_p_on_moveA :
  forall tst d a u1 u2,
  freshness_p_on_moveA tst d (u1 ++ (a :: u2)) ->
  freshness_p_on_moveA tst d (u1 ++ u2).
Proof.
  intros tst d a u1 u2.
  unfold freshness_p_on_moveA.
  intros Hfrs Htst.
  assert (Hfrs' := Hfrs Htst).
  generalize Hfrs'.
  apply (Forall_sublist _ a).
Qed.

(* moveA *)

Lemma keeping_freshness_p_when_skip :
  forall theta zth d z u tst asgn,
  (theta, d, z) |= tst ->
  is_proper_stack ((z, zth) :: u) ->
  freshness_p_on_moveA tst d ((z, zth) :: u) ->
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
  apply Hfrs_m in Htst_empty as Hfrs_m'.
  rewrite Forall_forall in Hfrs_m'.
  assert (Hth2' : In (d2, th2) ((z, zth) :: u)).
  { apply in_cons. exact Hth2. }
  assert (Hm := Hfrs_m' (d2, th2) Hth2').
  simpl in Hm.

  unfold freshness_p_on_triple.
  unfold freshness_p.
  split.
  ** (* forall i j, th1 i = update ... -> ... *)
  intros i j.
  unfold update.
  case (asgn j); intros EQth2.
  +++ (* asgn j = true -> ... *)
  apply Hm in EQth2.
  contradiction.
  +++ (* asgn j = false -> ... *)
  apply H1 with j.
  exact EQth2.
  ** (* forall j, d1 = update ... -> ... *)
  intros j.
  unfold update.
  case (asgn j); intros EQd2.
  +++ (* asgn j = true -> ... *)
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
  freshness_p_on_moveA tst d ((z, zth) :: u) ->
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
  -- intros i j Hth1. exists j; auto.
  -- intros j Hd1. exists j; auto.

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
  -- apply (substack_is_proper_stack (d1, th1) ((z, zth) :: nil)); auto.
  -- apply (substack_keeps_freshness_p_on_moveA _ _ (d1,th1) ((z,zth)::nil));
     auto.
  -- apply (Forall3_sublist _ (d1, th1) ((bot,theta)::(z,zth)::nil)); auto.

  - (* Forall3 ... ((z, zth) :: u) *)
  apply (Forall3_sublist _ (bot, theta) nil); auto.
Qed.


Lemma moveA_inversion :
  forall q q' theta theta' u u' a d,
  moveA (q, theta, u) a d (q', theta', u') ->
  exists tst asgn com z zth uu,
  ruleA q a tst q' asgn com /\
  u = cons (z, zth) uu /\
  (theta, d, z) |= tst /\
  theta' = update theta asgn d /\
  u' = update_stack u theta' com /\
  freshness_p_on_moveA tst d u.
Proof.
  intros q q' theta theta' u u' a d.
  intros Hm.
  inversion Hm as [tst asgn com z zth uu].
  exists tst, asgn, com, z, zth, uu.
  split; [| split]; auto.
Qed.

Lemma no_moveA_on_nil :
  forall q q' theta theta' a d v',
  ~ moveA (q, theta, nil) a d (q', theta', v').
Proof.
  intros q q' theta theta' a d v'.
  intro H.
  inversion H.
Qed.

Lemma moveA_keeps_proper_stack :
  forall q theta u a d q' theta' u',
  moveA (q, theta, u) a d (q', theta', u') ->
  is_proper_stack u ->
  is_proper_stack u'.
Proof.
  intros q theta u a d q' theta' u'.
  intros HmA Hproper.
  apply moveA_inversion in HmA as HrA.
  destruct HrA
  as [tst [asgn [com [z [zth [uu [HrA [EQu [Htst [EQth' [EQu' Hfrs_m]]]]]]]]]]].
  case_eq com;
  [intros Hcom | intros Hcom | intros j Hcom];
  rewrite Hcom in EQu';
  rewrite Hcom in HrA;
  clear com Hcom;
  rewrite EQu in EQu';
  unfold update_stack in EQu'.
  - (* com = pop -> ... *)
  rewrite<- EQu' in EQu.
  clear uu EQu'.
  unfold is_proper_stack.
  unfold is_proper_stack in Hproper.
  rewrite EQu in Hproper.
  inversion Hproper as [| x l Hz Hproper_u' [EQx EQl]].
  apply Hproper_u'.
  - (* com = skip -> ... *)
  rewrite<- EQu' in EQu.
  clear uu EQu'.
  rewrite<- EQu.
  exact Hproper.
  - (* com = push -> ... *)
  rewrite<- EQu in EQu'.
  clear uu EQu.
  rewrite EQu'.
  unfold is_proper_stack.
  apply Forall_cons.
  { exists j; reflexivity. }
  unfold is_proper_stack in Hproper.
  exact Hproper.
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
  apply moveA_inversion in HmA as HrA.
  destruct HrA
  as [tst [asgn [com [z [zth [uu [HrA [EQu [Htst [EQth' [EQu' Hfrs_m]]]]]]]]]]].

  assert (Hskip: freshness_p_on_stack theta' u).
  { rewrite EQth'. rewrite EQu.
  apply moveA_keeps_freshness_p_when_skip with tst;
  try rewrite<- EQu; auto.
  }

  case_eq com;
  [intros Hcom | intros Hcom | intros j Hcom];
  rewrite Hcom in EQu';
  rewrite Hcom in HrA;
  clear com Hcom;
  rewrite EQu in EQu';
  unfold update_stack in EQu'.
  - (* com = pop -> ... *)
  rewrite<- EQu' in EQu.
  apply (substack_keeps_freshness_p _ (z, zth) nil).
  unfold app.
  rewrite<- EQu.
  exact Hskip.
  - (* com = skip -> ... *)
  rewrite<- EQu' in EQu.
  rewrite<- EQu.
  exact Hskip.
  - (* com = push -> ... *)
  rewrite<- EQu in EQu'.
  clear uu EQu.
  rewrite EQu'.
  apply push_keeps_freshness_p.
  exact Hskip.
Qed.

(* config_R_config' *)

Lemma config_R_nil_nil_1 :
  forall q theta u phi,
  config_R_config' (q, theta, u) (q, phi, nil) ->
  u = nil.
Proof.
  intros q theta u phi.
  intro H.
  inversion H as [q1 theta1 u1 phi1 v1 HR].
  inversion HR.
  reflexivity.
Qed.

Lemma config_R_nil_nil_2 :
  forall q theta v phi,
  config_R_config' (q, theta, nil) (q, phi, v) ->
  v = nil.
Proof.
  intros q theta v phi.
  intro H.
  inversion H as [q1 theta1 u1 phi1 v1 HR].
  inversion HR.
  reflexivity.
Qed.

(* Theorem on bisimilarity *)

Lemma bisimilar_1 :
  forall q theta_n phi_n u v,
  forall a d q' theta' u',
    moveA (q, theta_n, u) a d (q', theta', u') ->
    config_R_config' (q, theta_n, u) ((q, phi_n), v) ->
    freshness_p_on_stack theta_n u ->
    is_proper_stack u ->
    (* u = nil \/ the last element of u is (bot, theta_bot) *)
    last u (bot, theta_bot) = (bot, theta_bot) ->
    is_equiv_rel phi_n -> Forall is_equiv_rel v ->
  exists phi'' v',
    moveA' ((q, phi_n), v) a ((q', phi''), v') /\
    config_R_config' (q', theta', u') ((q', phi''), v').
Proof.
  intros q theta_n phi_n u v.
  intros a d q' theta' u'.
  intros HmA HR.
  intros Hfresh Hproper Hu_last Heq_phi_n Heq_v.
  apply moveA_inversion in HmA as HrA.
  destruct HrA as
  [tst [asgn [com [z [zth [uu [HrA [EQu [Htst [EQth' [EQu' Hfrs_m]]]]]]]]]]].
  assert (Hfresh': freshness_p_on_stack theta' u).
  { rewrite EQth'. rewrite EQu.
  rewrite EQu in Hproper.
  rewrite EQu in Hfrs_m.
  rewrite EQu in Hfresh.
  apply moveA_keeps_freshness_p_when_skip with tst;
  auto. }

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
  as [th2 phi' Hphi_n EQth2 Hu_nil |
      th2 th1 d1 phi' phi1' u1 v1 Hphi_n HsR1 EQth2 EQu1 EQphi' EQv1].
  { (* nil = u -> ... *)
  rewrite EQu in Hu_nil;
  discriminate Hu_nil.
  }
  (* ((d1, th1) :: u1) = u -> ... *)
  clear th2 EQth2 phi' EQphi'.
  rewrite EQu in EQu1.
  injection EQu1; clear EQu1.
  intros EQu1 EQth1 EQd1.
  rewrite EQu1 in HsR1; clear u1 EQu1.
  rewrite EQd1 in Hphi_n; clear d1 EQd1.
  rewrite<- EQth1 in EQu; clear zth EQth1.
  rewrite EQv in EQv1.
  injection EQv1; clear EQv1.
  intros EQv1 EQphi1'.
  rewrite EQv1 in HsR1; clear v1 EQv1.
  rewrite EQphi1' in HsR1; clear phi1' EQphi1'.

  (* composable phi1 phi_n *)
  assert (Hphi_1_n: composable phi1 phi_n).
  { inversion HsR1
  as [th2 phi1' Hphi1 EQth2 EQuu EQphi1' EQvv |
     th2 th1' d1 phi' phi1' uu1 vv1 Hphi' HsR2 EQth2 EQuu1 EQphi' EQvv1].
  -- (* nil = vv -> ... *)
  apply (double_models_means_composable theta_bot th1 theta_n bot z).
  auto.
  -- (* (phi1' :: vv1) = vv -> ... *)
  apply (double_models_means_composable th1' th1 theta_n d1 z).
  auto.
  }

  (* weak_freshness_p th1 z theta_n theta' *)
  assert (Hwfrs: weak_freshness_p th1 z theta_n theta').
  { unfold weak_freshness_p.
  intros i j.
  intros H.
  rewrite EQth' in H.
  unfold update in H.

  destruct (tst_is_empty_or_not tst)
  as [Htst_empty | Htst_not_empty].
  ++ (* tst_empty -> ... *)
  apply Hfrs_m in Htst_empty as Hfrs_m'.
  rewrite Forall_forall in Hfrs_m'.
  assert (Hzin : In (z, th1) u).
  { rewrite EQu. apply in_eq. }
  assert (Hm := Hfrs_m' (z, th1) Hzin).
  simpl in Hm.
  generalize dependent H.
  case (asgn j); intro H.
  ** (* asgn j = true -> ... *)
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
  }

  (* phi3 *)
  assert (HtstEQth' := conj Htst EQth').
  apply ex_intro with (x := d) in HtstEQth' .
  apply meanings_of_Phi_tst_asgn in HtstEQth'.
  destruct HtstEQth' as [phi3 [Heq_phi3 [Htst_phi3 Hphi3]]].

  (* composableT phi_n phi3 *)
  assert (Hphi_n_3: composableT phi_n phi3).
  { apply (double_models_means_composableT th1 theta_n theta' z);
  auto. }

  case_eq com.
  - (* com = pop -> ... *)
  intros Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (composition phi1 (compositionT phi_n phi3)).
  exists (update_stack' v pop').
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  apply ruleA'_pop with (tst := tst) (asgn := asgn);
  auto.

  + (* config_R_config' ... *)
  rewrite EQu in EQu'.
  unfold update_stack in EQu'.
  rewrite EQu'.
  rewrite EQu' in HmA.
  clear u' EQu'.

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
  clear uu EQuu.

  rewrite EQu in Hu_last.
  unfold last in Hu_last.
  injection Hu_last.
  intros EQth1 EQz.
  rewrite EQth1 in Hphi1.
  rewrite EQth1 in Hphi_n.
  rewrite EQz in Hphi_n.
  rewrite EQz in Hphi3.

  unfold freshness_p_on_moveA in Hfrs_m.

  apply Stack_R_stack'_nil.
  apply (meanings_of_composition theta_bot theta_bot theta' bot bot).
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite EQv.
  apply in_eq.
  -- (* freshness_p theta_bot bot theta_bot theta' *)
  unfold freshness_p.
  split.
  ++ intros i j H.
  exists i.
  reflexivity.
  ++ intros j H.
  exists j.
  unfold theta_bot.
  reflexivity.
  -- (* (...) |= phi1 /\ (theta_bot,bot,theta') |= compositionT phi_n phi3 *)
  split; auto.
  apply (meanings_of_compositionT theta_bot theta_n theta' bot);
  auto.
  ++ (* weak_freshness_p theta_bot bot theta_n theta' *)
  unfold weak_freshness_p.
  intros i j H.
  right.
  unfold theta_bot.
  reflexivity.

  * (* vv = phi0 :: vv -> ... *)
  inversion HsR1
  as [| th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
        EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  clear th1' EQth1' phi1' EQphi1' phi0' EQphi0' EQvv.

  apply Stack_R_stack'_cons;
  auto.
  apply (meanings_of_composition th0 th1 theta' d0 z).
  -- (* is_equiv_rel phi1 *)
  rewrite Forall_forall in Heq_v.
  apply Heq_v.
  rewrite EQv.
  apply in_eq.
  -- (* freshness_p th0 d0 th1 theta' *)
  rewrite EQu in Hfresh'.
  rewrite<- EQuu in Hfresh'.
  unfold freshness_p_on_stack in Hfresh'.
  apply Forall3_hd3 in Hfresh'.
  unfold freshness_p_on_triple in Hfresh'.
  exact Hfresh'.
  -- (* (...) |= phi1 /\ (th1, z, theta') |= compositionT ... *)
  split; auto.
  apply meanings_of_compositionT with theta_n;
  auto.

  - (* com = skip -> ... *)
  intros Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (compositionT phi_n phi3).
  exists (update_stack' v skip').
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  apply ruleA'_skip with (tst := tst) (asgn := asgn);
  auto.

  + (* config_R_config' ... *)
  rewrite EQu in EQu'.
  unfold update_stack in EQu'.
  rewrite EQu'.
  rewrite EQu' in HmA.
  clear u' EQu'.

  unfold update_stack'.
  apply Config_R_config'.

  inversion HsR1
  as [th1' phi1' Hphi1 EQth1' EQuu EQphi1' EQvv |
      th1' th0 d0 phi1' phi0' uu' vv' Hphi1 HsR2
      EQth1' EQuu EQphi1' [EQphi0' EQvv]].
  * (* nil = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1' EQvv.

  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi_n phi3 *)
  apply meanings_of_compositionT with theta_n;
  auto.
  -- (* stack_R_stack' th1 nil phi1 nil *)
  apply Stack_R_stack'_nil.
  auto.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (th1, z, theta') |= compositionT phi_n phi3 *)
  apply (meanings_of_compositionT th1 theta_n theta');
  auto.
  -- (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  apply Stack_R_stack'_cons;
  auto.

  - (* com = push j -> ... *)
  intros j Hcom.
  rewrite Hcom in EQu'.
  rewrite Hcom in HrA.
  clear com Hcom.
  exists (phi_to_Phi_eq_j j phi3).
  exists (update_stack' v (push' (compositionT phi_n phi3))).
  rewrite EQv.
  split.
  + (* moveA' ... *)
  apply MoveA'.
  apply ruleA'_push with (tst := tst) (asgn := asgn);
  auto.

  + (* config_R_config' ... *)
  rewrite EQu in EQu'.
  unfold update_stack in EQu'.
  rewrite EQu'.
  rewrite EQu' in HmA.
  clear u' EQu'.

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
  apply theta_models_phi_to_Phi_eq_j with z theta_n;
  auto.
  -- (* stack_R_stack' theta' ((z, th1) :: nil) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi_n phi3 *)
  apply meanings_of_compositionT with theta_n;
  auto.
  ++ (* stack_R_stack' th1 nil phi1 nil *)
  apply Stack_R_stack'_nil.
  auto.
  * (* phi0' :: vv' = vv -> ...*)
  clear th1' EQth1' phi1' EQphi1'.
  apply Stack_R_stack'_cons.
  -- (* (theta', theta' j, theta') |= phi_to_Phi_eq_j ... *)
  apply theta_models_phi_to_Phi_eq_j with z theta_n;
  auto.
  -- (* stack_R_stack' theta' ((z, th1) :: ...) ... *)
  apply Stack_R_stack'_cons.
  ++ (* (th1, z, theta') |= compositionT phi_n phi3 *)
  apply (meanings_of_compositionT th1 theta_n theta');
  auto.
  ++ (* stack_R_stack' th1 ((d0, th0) :: uu') ... *)
  apply Stack_R_stack'_cons;
  auto.
Qed.

Lemma bisimilar_2 :
  forall q theta_n phi_n u v,
  forall a q' phi'' v',
    moveA' ((q, phi_n), v) a ((q', phi''), v') ->
    config_R_config' (q, theta_n, u) ((q, phi_n), v) ->
    freshness_p_on_stack theta_n u ->
    is_proper_stack u ->
    (* u = nil \/ the last element of u is (bot, theta_bot) *)
    last u (bot, theta_bot) = (bot, theta_bot) ->
    is_equiv_rel phi_n -> Forall is_equiv_rel v ->
  exists d theta' u',
    moveA (q, theta_n, u) a d (q', theta', u') /\
    config_R_config' (q', theta', u') ((q', phi''), v').
Proof.
  intros q theta_n phi_n u v.
  intros a q' phi'' v'.
  intros HmA' HR.
  intros Hfresh Hproper Hu_last Heq_phi_n Heq_v.

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

  inversion HR as [q1 theta1 u1 phi' v1 HsR [EQq1 EQth1 EQu1] [EQphi' EQv1]].
  clear q1 EQq1 theta1 EQth1 u1 EQu1;
  clear phi' EQphi' v1 EQv1.
  inversion HsR
  as [th2 phi' Hphi_n EQth2 Hu_nil |
      th2 th1' d1 phi' phi1' u1 v1 Hphi_n HsR1 EQth2 EQu1 EQphi' EQv1].
  { (* nil = u -> ... *)
  rewrite EQu in Hu_nil;
  discriminate Hu_nil.
  }
  (* ((d1, th1) :: u1) = u -> ... *)
  clear th2 EQth2 phi' EQphi'.
  rewrite EQu in EQu1.
  injection EQu1; clear EQu1.
  intros EQu1 EQth1 EQd1.
  rewrite EQu1 in HsR1; clear u1 EQu1.
  rewrite EQd1 in Hphi_n; clear d1 EQd1.
  rewrite EQth1 in HsR1.
  rewrite EQth1 in Hphi_n; clear th1' EQth1.
  rewrite<- EQv in EQv1.
  injection EQv1; clear EQv1.
  intros EQv1 EQphi1'.
  rewrite EQv1 in HsR1; clear v1 EQv1.
  rewrite EQphi1' in HsR1; clear phi1' EQphi1'.

  (* composable phi1 phi_n *)
  assert (Hphi_1_n: composable phi1 phi_n).
  { inversion HsR1
  as [th2 phi1' Hphi1 EQth2 EQuu EQphi1' EQvv |
     th2 th1' d1 phi' phi1' uu1 vv1 Hphi' HsR2 EQth2 EQuu1 EQphi' EQvv1].
  -- (* nil = vv -> ... *)
  apply (double_models_means_composable theta_bot th1 theta_n bot z);
  auto.
  -- (* (phi1' :: vv1) = vv -> ... *)
  apply (double_models_means_composable th1' th1 theta_n d1 z);
  auto.
  }


Admitted.
