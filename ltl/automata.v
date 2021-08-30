Require Import mu.
Require Import monotonic.

Inductive ra_ltl : ltl -> Prop :=
  | ra_ltl_OR :
      forall v v' : V,
      ra_ltl (var v .\/ var v')
  | ra_ltl_X :
      forall (v : V) (phi : ltl_phi),
      ra_ltl (X (var v) ./\ phi)
  | ra_ltl_STORE_X :
      forall r (v : V) (phi : ltl_phi),
      ra_ltl ((↓ r, X (var v)) ./\ phi)
  | ra_ltl_PHI :
      forall (phi : ltl_phi),
      ra_ltl (φ phi)
  .

Inductive SigmaE :=
  | epsilon
  | Σφ (phi : ltl_phi)
  .
Inductive regSet :=
  | reg_empty
  | reg (r : register)
  .
Inductive ruleA (sigma : eqn_sys)
  : ltl -> SigmaE -> regSet -> ltl -> Prop :=
  | ruleA_PHI :
    forall phi : ltl_phi,
    ruleA sigma (φ phi) (Σφ phi) reg_empty (φ [tt])
  | ruleA_OR_left :
    forall v1 v2 : V,
    ruleA sigma (var v1 .\/ var v2) epsilon reg_empty (sigma v1)
  | ruleA_OR_right :
    forall v1 v2 : V,
    ruleA sigma (var v1 .\/ var v2) epsilon reg_empty (sigma v2)
  | ruleA_X :
    forall (v : V) (phi : ltl_phi),
    ruleA sigma (X (var v) ./\ phi) (Σφ phi) reg_empty (sigma v)
  | ruleA_STORE_X :
    forall r (v : V) (phi : ltl_phi),
    ruleA sigma ((↓ r, X (var v)) ./\ phi) (Σφ phi) (reg r) (sigma v)
  | ruleA_NOTEND :
    ruleA sigma (φ ~[END]) (Σφ [tt]) reg_empty (φ [tt])
  .

Definition Config := (ltl * Theta * data_word)%type.

Inductive moveA (sigma : eqn_sys)
  : Config -> Config -> Prop :=
  | moveA_epsilon :
    forall q1 q2 theta w,
    ruleA sigma q1 epsilon reg_empty q2 ->
    moveA sigma (q1, theta, w) (q2, theta, w)
  | moveA_not_update :
    forall q1 q2 phi theta h t,
    ruleA sigma q1 (Σφ phi) reg_empty q2 ->
    models_phi (h::t) theta phi ->
    moveA sigma (q1, theta, h::t) (q2, theta, t)
  | moveA_update :
    forall q1 q2 phi r theta a t,
    ruleA sigma q1 (Σφ phi) (reg r) q2 ->
    models_phi (a::t) theta phi ->
    moveA sigma (q1, theta, a::t) (q2, update theta r (snd a), t)
  .

Inductive moveA_star (sigma : eqn_sys)
  : Config -> Config -> Prop :=
  | moveA_star_ref :
    forall q1,
    moveA_star sigma q1 q1
  | moveA_star_trans :
    forall q1 q2 q3,
    moveA sigma q1 q2 -> moveA_star sigma q2 q3 ->
    moveA_star sigma q1 q3
  .

Inductive finalA
  : ltl -> Prop :=
  | finalA_tt  : finalA (φ [tt])
  | finalA_END : finalA (φ [END])
  | finalA_not_p : forall a, finalA (φ ~[p a])
  | finalA_not_MATCH : forall r, finalA (φ ~[↑ r])
  .

Lemma tt_loop_exists :
  forall sigma theta w,
  moveA_star sigma (φ [tt], theta, w) (φ [tt], theta, nil).
Proof.
  intros sigma theta w.
  induction w.
  - apply moveA_star_ref.
  - apply (moveA_star_trans sigma _ (φ [tt], theta, w)).
  + apply moveA_not_update with (phi := [tt]).
  * apply ruleA_PHI.
  * now unfold models_phi.
  + trivial.
Qed.

Theorem sigma_to_A_1 :
  forall sigma : eqn_sys,
  (forall v : V, ra_ltl (sigma v)) ->
  forall l w v theta,
  (w, theta |= Fpow_emp sigma l, sigma v) ->
  exists theta' qF,
  finalA qF /\
  moveA_star sigma (sigma v, theta, w) (qF, theta', nil).
Proof.
  intros sigma Hra.
  intros l.
  induction l.
  - (* l = 0 -> ... *)
  intros w.
  destruct w as [| a w].
  + (* w = nil -> ... *)
  intros v theta Hw.
  inversion Hw
  as [w th u phi Hmo EQu EQw EQth EQphi
     | | 
     | w th u psi phi Hpsi Hmo EQu EQw EQth EQpsi
     | w th u psi1 psi2 Hmo EQu EQw EQth EQpsi
     | w th u psi Hmo EQu EQw EQth EQpsi
     | w th u phi psi Hmo EQu EQw EQth EQpsi
     | w th u v' Hmo EQu EQw EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  destruct phi.
  -- (* sigma v = φ [l] -> ... *)
  unfold models_phi in Hmo.
  destruct l.
  ++ (* sigma v = φ [tt] -> ... *)
  exists theta.
  exists (φ [tt]).
  split.
  ** apply finalA_tt.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ [↑ r] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ [p a] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ [END] -> ... *)
  exists theta.
  exists (φ [END]).
  split.
  ** apply finalA_END.
  ** apply moveA_star_ref.
  -- (* sigma v = φ ~[l] -> ... *)
  unfold models_phi in Hmo.
  destruct l.
  ++ (* sigma v = φ ~[tt] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ ~[↑ r] -> ... *)
  exists theta.
  exists (φ ~[↑ r]).
  split.
  ** apply finalA_not_MATCH.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ ~[p a] -> ... *)
  exists theta.
  exists (φ ~[p a]).
  split.
  ** apply finalA_not_p.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ ~[END] -> ... *)
  now unfold models_atom in Hmo.
  * (* sigma v = psi ./\ phi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|].
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi.
  * (* sigma v = psi1 .\/ psi2 -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  destruct Hmo as [Hmo | Hmo].
  -- (* (nil, theta |= empty_env, var v1) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H].
  now unfold empty_env in H.
  -- (* (nil, theta |= empty_env, var v2) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H].
  now unfold empty_env in H.
  * (* sigma v = G psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  + (* w = a::w -> ... *)
  intros v theta Hw.
  inversion Hw
  as [w' th u phi Hmo EQu EQw' EQth EQphi
     | h t th u r psi Hmo EQu [EQh EQt] EQth EQpsi
     | h t th u psi Hmo EQu [EQh EQt] EQth EQpsi 
     | w' th u psi phi Hpsi Hmo EQu EQw' EQth EQpsi
     | w' th u psi1 psi2 Hmo EQu EQw' EQth EQpsi
     | w' th u psi Hmo EQu EQw' EQth EQpsi
     | w' th u phi psi Hmo EQu EQw' EQth EQpsi
     | w' th u v' Hmo EQu EQw' EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  destruct phi.
  -- (* sigma v = φ [l] -> ... *)
  unfold models_phi in Hmo.
  exists theta.
  exists (φ [tt]).
  destruct l;
  split; try apply finalA_tt.
  ++ (* sigma v = φ [tt] -> ... *)
  apply tt_loop_exists.
  ++ (* sigma v = φ [↑ r] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [↑ r]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ [p a] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [p a0]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ [END] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [END]); auto.
  apply ruleA_PHI.
  -- (* sigma v = φ ~[l] -> ... *)
  unfold models_phi in Hmo.
  exists theta.
  exists (φ [tt]).
  destruct l;
  split; try apply finalA_tt.
  ++ (* sigma v = φ ~[tt] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ ~[↑ r] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[↑ r]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ ~[p a0] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[p a0]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ ~[END] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[END]); auto.
  apply ruleA_PHI.
  * (* sigma v = ↓ r, psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = X psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = psi ./\ phi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|];
  clear w' EQw' u EQu th EQth phi0 EQphi0.
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| | h t th' u' psi' Hmo' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear h EQh t th' EQth' EQt u' EQu' psi' EQpsi'.
  inversion Hmo'
  as [| | | | | | |w' th' u v1 Hf EQu EQw' EQth' EQv1].
  now unfold Fpow_emp in Hf.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| h t th' u' r' psi' Hmo' EQu' [EQh EQt] EQth' [EQr' EQpsi'] | | | | | |].
  clear h EQh t th' EQth' EQt u' EQu' r' EQr' psi' EQpsi'.
  inversion Hmo'
  as [| | h t th' u' psi' Hmo'' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear h EQh t th' EQth' EQt u' EQu' psi' EQpsi'.
  inversion Hmo''
  as [| | | | | | |w' th' u v1 Hf EQu EQw' EQth' EQv1].
  now unfold Fpow_emp in Hf.
  * (* sigma v = psi1 .\/ psi2 -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  clear w' EQw' th EQth u EQu.
  destruct Hmo as [Hmo | Hmo].
  -- (* (a::w, theta |= empty_env, var v1) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H].
  now unfold empty_env in H.
  -- (* (a::w, theta |= empty_env, var v2) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H].
  now unfold empty_env in H.
  * (* sigma v = G psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  - (* inductive step on l *)
  intros w.
  destruct w as [| a w].
  + (* w = nil -> ... *)
  intros v theta Hw.
  inversion Hw
  as [w th u phi Hmo EQu EQw EQth EQphi
     | | 
     | w th u psi phi Hpsi Hmo EQu EQw EQth EQpsi
     | w th u psi1 psi2 Hmo EQu EQw EQth EQpsi
     | w th u psi Hmo EQu EQw EQth EQpsi
     | w th u phi psi Hmo EQu EQw EQth EQpsi
     | w th u v' Hmo EQu EQw EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  destruct phi.
  -- (* sigma v = φ [l0] -> ... *)
  unfold models_phi in Hmo.
  destruct l0.
  ++ (* sigma v = φ [tt] -> ... *)
  exists theta.
  exists (φ [tt]).
  split.
  ** apply finalA_tt.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ [↑ r] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ [p a] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ [END] -> ... *)
  exists theta.
  exists (φ [END]).
  split.
  ** apply finalA_END.
  ** apply moveA_star_ref.
  -- (* sigma v = φ ~[l0] -> ... *)
  unfold models_phi in Hmo.
  destruct l0.
  ++ (* sigma v = φ ~[tt] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ ~[↑ r] -> ... *)
  exists theta.
  exists (φ ~[↑ r]).
  split.
  ** apply finalA_not_MATCH.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ ~[p a] -> ... *)
  exists theta.
  exists (φ ~[p a]).
  split.
  ** apply finalA_not_p.
  ** apply moveA_star_ref.
  ++ (* sigma v = φ ~[END] -> ... *)
  now unfold models_atom in Hmo.
  * (* sigma v = psi ./\ phi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|].
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi.
  * (* sigma v = psi1 .\/ psi2 -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  destruct Hmo as [Hmo | Hmo].
  -- (* (nil, theta |= Fpow sigma (S l), var v1) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl nil v1 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v1, theta, nil));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  -- (* (nil, theta |= Fpow sigma (S l), var v2) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl nil v2 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v2, theta, nil));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_right.
  * (* sigma v = G psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  + (* w = a::w -> ... *)
  intros v theta Hw.
  inversion Hw
  as [w' th u phi Hmo EQu EQw' EQth EQphi
     | h t th u r psi Hmo EQu [EQh EQt] EQth EQpsi
     | h t th u psi Hmo EQu [EQh EQt] EQth EQpsi 
     | w' th u psi phi Hpsi Hmo EQu EQw' EQth EQpsi
     | w' th u psi1 psi2 Hmo EQu EQw' EQth EQpsi
     | w' th u psi Hmo EQu EQw' EQth EQpsi
     | w' th u phi psi Hmo EQu EQw' EQth EQpsi
     | w' th u v' Hmo EQu EQw' EQth EQpsi].
  * (* sigma v = φ phi -> ... *)
  destruct phi.
  -- (* sigma v = φ [l0] -> ... *)
  unfold models_phi in Hmo.
  exists theta.
  exists (φ [tt]).
  destruct l0;
  split; try apply finalA_tt.
  ++ (* sigma v = φ [tt] -> ... *)
  apply tt_loop_exists.
  ++ (* sigma v = φ [↑ r] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [↑ r]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ [p a] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [p a0]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ [END] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := [END]); auto.
  apply ruleA_PHI.
  -- (* sigma v = φ ~[l0] -> ... *)
  unfold models_phi in Hmo.
  exists theta.
  exists (φ [tt]).
  destruct l0;
  split; try apply finalA_tt.
  ++ (* sigma v = φ ~[tt] -> ... *)
  now unfold models_atom in Hmo.
  ++ (* sigma v = φ ~[↑ r] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[↑ r]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ ~[p a0] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[p a0]); auto.
  apply ruleA_PHI.
  ++ (* sigma v = φ ~[END] -> ... *)
  apply (moveA_star_trans _ _ (φ [tt], theta, w));
  try apply tt_loop_exists.
  apply moveA_not_update with (phi := ~[END]); auto.
  apply ruleA_PHI.
  * (* sigma v = ↓ r, psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = X psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = psi ./\ phi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'
  as [| v0 phi0 [EQv0 EQphi0]| r v0 phi0 [EQv0 EQphi0]|];
  clear w' EQw' u EQu th EQth phi0 EQphi0.
  -- (* sigma v = X (var v0) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| | h t th' u' psi' Hmo' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear h EQh t th' EQth' EQt u' EQu' psi' EQpsi'.
  inversion Hmo'
  as [| | | | | | |w' th' u v1 Hf EQu EQw' EQth' EQv1].
  clear w' EQw' th' EQth' u EQu v1 EQv1.
  assert (IHl' := IHl w v0 theta Hf).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v0, theta, w));
  auto.
  apply moveA_not_update with (phi := phi);
  auto.
  apply ruleA_X.
  -- (* sigma v = (↓ r, X (var v0)) ./\ phi -> ... *)
  rewrite <- EQv0 in Hpsi.
  inversion Hpsi
  as [| h t th' u' r' psi' Hmo' EQu' [EQh EQt] EQth' [EQr' EQpsi'] | | | | | |].
  clear h EQh t th' EQth' EQt u' EQu' r' EQr' psi' EQpsi'.
  inversion Hmo'
  as [| | h t th' u' psi' Hmo'' EQu' [EQh EQt] EQth' EQpsi'| | | | |].
  clear h EQh t th' EQth' EQt u' EQu' psi' EQpsi'.
  inversion Hmo''
  as [| | | | | | |w' th' u v1 Hf EQu EQw' EQth' EQv1].
  assert (IHl' := IHl w v0 (update theta r (snd a)) Hf).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v0, (update theta r (snd a)), w));
  auto.
  apply moveA_update with (phi := phi);
  auto.
  apply ruleA_STORE_X.
  * (* sigma v = psi1 .\/ psi2 -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra' as [v1 v2 [EQpsi1 EQpsi2]| | |].
  (* sigma v = var v1 .\/ var v2 -> ... *)
  rewrite <- EQpsi1 in Hmo.
  rewrite <- EQpsi2 in Hmo.
  unfold Fpow_emp in Hmo.
  unfold Fpow in Hmo.
  clear w' EQw' th EQth u EQu.
  destruct Hmo as [Hmo | Hmo].
  -- (* (a::w, theta |= Fpow sigma (S l), var v1) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl (a::w) v1 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v1, theta, a::w));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  -- (* (a::w, theta |= Fpow sigma (S l), var v2) -> ... *)
  inversion Hmo as [| | | | | | |w' th' u' v' H EQu' EQw' EQth' EQv'].
  clear w' EQw' th' EQth' u' EQu' v' EQv'.
  assert (IHl' := IHl (a::w) v2 theta H).
  destruct IHl' as [theta' [qF [Hfin Hmv]]].
  exists theta'.
  exists qF.
  split; auto.
  apply (moveA_star_trans _ _ (sigma v2, theta, a::w));
  auto.
  apply moveA_epsilon.
  apply ruleA_OR_right.
  * (* sigma v = G psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = phi U psi -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
  * (* sigma v = var v' -> ... *)
  assert (Hra' := Hra v).
  rewrite <- EQpsi in Hra'.
  inversion Hra'.
Qed.
