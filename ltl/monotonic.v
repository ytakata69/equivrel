Require Import mu.

Lemma models_is_monotonic :
  forall (u1 u2 : Env),
  (forall (v : V) (theta : Theta) (w : data_word),
   u1 v theta w -> u2 v theta w) ->
  forall (psi : ltl) (theta : Theta) (w : data_word),
  (w, theta |= u1, psi) -> (w, theta |= u2, psi).
Proof.
  intros u1 u2 Hu1u2.
  intros psi.
  induction psi; intros theta w Hm.
  - apply models_var.
  inversion Hm.
  now apply Hu1u2.
  - apply models_OR.
  inversion Hm as [| | | | w' th' u p1 p2 Ho| | |].
  destruct Ho as [Ho | Ho].
  + left; auto.
  + right; auto.
  - apply models_AND.
  inversion Hm; auto.
  inversion Hm; auto.
  - inversion Hm.
  apply models_STORE.
  now apply IHpsi.
  - inversion Hm.
  apply models_X.
  now apply IHpsi.
  - inversion Hm
  as [| | | | | | w' th' u phi psi' Hu EQu EQw'|].
  clear w' EQw'.
  destruct Hu as [w' [Hu1 Hu]].
  apply models_U.
  exists w'.
  split; auto.
  - inversion Hm.
  now apply models_PHI.
  - apply models_G.
  now inversion Hm.
Qed.

Fixpoint Fpow (sigma : eqn_sys) (i : nat) (u : Env) : Env :=
  match i with
    0   => u
  | S n => F sigma (Fpow sigma n u)
  end.
Definition Fpow_emp sigma i := Fpow sigma i empty_env.

Theorem F_is_monotonic_1 :
  forall (sigma : eqn_sys) (i : nat),
  forall v theta w,
  (Fpow_emp sigma i) v theta w -> Fpow_emp sigma (S i) v theta w.
Proof.
  intros sigma i.
  induction i.
  { intros v theta w H.
    now unfold Fpow_emp in H. }
  intros v.
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  induction (sigma v); intros theta w H.
  (* H: (w, theta |= Fpow sigma i, sigma v) *)
  + (* sigma v = var v0 -> ... *)
  apply models_var.
  apply IHi.  (* apply (IHi v0). *)
  now inversion H.
  + (* sigma v = l1 .\/ l2 -> ... *)
  apply models_OR.
  inversion H as [| | | | w' th' u p1 p2 Ho| | |].
  destruct Ho as [Ho | Ho].
  * left; auto.
  * right; auto.
  + (* sigma v = l ./\ l0 -> ... *)
  inversion H.
  apply models_AND; auto.
  + (* sigma v = ↓ r, l -> ... *)
  inversion H as [| h t th u r' psi H' EQu EQht | | | | | |].
  apply models_STORE; auto.
  + (* sigma v = X l -> ... *)
  inversion H.
  apply models_X; auto.
  + (* sigma v = l U l0 -> ... *)
  inversion H
  as [| | | | | | w' th' u phi psi' Hu EQu EQw'|].
  clear w' EQw'.
  destruct Hu as [w' [Hu' Hu]].
  apply models_U.
  exists w'.
  split; auto.
  + (* sigma v = φ l -> ... *)
  inversion H.
  now apply models_PHI.
  + (* sigma v = G l -> ... *)
  inversion H.
  now apply models_G.
Qed.

Theorem F_is_monotonic_2 :
  forall (sigma : eqn_sys) (i : nat) (Y : Env),
  (forall v theta w,
   Fpow_emp sigma i v theta w -> Y v theta w) ->
  (forall v theta w,
   Fpow_emp sigma (S i) v theta w -> F sigma Y v theta w).
Proof.
  intros sigma i Y.
  intros H0 v.
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  induction (sigma v);
  intros theta w H.
  (* H: (w, theta |= Fpow sigma i, sigma v) *)
  + (* sigma v = var v0 -> ... *)
  apply models_var.
  apply H0.
  now inversion H.
  + (* sigma v = l1 .\/ l2 -> ... *)
  apply models_OR.
  inversion H as [| | | | w' th' u p1 p2 Ho| | |].
  destruct Ho as [Ho | Ho].
  * left; auto.
  * right; auto.
  + (* sigma v = l ./\ l0 -> ... *)
  inversion H.
  apply models_AND; auto.
  + (* sigma v = ↓ r, l -> ... *)
  inversion H as [| h t th u r' psi H' EQu EQht | | | | | |].
  apply models_STORE; auto.
  + (* sigma v = X l -> ... *)
  inversion H.
  apply models_X; auto.
  + (* sigma v = l U l0 -> ... *)
  inversion H
  as [| | | | | | w' th' u phi psi' Hu EQu EQw'|].
  clear w' EQw'.
  destruct Hu as [w' [Hu' Hu]].
  apply models_U.
  exists w'.
  split; auto.
  + (* sigma v = φ l -> ... *)
  inversion H.
  now apply models_PHI.
  + (* sigma v = G l -> ... *)
  inversion H.
  now apply models_G.
Qed.

Theorem least_fixpoint_of_F :
  forall (sigma : eqn_sys) (Y : Env),
  F sigma Y = Y ->
  forall i,
  forall v theta w,
  Fpow_emp sigma i v theta w -> Y v theta w.
Proof.
  intros sigma Y HY i.
  induction i;
  intros v theta w H.
  - now unfold Fpow_emp in H.
  - rewrite<- HY.
  now apply (F_is_monotonic_2 sigma i Y IHi).
Qed.

(*
 * F_is_monotonic_1 より
 * ∅ ⊆ F ∅ ⊆ F^2 ∅ ⊆ F^3 ∅ ⊆ …
 * このω鎖の supremum = ∪_i F^i ∅ = supF.
 * wが固定ならFの値域は有限 (V -> powerset (wの接尾辞 × w中のデータ値)).
 * 従って，ある n が存在して F^n ∅ = supF.
 * F_is_monotonic_2 より
 * forall (Y : Env) i, F^i ∅ ⊆ F^i Y.
 * YがFの不動点なら supF = F^n ∅ ⊆ Y.
 * 従って supF はFの最小不動点.
 *)
