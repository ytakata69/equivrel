Require Import mu.

(* Equation systems *)

Definition eqn_sys := V -> ltl.  (* the set of equation systems *)

(* the environment that assigns the empty set to every variable *)
Definition empty_env : Env :=
  fun (v : V) (theta : Theta) (w : data_word) => False.

(* The transformation from Env to Env *)
Definition F (sigma : eqn_sys) (env : Env) : Env :=
  fun (v : V) (theta : Theta) (w : data_word) =>
  (w, theta |= env, sigma v).

(* power of F *)
Fixpoint Fpow (sigma : eqn_sys) (i : nat) (u : Env) : Env :=
  match i with
    0   => u
  | S n => F sigma (Fpow sigma n u)
  end.
Definition Fpow_emp sigma i := Fpow sigma i empty_env.

Section EqnExample.

Variable b : Sigma.
Let w : data_word :=
  ((b, 2) :: (b, 3) :: (b, 3) :: (b, 4) :: (b, 2) :: nil).
Let sigma : eqn_sys :=
  fun v => match v with
    1 => ↓ 1, X (var 2)
  | 2 => ((X (var 2)) ./\ ~[↑ 1]) .\/ ((X (var 3)) ./\ [↑ 1])
  | 3 => φ [END]
  | _ => φ [tt]
  end.

Let th : Theta :=
  fun r => match r with
    1 => 2
  | _ => 0
  end.

Goal F sigma empty_env 3 th nil.
Proof.
  unfold F.
  unfold sigma.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
Qed.
Goal ~ F sigma empty_env 1 th nil.
Proof.
  unfold F.
  unfold sigma.
  intros H.
  inversion H.
Qed.
Goal forall w' th',
  ~ F sigma empty_env 1 th' w'.
Proof.
  intros w' th'.
  unfold F.
  unfold sigma.
  intros H.
  inversion H
  as [| h t th'' u r psi Hht EQu EQht EQth'' [EQr EQpsi] | | | | | |].
  clear th'' EQth'' u EQu r EQr psi EQpsi.
  inversion Hht
  as [| |h' t' th'' u psi Ht EQu [EQh' EQt'] EQth'' EQpsi| | | | |].
  clear h' EQh' t' EQt' th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
Qed.
Goal forall w' th',
  ~ F sigma empty_env 2 th' w'.
Proof.
  intros w' th'.
  unfold F.
  unfold sigma.
  intros H.
  inversion H
  as [| | | | w'' th'' u psi1 psi2 Ho EQu EQw'' EQth'' [EQp1 EQp2]| | |].
  clear w'' EQw'' th'' EQth'' u EQu psi1 EQp1 psi2 EQp2.
  destruct Ho as [Ho | Ho].
  - inversion Ho
  as [| | |w'' th'' u psi phi Hx Hp EQu EQw'' EQth'' [EQpsi EQphi]| | | |].
  clear w'' EQw'' th'' EQth'' u EQu psi EQpsi phi EQphi.
  inversion Hx
  as [| |h t th'' u psi Ht EQu EQht EQth'' EQpsi | | | | |].
  clear th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
  - inversion Ho
  as [| | |w'' th'' u psi phi Hx Hp EQu EQw'' EQth'' [EQpsi EQphi]| | | |].
  clear w'' EQw'' th'' EQth'' u EQu psi EQpsi phi EQphi.
  inversion Hx
  as [| |h t th'' u psi Ht EQu EQht EQth'' EQpsi | | | | |].
  clear th'' EQth'' u EQu psi EQpsi.
  inversion Ht
  as [| | | | | | |w'' th'' u v He EQu EQw'' EQth'' EQv].
  clear w'' EQw'' th'' EQth'' u EQu v EQv.
  unfold empty_env in He.
  contradiction.
Qed.
Goal (F sigma) ((F sigma) empty_env) 2 th ((b, 2)::nil).
Proof.
  unfold F.
  unfold sigma at 2.
  apply models_OR.
  right.
  apply models_AND.
  - apply models_X.
  apply models_var.
  unfold sigma.
  apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  - unfold models_phi.
  unfold models_atom.
  unfold snd.
  now unfold th.
Qed.

End EqnExample.

(* F and models *)

Lemma meanings_of_models_var :
  forall (w : data_word) (sigma : eqn_sys)
    (theta : Theta) (u : Env) (v : V),
  (w, theta |= F sigma u, var v) <->
  (w, theta |= u, sigma v).
Proof.
  intros w sigma theta u v.
  split.
  - (* -> *)
  intros H.
  inversion H
  as [| | | | | | |w' th u' v' H' EQu' EQw' EQth EQv'].
  clear w' EQw' th EQth u' EQu' v' EQv'.
  now unfold F in H'.
  - (* <- *)
  intros H.
  apply models_var.
  now unfold F.
Qed.

Lemma meanings_of_models_var_on_lfp :
  forall (w : data_word) (sigma : eqn_sys)
    (theta : Theta) (u : Env) (v : V),
  u = F sigma u ->
  (w, theta |= u, var v) <->
  (w, theta |= u, sigma v).
Proof.
  intros w sigma theta u v.
  intros Hlfp.
  rewrite Hlfp at 1.
  apply meanings_of_models_var.
Qed.

(* monotonicity *)

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
