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

Section Monotonicity.

Definition env_leq (u1 u2 : Env) : Prop :=
  forall v : V,
  forall (theta : Theta) (w : data_word),
  u1 v theta w -> u2 v theta w.

Lemma models_is_monotonic :
  forall (u1 u2 : Env),
  env_leq u1 u2 ->
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

Theorem F_is_monotonic :
  forall (sigma : eqn_sys) (u1 u2 : Env),
  env_leq u1 u2 ->
  env_leq (F sigma u1) (F sigma u2).
Proof.
  intros sigma u1 u2 H.
  unfold env_leq.
  unfold F.
  intros v.
  now apply models_is_monotonic.
Qed.

Theorem Fpow_is_monotonic_1 :
  forall (sigma : eqn_sys) (i : nat),
  env_leq (Fpow_emp sigma i) (Fpow_emp sigma (S i)).
Proof.
  intros sigma i.
  induction i.
  { intros v theta w H.
    now unfold Fpow_emp in H. }
  unfold Fpow_emp.
  unfold Fpow.
  now apply F_is_monotonic.
Qed.

Theorem Fpow_is_monotonic_2 :
  forall (sigma : eqn_sys) (i : nat) (Y : Env),
  env_leq (Fpow_emp sigma i) Y ->
  env_leq (Fpow_emp sigma (S i)) (F sigma Y).
Proof.
  intros sigma i Y.
  intros H0.
  unfold Fpow_emp.
  unfold Fpow.
  now apply F_is_monotonic.
Qed.

Theorem least_fixpoint_of_F :
  forall (sigma : eqn_sys) (Y : Env),
  F sigma Y = Y ->
  forall i,
  env_leq (Fpow_emp sigma i) Y.
Proof.
  intros sigma Y HY i.
  induction i;
  intros v theta w H.
  - now unfold Fpow_emp in H.
  - rewrite<- HY.
  now apply (Fpow_is_monotonic_2 sigma i Y IHi).
Qed.

End Monotonicity.


Inductive var_not_appear (v : V)
  : ltl -> Prop :=
  | var_not_appear_VAR (v1 : V) :
      v <> v1 ->
      var_not_appear v (var v1)
  | var_not_appear_OR (p1 p2 : ltl) :
      var_not_appear v p1 ->
      var_not_appear v p2 ->
      var_not_appear v (p1 .\/ p2)
  | var_not_appear_AND (psi : ltl) (phi : ltl_phi) :
      var_not_appear v psi ->
      var_not_appear v (psi ./\ phi)
  | var_not_appear_STORE (r : register) (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (↓ r, psi)
  | var_not_appear_X (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (X psi)
  | var_not_appear_U (phi : ltl_phi) (psi : ltl) :
      var_not_appear v psi ->
      var_not_appear v (phi U psi)
  | var_not_appear_PHI (phi : ltl_phi) :
      var_not_appear v (φ phi)
  | var_not_appear_G (phi : ltl_phi) :
      var_not_appear v (G phi)
  .

Lemma ineq_sym {A : Type} :
  forall x y : A, x <> y <-> y <> x.
Proof.
  intros x y.
  split.
  - intros nxy yx. now apply nxy.
  - intros nyx xy. now apply nyx.
Qed.

Section VarExample.

Variable  r : register.
Variable  a : At.
Variables v1 v2 : V.
Hypothesis var_discrimination : v1 <> v2.
Let phi1 := (↓ r, (X (var v1))) ./\ ([p a] ../\ ~[↑ r]).

Goal ~ var_not_appear v1 phi1.
Proof.
  intros H.
  inversion H as [| |psi phi H1 [EQpsi EQphi] | | | | |].
  clear psi EQpsi phi EQphi.
  inversion H1 as [| | | r' psi H2 [EQr' EQpsi]| | | |].
  clear r' EQr' psi EQpsi.
  inversion H2 as [| | | | psi H3 EQpsi| | |].
  clear psi EQpsi.
  inversion H3 as [v1' Hv1 EQv1'| | | | | | |].
  now apply Hv1.
Qed.

Goal var_not_appear v2 phi1.
Proof.
  apply var_not_appear_AND.
  apply var_not_appear_STORE.
  apply var_not_appear_X.
  apply var_not_appear_VAR.
  now apply ineq_sym.
Qed.

End VarExample.

Section UnusedVar.

Variables sigma1 sigma2 : eqn_sys.
Variable v1 : V.
Hypothesis v1_not_in_sigma1 :
  forall v, var_not_appear v1 (sigma1 v).
Hypothesis sigma_equiv :
  forall v, v <> v1 -> sigma1 v = sigma2 v.

Lemma unused_var_not_matter :
  forall i theta w,
  forall v, v <> v1 ->
  Fpow_emp sigma1 i v theta w <-> Fpow_emp sigma2 i v theta w.
Proof.
  induction i; intros theta w v Hv1.
  - (* i = 0 -> ... *)
  unfold Fpow_emp.
  unfold Fpow.
  reflexivity.
  - (* inductive step on i *)
  unfold Fpow_emp.
  unfold Fpow.
  unfold F at 1.
  unfold F at 2.
  rewrite<- (sigma_equiv v Hv1).
  assert (Hnv1 := v1_not_in_sigma1 v).
  generalize dependent w.
  generalize dependent theta.
  induction (sigma1 v); intros theta w.
  + (* sigma1 v = var v0 -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  apply models_var;
  apply IHi;
  inversion Hx; trivial;
  try now apply ineq_sym.
  + (* sigma1 v = l1 .\/ l2 -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  apply models_OR;
  inversion Hx
  as [| | | |w' th u p1' p2' Ho | | |];
  destruct Ho as [Ho | Ho];
  try (left; now apply IHl1);
  try (right; now apply IHl2).
  + (* sigma1 v = l ./\ l0 -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx;
  apply models_AND;
  try apply IHl;
  auto.
  + (* sigma1 v = ↓ r, l -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx;
  apply models_STORE;
  now apply IHl.
  + (* sigma1 v = X l -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx;
  apply models_X;
  now apply IHl.
  + (* sigma1 v = l U l0 -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx
  as [| | | | | | w' th u l' l0' Hx' EQu EQw'|];
  clear w' EQw';
  destruct Hx' as [w' [Hx' Hsuf]];
  apply models_U;
  exists w';
  split;
  try apply IHl; auto.
  + (* sigma1 v = φ l -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx;
  now apply models_PHI.
  + (* sigma1 v = G l -> ... *)
  inversion Hnv1.
  split;
  intros Hx;
  inversion Hx;
  now apply models_G.
Qed.

End UnusedVar.
