Require Import mu.
Require Import eqnSys.
Require Import automata.

(* Definition of an RA *)

Parameter Q : Type.

Definition ConfigRA := (Q * Theta * data_word)%type.

Definition ruleRAt := (Q * SigmaE * regSet * Q)%type.
Parameter delta : list ruleRAt.

Inductive moveRA
  : ConfigRA -> ConfigRA -> Prop :=
  | moveRA_epsilon :
    forall q1 q2 theta w,
    In (q1, epsilon, reg_empty, q2) delta ->
    moveRA (q1, theta, w) (q2, theta, w)
  | moveRA_not_update :
    forall q1 q2 phi theta h t,
    In (q1, Σφ phi, reg_empty, q2) delta ->
    models_phi (h::t) theta phi ->
    moveRA (q1, theta, h::t) (q2, theta, t)
  | moveRA_update :
    forall q1 q2 phi r theta a t,
    In (q1, Σφ phi, reg r, q2) delta ->
    models_phi (a::t) theta phi ->
    moveRA (q1, theta, a::t) (q2, update theta r (snd a), t)
  .

Inductive moveRA_star
  : ConfigRA -> ConfigRA -> Prop :=
  | moveRA_star_ref :
    forall q1, moveRA_star q1 q1
  | moveRA_star_trans :
    forall q1 q2 q3,
    moveRA q1 q2 -> moveRA_star q2 q3 ->
    moveRA_star q1 q3
  .

Parameter finalRA : Q -> Prop.

Axiom ruleRA_is_epsilon_free :
  forall q r q',
  ~ In (q, epsilon, r, q') delta.

(* decidability *)
Axiom finalRA_dec : forall q : Q, {finalRA q} + {~ finalRA q}.
Axiom Q_eq_dec : forall q1 q2 : Q, {q1 = q2} + {q1 <> q2}.

Fixpoint restrict_rules (ls : list ruleRAt) (q : Q) :=
  match ls with
  | nil => nil
  | ((q1, _, _, _) as h) :: t =>
    if Q_eq_dec q1 q then h :: restrict_rules t q
                     else restrict_rules t q
  end.
Definition deltaq := restrict_rules delta.

(* Conversion of RA into an eqnSys *)

Parameter QVar  : Q -> V.
Parameter QDVar : (list ruleRAt) -> V.
Parameter RVar  : ruleRAt -> V.
Parameter Vend  : V.

Parameter sigmaRA : eqn_sys.

Axiom sigmaRA_end : sigmaRA Vend = φ [END].

Axiom sigmaRA_r :
  forall r,
  sigmaRA (RVar r) = 
    match r with
    | (q, Σφ phi, reg R, q') =>
        (↓ R, X (var (QVar q'))) ./\ phi
    | (q, Σφ phi, reg_empty, q') =>
        (X (var (QVar q'))) ./\ phi
    | (_, epsilon, _, _) => φ ~[tt]
    end.

Inductive disjunction_of_succ : list ruleRAt -> Prop :=
  | disjunction_of_succ_nil :
      sigmaRA (QDVar nil) = (φ ~[tt]) ->
      disjunction_of_succ nil
  | disjunction_of_succ_cons r t :
      sigmaRA (QDVar (r::t)) = (var (RVar r) .\/ var (QDVar t)) ->
      disjunction_of_succ t ->
      disjunction_of_succ (r :: t)
  .

Axiom sigmaRA_q_not_final :
  forall q : Q, ~ finalRA q ->
  sigmaRA (QVar q) =
    (var (QDVar (deltaq q)) .\/ var (QDVar (deltaq q))) /\
  disjunction_of_succ (deltaq q).

Axiom sigmaRA_q_final :
  forall q : Q, finalRA q ->
  sigmaRA (QVar q) =
    (var Vend .\/ var (QDVar (deltaq q))) /\
  disjunction_of_succ (deltaq q).

(* utilities *)

Lemma delta_and_deltaq_nonnil :
  forall q a r q',
  In (q, a, r, q') delta -> deltaq q <> nil.
Proof.
  intros q a r q' Hin.
  unfold deltaq.
  induction delta as [| h l IHl].
  - (* delta = nil -> ... *)
  now unfold In in Hin.
  - (* delta = h::l -> ... *)
  unfold In in Hin.
  destruct Hin as [Hin | Hin].
  + (* h = (q, a, r, q') -> ... *)
  rewrite Hin.
  unfold restrict_rules.
  unfold In in Hin.
  destruct (Q_eq_dec q q) as [q_eq_q | q_ne_q].
  * intros H. discriminate.
  * contradiction.
  + (* In (q, a, r, q') l -> ... *)
  assert (IHl' := IHl Hin).
  destruct h as [[[q1 a'] r'] q2].
  unfold restrict_rules.
  destruct (Q_eq_dec q1 q) as [q1_eq_q | q1_ne_q].
  * intros H. discriminate.
  * apply IHl'.
Qed.

Lemma delta_and_deltaq :
  forall q a r q',
  In (q, a, r, q') delta -> In (q, a, r, q') (deltaq q).
Proof.
  intros q a r q' Hdelta.
  unfold deltaq.
  induction delta as [| h t IHt].
  - (* delta = nil -> ... *)
  now unfold In in Hdelta.
  - (* delta = h::t -> ... *)
  unfold In in Hdelta.
  destruct Hdelta as [EQh | Hdelta].
  + (* h = (q, ...) -> ... *)
  rewrite EQh.
  unfold restrict_rules.
  destruct (Q_eq_dec q q) as [q_eq_q | q_ne_q].
  * unfold In. now left.
  * contradiction.
  + (* In (q, ...) t -> ... *)
  apply IHt in Hdelta.
  destruct h as [[[q1 a'] r'] q2].
  unfold restrict_rules.
  destruct (Q_eq_dec q1 q) as [q1_eq_q | q1_ne_q].
  * (* q1 = q -> ... *)
  unfold In. now right.
  * (* q1 <> q -> ... *)
  apply Hdelta.
Qed.

Lemma neq_to_cons_self {A : Type} :
  forall (a : A) (t : list A), t <> a :: t.
Proof.
  intros a t H.
  assert (Hl : length t = length (a::t)).
  { now rewrite<- H. }
  unfold length in Hl.
  now apply n_Sn in Hl.
Qed.

Lemma moveA_star_mid :
  forall sigma q1 q2 q3,
  moveA_star sigma q1 q2 ->
  moveA_star sigma q2 q3 ->
  moveA_star sigma q1 q3.
Proof.
  intros sigma q1 q2 q3.
  intros H12 H23.
  induction H12 as [| q1 q2 q3' H12 H23' IH];
  auto.
  apply moveA_star_trans with q2;
  now try apply IH.
Qed.

Lemma moveA_star_last :
  forall sigma q1 q2 q3,
  moveA_star sigma q1 q2 ->
  moveA sigma q2 q3 ->
  moveA_star sigma q1 q3.
Proof.
  intros sigma q1 q2 q3 H12 H23.
  apply moveA_star_mid with q2; auto.
  apply moveA_star_trans with q3;
  try apply moveA_star_ref.
  apply H23.
Qed.

(* sigmaRA simulates moveRA *)

Lemma epsilon_move_of_sigmaRA_1 :
  forall q phi q' theta w,
  let r := (q, Σφ phi, reg_empty, q') in
  In r delta ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, w)
                     (sigmaRA (RVar r), theta, w).
Proof.
  intros q phi q' theta w r Hin.
  assert (Hinq := delta_and_deltaq q (Σφ phi) reg_empty q' Hin).

  destruct (finalRA_dec q) as [Hfq | Hnfq].
  + (* finalRA q -> ... *)
  destruct (sigmaRA_q_final q Hfq) as [Hsq Hdq].
  rewrite Hsq.
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply moveA_epsilon;
  apply ruleA_OR_right. }
  clear Hsq.
  induction (deltaq q) as [| r' t IHt].
  { now unfold In in Hinq. }
  unfold In in Hinq.
  destruct Hinq as [EQr | Hinq].
  * (* r' = (q,...) -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  rewrite Hsd.
  rewrite EQr.
  apply moveA_star_trans with (sigmaRA (RVar r), theta, w);
  try apply moveA_star_ref.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  * (* In (q,...) t -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  apply moveA_star_trans
  with (sigmaRA (QDVar t), theta, w);
  try now apply IHt.
  rewrite Hsd.
  apply moveA_epsilon.
  apply ruleA_OR_right.
  + (* ~ finalRA q -> ... *)
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hdq].
  rewrite Hsq.
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply moveA_epsilon;
  apply ruleA_OR_right. }
  clear Hsq.
  induction (deltaq q) as [| r' t IHt].
  { now unfold In in Hinq. }
  unfold In in Hinq.
  destruct Hinq as [EQr | Hinq].
  * (* r' = (q,...) -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  rewrite Hsd.
  rewrite EQr.
  apply moveA_star_trans with (sigmaRA (RVar r), theta, w);
  try apply moveA_star_ref.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  * (* In (q,...) t -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  apply moveA_star_trans
  with (sigmaRA (QDVar t), theta, w);
  try now apply IHt.
  rewrite Hsd.
  apply moveA_epsilon.
  apply ruleA_OR_right.
Qed.

Lemma epsilon_move_of_sigmaRA_2 :
  forall q phi q' theta w rg,
  let r := (q, Σφ phi, reg rg, q') in
  In r delta ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, w)
                     (sigmaRA (RVar r), theta, w).
Proof.
  intros q phi q' theta w rg.
  intros r Hin.
  assert (Hinq := delta_and_deltaq q (Σφ phi) (reg rg) q' Hin).

  destruct (finalRA_dec q) as [Hfq | Hnfq].
  + (* finalRA q -> ... *)
  destruct (sigmaRA_q_final q Hfq) as [Hsq Hdq].
  rewrite Hsq.
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply moveA_epsilon; apply ruleA_OR_right. }
  clear Hsq.
  induction (deltaq q) as [| r' t IHt].
  { now unfold In in Hinq. }
  unfold In in Hinq.
  destruct Hinq as [EQr | Hinq].
  * (* r' = (q,...) -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  rewrite Hsd.
  rewrite EQr.
  apply moveA_star_trans with (sigmaRA (RVar r), theta, w);
  try apply moveA_star_ref.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  * (* In (q,...) t -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  apply moveA_star_trans
  with (sigmaRA (QDVar t), theta, w);
  try now apply IHt.
  rewrite Hsd.
  apply moveA_epsilon.
  apply ruleA_OR_right.
  + (* ~ finalRA q -> ... *)
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hdq].
  rewrite Hsq.
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply moveA_epsilon;
  apply ruleA_OR_right. }
  clear Hsq.
  induction (deltaq q) as [| r' t IHt].
  { now unfold In in Hinq. }
  unfold In in Hinq.
  destruct Hinq as [EQr | Hinq].
  * (* r = (q,...) -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  rewrite Hsd.
  rewrite EQr.
  apply moveA_star_trans with (sigmaRA (RVar r), theta, w);
  try apply moveA_star_ref.
  apply moveA_epsilon.
  apply ruleA_OR_left.
  * (* In (q,...) t -> ... *)
  inversion Hdq as [| r'' t' Hsd Hdt [EQr'' EQt']].
  clear r'' EQr'' t' EQt'.
  apply moveA_star_trans
  with (sigmaRA (QDVar t), theta, w);
  try now apply IHt.
  rewrite Hsd.
  apply moveA_epsilon.
  apply ruleA_OR_right.
Qed.

Lemma sigmaRA_simulates_finalRA :
  forall q theta,
  finalRA q ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, nil)
                     (φ [END], theta, nil).
Proof.
  intros q theta Hfin.
  apply moveA_star_trans with (φ [END], theta, nil);
  try apply moveA_star_ref.
  destruct (sigmaRA_q_final q Hfin) as [Hsq Hd].
  rewrite Hsq.
  apply moveA_epsilon.
  rewrite<- sigmaRA_end.
  apply ruleA_OR_left.
Qed.

Lemma sigmaRA_simulates_one_moveRA :
  forall q theta w q' theta' w',
  moveRA (q, theta, w) (q', theta', w') ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, w)
                     (sigmaRA (QVar q'), theta', w').
Proof.
  intros q theta w q' theta' w'.
  intros Hmo.
  remember (q, theta, w) as x.
  remember (q', theta', w') as y.
  destruct Hmo
  as [q1 q2 th w1 Hd | q1 q2 phi th h t Hin Hm
     |q1 q2 phi rg th h t Hin Hphi].
  - (* In (q1, epsilon, ...) delta -> ... *)
  assert (He := ruleRA_is_epsilon_free q1 reg_empty q2).
  contradiction.
  - (* In (q1, Σφ phi, ...) delta -> ... *)
  injection Heqx; intros EQw EQth EQq1.
  rewrite<- EQw.
  rewrite EQth in Heqy.
  rewrite EQth in Hm.
  rewrite EQq1 in Hin.
  clear w EQw th EQth q1 EQq1 Heqx.
  injection Heqy; intros EQw EQth EQq2.
  rewrite<- EQw.
  rewrite<- EQth.
  rewrite EQq2 in Hin.
  clear w' EQw theta' EQth q2 EQq2 Heqy.
  assert (Hep := epsilon_move_of_sigmaRA_1
                 q phi q' theta (h::t) Hin).
  apply moveA_star_last
  with (sigmaRA (RVar (q, Σφ phi, reg_empty, q')), theta, h::t);
  try apply Hep.
  rewrite sigmaRA_r.
  apply moveA_not_update with phi; auto.
  apply ruleA_X.
  - (* In (q1, Σφ phi, ...) delta -> ... *)
  injection Heqx; intros EQw EQth EQq1.
  rewrite<- EQw.
  rewrite EQth in Heqy.
  rewrite EQth in Hphi.
  rewrite EQq1 in Hin.
  clear w EQw th EQth q1 EQq1 Heqx.
  injection Heqy; intros EQw EQth EQq2.
  rewrite<- EQw.
  rewrite<- EQth.
  rewrite EQq2 in Hin.
  clear w' EQw theta' EQth q2 EQq2 Heqy.
  assert (Hep := epsilon_move_of_sigmaRA_2
                 q phi q' theta (h::t) rg Hin).
  apply moveA_star_last
  with (sigmaRA (RVar (q, Σφ phi, reg rg, q')), theta, h::t);
  try apply Hep.
  rewrite sigmaRA_r.
  apply moveA_update with phi; auto.
  apply ruleA_STORE_X.
Qed.

Theorem sigmaRA_simulates_RA :
  forall q theta w theta',
  (exists qF,
   finalRA qF /\
   moveRA_star (q, theta, w) (qF, theta', nil)) ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, w) (φ [END], theta', nil).
Proof.
  intros q theta w theta'.
  intros [qF [Hfin Hmo]].
  remember (q, theta, w) as x.
  remember (qF, theta', nil) as y.
  generalize dependent w.
  generalize dependent theta.
  generalize dependent q.
  induction Hmo as [c1| c1 c2 c3 Hmo12 Hmo23 IH]
  ; intros q theta w Hq.
  - (* base case *)
  rewrite Heqy in Hq.
  injection Hq;
  intros EQw EQth EQqF.
  rewrite <- EQw.
  rewrite EQth.
  rewrite EQqF in Hfin.
  now apply sigmaRA_simulates_finalRA.
  - (* inductive step *)
  assert (IH' := IH Heqy).
  clear Heqy IH.
  inversion Hmo12
  as [q1 q2 th w' Hin EQq1 EQq2
     |q1 q2 phi th h t Hin Hphi EQq1 EQq2
     |q1 q2 phi r th h t Hin Hphi EQq1 EQq2].
  + (* moveRA (q1, theta, w) (q2, theta, w) -> ... *)
  rewrite Hq in EQq1.
  injection EQq1;
  intros EQw' EQth EQq.
  rewrite EQw' in EQq2.
  rewrite EQth in EQq2.
  rewrite EQq in Hin.
  clear EQq1 EQw' EQth EQq w' th q1.
  symmetry in EQq2.
  apply moveRA_epsilon with (theta := theta) (w := w)
  in Hin as Hmo.
  apply moveA_star_mid with (sigmaRA (QVar q2), theta, w).
  * now apply sigmaRA_simulates_one_moveRA.
  * now apply IH'.
  + (* moveRA (q1, theta, h::t) (q2, theta, t) -> ... *)
  rewrite Hq in EQq1.
  injection EQq1;
  intros EQw EQth EQq.
  rewrite EQth in EQq2.
  rewrite EQth in Hphi.
  rewrite EQq in Hin.
  rewrite<- EQw.
  clear EQq1 EQw EQth EQq th q1.
  symmetry in EQq2.
  apply moveRA_not_update with (theta:=theta) (h:=h) (t:=t)
  in Hin as Hmo; auto.
  apply moveA_star_mid with (sigmaRA (QVar q2), theta, t).
  * now apply sigmaRA_simulates_one_moveRA.
  * now apply IH'.
  + (* moveRA (q1, theta, h::t) (q2, update theta ..., t) -> ... *)
  rewrite Hq in EQq1.
  injection EQq1;
  intros EQw EQth EQq.
  rewrite EQth in EQq2.
  rewrite EQth in Hphi.
  rewrite EQq in Hin.
  rewrite<- EQw.
  clear EQq1 EQw EQth EQq th q1.
  symmetry in EQq2.
  apply moveRA_update with (theta:=theta) (a:=h) (t:=t)
  in Hin as Hmo; auto.
  apply moveA_star_mid with (sigmaRA (QVar q2), update theta r (snd h), t).
  * now apply sigmaRA_simulates_one_moveRA.
  * now apply IH'.
Qed.
