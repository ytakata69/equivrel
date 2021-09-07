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

Axiom QDVar_is_injective :
  forall l1 l2, QDVar l1 = QDVar l2 -> l1 = l2.

Axiom RVar_is_not_Vend  : forall r, RVar r <> Vend.
Axiom QDVar_is_not_Vend : forall l, QDVar l <> Vend.
Axiom RVar_is_not_QDVar : forall r l, RVar r <> QDVar l.


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

Axiom sigmaRA_QVar_dec :
  forall q',
  {exists q, q' = (sigmaRA (QVar q))} +
  {forall q, q' <> (sigmaRA (QVar q))}.

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

Lemma deltaq_is_subset_of_delta :
  forall r q,
  In r (deltaq q) -> In r delta.
Proof.
  intros r q H.
  unfold deltaq in H.
  induction delta as [| h t IHt].
  - (* delta = nil -> ... *)
  now unfold In in H.
  - (* delta = h::t -> ... *)
  destruct h as [[[q1 a] rg] q2].
  unfold restrict_rules in H.
  destruct (Q_eq_dec q1 q) as [q1_eq_q | q1_ne_q].
  + unfold In in H.
  destruct H as [H | H].
  * rewrite H. unfold In. now left.
  * unfold In. right. apply (IHt H).
  + unfold In. right. apply (IHt H).
Qed.

Lemma deltaq_and_q :
  forall q r,
  In r (deltaq q) ->
  match r with (q1, _, _, _) => q1 = q end.
Proof.
  intros q r H.
  unfold deltaq in H.
  induction delta as [| r' t' IHt'].
  - now unfold restrict_rules in H.
  - destruct r' as [[[q1 a] rg] q2].
  unfold restrict_rules in H.
  destruct (Q_eq_dec q1 q) as [q1q | q1q].
  + unfold In in H.
  destruct H as [H | H].
  * rewrite q1q in H.
  now rewrite <- H.
  * apply (IHt' H).
  + apply (IHt' H).
Qed.

Lemma deltaq_and_q_1 :
  forall q r t,
  deltaq q = r :: t ->
  match r with (q1, _, _, _) => q1 = q end.
Proof.
  intros q r t H.
  apply deltaq_and_q.
  rewrite H.
  unfold In.
  now left.
Qed.

Lemma q_disjunction_of_succ :
  forall q : Q, disjunction_of_succ (deltaq q).
Proof.
  intros q.
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  - now destruct (sigmaRA_q_final q Hfq).
  - now destruct (sigmaRA_q_not_final q Hnfq).
Qed.

Lemma sigmaRA_QVar :
  forall q,
  let Vd := QDVar (deltaq q) in
  sigmaRA (QVar q) = (var Vend .\/ var Vd) \/
  sigmaRA (QVar q) = (var Vd .\/ var Vd).
Proof.
  intros q.
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  - left. apply (sigmaRA_q_final q Hfq).
  - right. apply (sigmaRA_q_not_final q Hnfq).
Qed.

Lemma sigmaRA_RVar :
  forall r,
  sigmaRA (RVar r) = (φ ~[tt]) \/
  (exists q phi,
   sigmaRA (RVar r) = ((X (var (QVar q))) ./\ phi)) \/
  (exists rg q phi,
   sigmaRA (RVar r) = ((↓ rg, X (var (QVar q))) ./\ phi)).
Proof.
  intros r.
  destruct r as [[[q1 a] rg] q2].
  assert (Hr := sigmaRA_r (q1, a, rg, q2)).
  destruct a as [| phi].
  - (* a = epsilon -> ... *)
  now left.
  - (* a = Σφ phi -> ... *)
  destruct rg as [| rg].
  + (* rg = reg_empty -> ... *)
  right; left.
  now exists q2; exists phi.
  + (* rg = reg rg -> ... *)
  right; right.
  now exists rg; exists q2; exists phi.
Qed.

Lemma sigmaRA_QDVar :
  forall l,
  disjunction_of_succ l ->
  sigmaRA (QDVar l) = (φ ~[tt]) \/
  (exists r t,
   sigmaRA (QDVar l) = (var (RVar r) .\/ var (QDVar t))).
Proof.
  intros l H.
  inversion H as [| r t].
  - now left.
  - right.
  exists r.
  now exists t.
Qed.

Lemma sigmaRA_QVar_neq_end :
  forall q, sigmaRA (QVar q) <> (φ [END]).
Proof.
  intros q.
  destruct (sigmaRA_QVar q) as [EQsq | EQsq];
  rewrite EQsq;
  discriminate.
Qed.

Lemma sigmaRA_RVar_neq_end :
  forall r, sigmaRA (RVar r) <> (φ [END]).
Proof.
  intros r.
  destruct (sigmaRA_RVar r)
  as [EQsr | [[q [phi EQsr]] | [rg [q [phi EQsr]]]]];
  rewrite EQsr.
  - now apply ff_neq_end.
  - discriminate.
  - discriminate.
Qed.

Lemma sigmaRA_QDVar_neq_end :
  forall l,
  disjunction_of_succ l ->
  sigmaRA (QDVar l) <> (φ [END]).
Proof.
  intros l Hd.
  destruct (sigmaRA_QDVar l) as [EQsd | [v1 [v2 EQsd]]];
  try rewrite EQsd; try apply Hd.
  - now apply ff_neq_end.
  - discriminate.
Qed.

Lemma sigmaRA_QDVar_neq_QVar :
  forall l q,
  disjunction_of_succ l ->
  sigmaRA (QDVar l) <> sigmaRA (QVar q).
Proof.
  intros l q Hd.
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  - destruct (sigmaRA_q_final q Hfq) as [Hsq Hdq];
  rewrite Hsq.
  destruct (sigmaRA_QDVar l) as [EQsd | [r [t EQsd]]];
  try rewrite EQsd; try apply Hd.
  + intros H. discriminate.
  + intros H. injection H.
  intros Hqd Hr.
  now apply RVar_is_not_Vend in Hr.
  - destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hdq];
  rewrite Hsq.
  destruct (sigmaRA_QDVar l) as [EQsd | [r [t EQsd]]];
  try rewrite EQsd; try apply Hd.
  + intros H. discriminate.
  + intros H. injection H.
  intros Hqd Hr.
  now apply RVar_is_not_QDVar in Hr.
Qed.

Section Injectivity.

Variables q q' : Q.

Lemma deltaq_is_injective :
  deltaq q = deltaq q' ->
  deltaq q = nil \/ q = q'.
Proof.
  remember (deltaq q) as dq.
  destruct dq as [| r t].
  - intros. now left.
  - destruct r as [[[q1 a] rg] q2].
  intros Hq'.
  symmetry in Heqdq.
  symmetry in Hq'.
  apply deltaq_and_q_1 in Heqdq.
  apply deltaq_and_q_1 in Hq'.
  rewrite <- Heqdq.
  rewrite <- Hq'.
  now right.
Qed.

Lemma sigmaRA_QVar_is_injective :
  sigmaRA (QVar q) = sigmaRA (QVar q') ->
  (deltaq q = nil /\ deltaq q' = nil) \/
  q = q'.
Proof.
  intros H.
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  - (* finalRA q -> ... *)
  destruct (sigmaRA_q_final q Hfq) as [EQsq Hd];
  rewrite EQsq in H.
  destruct (finalRA_dec q') as [Hfq' | Hnfq'].
  + (* finalRA q' -> ... *)
  destruct (sigmaRA_q_final q' Hfq') as [EQsq' Hd'];
  rewrite EQsq' in H.
  injection H; intros Hqd.
  apply QDVar_is_injective in Hqd.
  apply deltaq_is_injective in Hqd as Hqd'.
  destruct Hqd' as [Hqd' | Hqd'].
  * rewrite<- Hqd. now left.
  * now right.
  + (* ~ finalRA q' -> ... *)
  destruct (sigmaRA_q_not_final q' Hnfq') as [EQsq' Hd'];
  rewrite EQsq' in H.
  injection H; intros Hqd Hve.
  symmetry in Hve.
  now apply QDVar_is_not_Vend in Hve.
  - (* ~ finalRA q -> ... *)
  destruct (sigmaRA_q_not_final q Hnfq) as [EQsq Hd];
  rewrite EQsq in H.
  destruct (finalRA_dec q') as [Hfq' | Hnfq'].
  + (* finalRA q' -> ... *)
  destruct (sigmaRA_q_final q' Hfq') as [EQsq' Hd'];
  rewrite EQsq' in H.
  injection H; intros Hqd Hve.
  now apply QDVar_is_not_Vend in Hve.
  + (* ~ finalRA q' -> ... *)
  destruct (sigmaRA_q_not_final q' Hnfq') as [EQsq' Hd'];
  rewrite EQsq' in H.

  injection H; intros Hqd _.
  apply QDVar_is_injective in Hqd.
  apply deltaq_is_injective in Hqd as Hqd'.
  destruct Hqd' as [Hqd' | Hqd'].
  * rewrite<- Hqd. now left.
  * now right.
Qed.

End Injectivity.

Lemma neq_to_cons_self {A : Type} :
  forall (a : A) (t : list A), t <> a :: t.
Proof.
  intros a t H.
  assert (Hl : length t = length (a::t)).
  { now rewrite<- H. }
  unfold length in Hl.
  now apply n_Sn in Hl.
Qed.

(* sigmaRA simulates moveRA *)

Section SigmaSimulatesRA.

Lemma QVar_to_QDVar :
  forall q theta w,
  moveA sigmaRA (sigmaRA (QVar q), theta, w)
                (sigmaRA (QDVar (deltaq q)), theta, w).
Proof.
  intros q theta w.
  destruct (finalRA_dec q) as [Hfq | Hnfq];
  [ destruct (sigmaRA_q_final q Hfq) as [Hsq Hdq']
  | destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hdq'] ];
  rewrite Hsq;
  apply moveA_epsilon;
  apply ruleA_OR_right.
Qed.

Lemma epsilon_move_of_sigmaRA_1 :
  forall q phi q' theta w,
  let r := (q, Σφ phi, reg_empty, q') in
  In r delta ->
  moveA_star sigmaRA (sigmaRA (QVar q), theta, w)
                     (sigmaRA (RVar r), theta, w).
Proof.
  intros q phi q' theta w r Hin.
  assert (Hinq := delta_and_deltaq q (Σφ phi) reg_empty q' Hin).
  assert (Hdq := q_disjunction_of_succ q).
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply QVar_to_QDVar. }

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
  assert (Hdq := q_disjunction_of_succ q).
  apply moveA_star_trans
  with (sigmaRA (QDVar (deltaq q)), theta, w).
  { apply QVar_to_QDVar. }

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
  apply moveA_star_is_transitive_at_last
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
  apply moveA_star_is_transitive_at_last
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
  apply moveA_star_is_transitive with (sigmaRA (QVar q2), theta, w).
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
  apply moveA_star_is_transitive with (sigmaRA (QVar q2), theta, t).
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
  apply moveA_star_is_transitive with (sigmaRA (QVar q2), update theta r (snd h), t).
  * now apply sigmaRA_simulates_one_moveRA.
  * now apply IH'.
Qed.

End SigmaSimulatesRA.

Section RASimulatesSigma.

(* transitive closure of (moveA sigmaRA) *)
Inductive moveA_plus_without_QVar
  : Config -> Config -> Prop :=
  | moveA_plus_without_QVar_step :
    forall c1 c2,
    moveA sigmaRA c1 c2 ->
    moveA_plus_without_QVar c1 c2
  | moveA_plus_without_QVar_trans :
    forall c1 c2 c3 : Config,
    (forall q,
     match c2 with (q2, _, _) =>
       (q2 <> (sigmaRA (QVar q))) end) ->
    moveA sigmaRA c1 c2 ->
    moveA_plus_without_QVar c2 c3 ->
    moveA_plus_without_QVar c1 c3
  .

(* reflexive transitive closure of (moveA sigmaRA) *)
Inductive moveA_star_without_QVar
  : Config -> Config -> Prop :=
  | moveA_star_without_QVar_ref :
    forall c1,
    moveA_star_without_QVar c1 c1
  | moveA_star_without_QVar_plus :
    forall c1 c2,
    moveA_plus_without_QVar c1 c2 ->
    moveA_star_without_QVar c1 c2
  .

Lemma moveA_star_can_be_split_at_QVar :
  forall c1 c3,
  moveA_star sigmaRA c1 c3 ->
  moveA_star_without_QVar c1 c3 \/
  exists c2,
    (exists q, match c2 with (q2, _, _) =>
               q2 = (sigmaRA (QVar q)) end) /\
    moveA_plus_without_QVar c1 c2 /\
    moveA_star sigmaRA c2 c3.
Proof.
  intros c1 c3 Hmo.
  induction Hmo as [c1 | c1 c2 c3 H12 H23 IH].
  - (* zero step *)
  left. apply moveA_star_without_QVar_ref.
  - (* one or more steps *)
  destruct IH as [IH | [c2' [IH1 [IH2 IH3]]]].
  + (* moveA_star_without_QVar c2 c3 -> ... *)
  destruct c2 as [[q2 th] w'].
  destruct (sigmaRA_QVar_dec q2) as [[q Hq2] | Hq2].
  * (* q2 = sigmaRA (QVar q) -> ... *)
  right.
  exists (q2, th, w').
  split; [| split]; auto.
  -- now exists q.
  -- now apply moveA_plus_without_QVar_step.
  * (* (forall q, q2 <> sigmaRA (QVar q)) -> ... *)
  left.
  inversion IH as [c3' EQc3' EQc3| c2 c3' IH' EQc2 EQc3];
  apply moveA_star_without_QVar_plus.
  -- now apply moveA_plus_without_QVar_step.
  -- apply moveA_plus_without_QVar_trans
  with (q2, th, w'); auto.
  + (* exists c2', moveA_star_without_QVar c2 c2' /\ ... -> ... *)
  destruct c2 as [[q2 th] w'].
  destruct (sigmaRA_QVar_dec q2) as [[q Hq2] | Hq2].
  * (* q2 = sigmaRA (QVar q) -> ... *)
  right.
  exists (q2, th, w').
  split; [| split]; auto.
  -- now exists q.
  -- now apply moveA_plus_without_QVar_step.
  * (* (forall q, q2 <> sigmaRA (QVar q)) -> ... *)
  right.
  exists c2'.
  split; [| split]; auto.
  inversion IH2
  as [c2'' c2 H23' EQc2'' EQc2
     |c2'' c2 c3' Hc2 H23' H23'' EQc2 EQc3];
  apply moveA_plus_without_QVar_trans
  with (q2, th, w'); auto.
Qed.

(* Simulate final step *)

Lemma RVar_to_end_without_QVar :
  forall r theta w theta',
  ~ moveA_star_without_QVar
    (sigmaRA (RVar r), theta, w)
    (φ [END], theta', nil).
Proof.
  intros r theta w theta' H.
  inversion H
  as [c1 EQc1 [EQsr EQtheta EQw]
     |c1' c2' Hplus EQc1' EQc2'];
  [| inversion Hplus
      as [c1 c2 H12 EQc1 EQc2
         |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3]].
  - (* sigmaRA (RVar r) = φ [END] -> ... *)
  now apply sigmaRA_RVar_neq_end in EQsr.
  - (* c2 = (φ [END], theta', nil) -> ... *)
  destruct (sigmaRA_RVar r)
  as [EQsr' | [[q [phi EQsr']] | [rg [q [phi EQsr']]]]];
  rewrite EQsr' in H12;
  inversion H12
  as [q1' q2' th w' Hr [EQq1 EQth EQw'] EQq2
     |q1' q2' phi' th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1' q2' phi' rg' th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [| | |v phi'' [EQv EQphi''] EQphi' EQr EQq2'
     |r' v phi'' [EQr' EQv EQphi''] EQphi' EQr EQq2'];
  destruct (sigmaRA_QVar q) as [Hsq | Hsq];
  rewrite Hsq in EQq2';
  discriminate.
  - (* moveA ... (sigmaRA (RVar r), ...) c2 -> ... *)
  destruct (sigmaRA_RVar r)
  as [EQsr' | [[q [phi EQsr']] | [rg [q [phi EQsr']]]]];
  rewrite EQsr' in H12;
  inversion H12
  as [q1' q2' th w' Hr [EQq1 EQth EQw'] EQq2
     |q1' q2' phi' th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1' q2' phi' rg' th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [phi'' EQphi'' EQphi' EQr EQq2' | |
     |v phi'' [EQv EQphi''] EQphi' EQr EQq2'
     |r' v phi'' [EQr' EQv EQphi''] EQphi' EQr EQq2'].
  + (* sigmaRA (RVar r) = φ ~[tt] -> ... *)
  rewrite <- EQphi' in Hphi.
  unfold models_phi in Hphi.
  now unfold models_atom in Hphi.
  + (* sigmaRA (RVar r) = X ... -> ... *)
  rewrite <- EQq2' in EQq2.
  rewrite <- EQq2 in Hc2.
  now apply (Hc2 q).
  + (* sigmaRA (RVar r) = ↓ rg, X ... -> ... *)
  rewrite <- EQq2' in EQq2.
  rewrite <- EQq2 in Hc2.
  now apply (Hc2 q).
Qed.

Lemma QDVar_to_end_without_QVar :
  forall q theta w theta',
  ~ moveA_star_without_QVar
    (sigmaRA (QDVar (deltaq q)), theta, w)
    (φ [END], theta', nil).
Proof.
  intros q theta w theta' H.
  assert (Hd := q_disjunction_of_succ q).

  induction (deltaq q) as [| r t IHt];
  inversion Hd as [EQsd|r' t' EQsd Hdt [EQr' EQt']].
  + (* deltaq q = nil -> ... *)
  inversion H
  as [c1 EQc1 [EQsd' EQtheta EQw]
     |c1' c2' Hplus EQc1' EQc2'];
  [| inversion Hplus
      as [c1 c2 H12 EQc1 EQc2
         |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3]].
  * (* sigmaRA (QDVar (deltaq q)) = (φ [END]) -> ... *)
  rewrite EQsd in EQsd'.
  now apply ff_neq_end in EQsd'.
  * (* c2 = (φ [END], theta', nil) -> ... *)
  rewrite EQsd in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr.
  * (* moveA ... (sigmaRA (QDVar nil), ...) c2 -> ... *)
  rewrite EQsd in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr as [phi' EQphi' EQphi EQr EQq2'| | | |].
  rewrite <- EQphi in Hphi.
  unfold models_phi in Hphi.
  now unfold models_atom in Hphi.
  + (* deltaq q = r :: t -> ... *)
  clear r' EQr' t' EQt'.
  inversion H
  as [c1 EQc1 [EQsd' EQtheta EQw]
     |c1' c2' Hplus EQc1' EQc2'];
  [| inversion Hplus
      as [c1 c2 H12 EQc1 EQc2
         |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3]].
  * (* sigmaRA (QDVar (deltaq q)) = (φ [END]) -> ... *)
  rewrite EQsd in EQsd'.
  discriminate.
  * (* c2 = (φ [END], theta', nil) -> ... *)
  rewrite EQsd in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t' Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t' Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2'| |];
  clear v1 EQv1 v2 EQv2 EQe EQr.
  -- (* c2 = (sigmaRA (RVar r), ...) -> ... *)
  now apply sigmaRA_RVar_neq_end in EQq2'.
  -- (* c2 = (sigmaRA (QDVar t), ...) -> ... *)
  now apply sigmaRA_QDVar_neq_end in EQq2'.
  * (* moveA ... (sigmaRA (QDVar (r::t)), ...) c2 -> ... *)
  rewrite EQsd in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t' Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t' Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2'| |];
  clear v1 EQv1 v2 EQv2 EQe EQr;
  rewrite <- EQq2' in EQq2;
  rewrite <- EQq2 in H23.
  -- (* c2 = (sigmaRA (RVar r), ...) -> ... *)
  apply moveA_star_without_QVar_plus in H23.
  now apply RVar_to_end_without_QVar in H23.
  -- (* c2 = (sigmaRA (QDVar t), ...) -> ... *)
  apply IHt; auto.
  now apply moveA_star_without_QVar_plus.
Qed.

Lemma Vend_to_end_without_QVar :
  forall theta w theta',
  moveA_star_without_QVar
    (sigmaRA Vend, theta, w) (φ [END], theta', nil) ->
  theta = theta' /\ w = nil.
Proof.
  intros theta w theta' H.
  inversion H
  as [c1 EQc1 [EQsd' EQtheta EQw]
     |c1' c2' Hplus EQc1' EQc2'];
  [| inversion Hplus
      as [c1 c2 H12 EQc1 EQc2
         |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3]].
  * (* zero step -> ... *)
  split; auto.
  * (* one step -> ... *)
  rewrite sigmaRA_end in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr.
  * (* moveA ... (sigmaRA Vend, ...) c2 -> ... *)
  rewrite sigmaRA_end in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr as [phi' EQphi' EQphi EQr EQq2'| | | |].
  rewrite <- EQphi in Hphi.
  unfold models_phi in Hphi.
  now unfold models_atom in Hphi.
Qed.

Theorem RA_simulates_sigmaRA_end :
  forall q theta w theta',
  moveA_star_without_QVar (sigmaRA (QVar q), theta, w) (φ [END], theta', nil) ->
  finalRA q /\ theta = theta' /\ w = nil.
Proof.
  intros q theta w theta' Hmo.
  inversion Hmo
  as [c1 EQc1 [Hsq EQth EQw]
     |c1' c2' Hplus EQc1' EQc2'];
  [| inversion Hplus
      as [c1 c2 H12 EQc1 EQc2
         |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3]].
  - (* zero step /\ sigmaRA (QVar q) = φ [END] -> ... *)
  split; [| split];
  destruct (finalRA_dec q) as [Hfq | Hnfq];
  auto; try apply Hfq. (* finalRA q -> proved *)
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq' Hd].
  rewrite Hsq' in Hsq.
  discriminate.
  - (* one step /\ c2 = (φ [END], theta', nil) -> ... *)
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  + (* finalRA q -> ... *)
  destruct (sigmaRA_q_final q Hfq) as [Hsq Hd].
  rewrite Hsq in H12.
  split; [| split];
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  auto.
  + (* ~ finalRA q -> ... *)
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hd].
  rewrite Hsq in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  now apply (sigmaRA_QDVar_neq_end (deltaq q) Hd) in EQq2'.
  - (* more than one steps /\ moveA sigmaRA (sigmaRA (QVar q), ...) c2 -> ... *)
  destruct (finalRA_dec q) as [Hfq | Hnfq].
  + (* finalRA q -> ... *)
  split; auto.
  destruct (sigmaRA_q_final q Hfq) as [Hsq Hd].
  rewrite Hsq in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  rewrite <- EQq2' in EQq2;
  rewrite <- EQq2 in H23;
  apply moveA_star_without_QVar_plus in H23.
  * now apply Vend_to_end_without_QVar in H23.
  * now apply QDVar_to_end_without_QVar in H23.
  + (* ~ finalRA q -> ... *)
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq Hd].
  rewrite Hsq in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  rewrite <- EQq2' in EQq2;
  rewrite <- EQq2 in H23;
  apply moveA_star_without_QVar_plus in H23;
  now apply QDVar_to_end_without_QVar in H23.
Qed.

(* Simulate one middle step *)

Lemma QDVar_nil_to_QVar :
  forall theta w q' theta' w',
  disjunction_of_succ nil ->
  ~ moveA_plus_without_QVar
    (sigmaRA (QDVar nil), theta, w)
    (sigmaRA (QVar q'), theta', w').
Proof.
  intros theta w q' theta' w'.
  intros Hd Hmo.
  inversion Hd as [EQsd |].
  rewrite EQsd in Hmo.
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc2];
  inversion H12
  as [q1 q2 th w'' Hr
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQw] [EQq2 EQtheta EQt]
     |q1 q2 phi r th h t Hr Hphi];
  inversion Hr as [phi' EQphi' EQphi EQr EQsq'| | | |];
  rewrite <- EQphi in Hphi;
  unfold models_phi in Hphi;
  now unfold models_atom in Hphi.
Qed.

Lemma Vend_to_QVar :
  forall theta w q' theta' w',
  ~ moveA_plus_without_QVar
    (sigmaRA Vend, theta, w)
    (sigmaRA (QVar q'), theta', w').
Proof.
  intros theta w q' theta' w'.
  intros Hmo.
  rewrite sigmaRA_end in Hmo.
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc2];
  inversion H12
  as [q1 q2 th w'' Hr
     |q1 q2 phi th h t Hr Hphi
     |q1 q2 phi r th h t Hr Hphi];
  inversion Hr as [phi' EQphi' EQphi EQr EQsq'| | | |];
  rewrite <- EQphi in Hphi;
  unfold models_phi in Hphi;
  now unfold models_atom in Hphi.
Qed.

Hypothesis at_most_one_dead_end_state :
  forall q1 q2,
  deltaq q1 = nil -> deltaq q2 = nil ->
  (finalRA q1 <-> finalRA q2) ->
  q1 = q2.

Lemma RVar_to_QVar_one_step :
  forall r theta w q' theta' w',
  In r delta ->
  moveA_plus_without_QVar
    (sigmaRA (RVar r), theta, w)
    (sigmaRA (QVar q'), theta', w') ->
  match r with (q, _, _, _) =>
  moveRA (q, theta, w) (q', theta', w')
  end.
Proof.
  intros r theta w q' theta' w'.
  intros Hin Hmo.
  assert (EQsr := sigmaRA_r r).
  destruct r as [[[q a] rg] q''].
  destruct a as [|phi].
  - (* a = epsilon -> ... *)
  rewrite EQsr in Hmo.
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [q1 q2 th w'' Hr (*[EQq1 EQth EQw'] EQq2*)
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r' th h t Hr (*Hphi [EQq1 EQth EQht] EQq2*)];
  inversion Hr
  as [phi'' EQphi'' EQphi EQr EQsq' | | | |];
  rewrite <- EQphi in Hphi;
  unfold models_phi in Hphi;
  now unfold models_atom in Hphi.

  - (* a = Σφ phi -> ... *)
  assert (Htriv : sigmaRA (QVar q'') = sigmaRA (QVar q'')).
  { trivial. }
  destruct rg as [| rg];
  rewrite EQsr in Hmo;
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [q1 q2 th w'' Hr (*[EQq1 EQth EQw'] EQq2*)
     |q1 q2 phi' th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi' r' th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [(*phi'' EQphi'' EQphi EQr EQsq'*)
     |(*v1 v2 [EQv1 EQv2] EQe EQr EQq2'*)
     |(*v1 v2 [EQv1 EQv2] EQe EQr EQq2'*)
     |v1 phi'' [EQv1 EQphi''] EQphi EQr EQq2'
     |rg' v1 phi'' [EQrg' EQv1 EQphi''] EQphi EQrg EQq2'];
  clear v1 EQv1;
  rewrite <- EQphi in Hphi;
  try apply moveRA_not_update with phi;
  try apply moveRA_update with phi; auto;
  assert (Hsq'sq'' := EQq2');
  rewrite <- EQq2' in EQq2;
  try (rewrite <- EQq2 in Hc2;
  now apply (Hc2 q'') in Htriv);
  apply sigmaRA_QVar_is_injective in EQq2'.

  + (* not update *)
  destruct EQq2' as [[dq''nil dq'nil] | EQq2'];
  try apply (at_most_one_dead_end_state q'' q' dq''nil) in dq'nil;
  try now rewrite <- dq'nil.
  * destruct (finalRA_dec q') as [Hfq' | Hnfq'];
  [ destruct (sigmaRA_q_final q' Hfq') as [Hsq' Hd']
  | destruct (sigmaRA_q_not_final q' Hnfq') as [Hsq' Hd'] ];
  destruct (finalRA_dec q'') as [Hfq'' | Hnfq''];
  [ destruct (sigmaRA_q_final q'' Hfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_not_final q'' Hnfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_final q'' Hfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_not_final q'' Hnfq'') as [Hsq'' Hd''] ];
  rewrite Hsq' in Hsq'sq'';
  rewrite Hsq'' in Hsq'sq''.
  ** split; auto.
  ** injection Hsq'sq''; intros _ He;
  now apply QDVar_is_not_Vend in He.
  ** injection Hsq'sq''; intros _ He;
  symmetry in He;
  now apply QDVar_is_not_Vend in He.
  ** split; intros Hf;
  [apply Hnfq'' in Hf | apply Hnfq' in Hf];
  contradiction.
  * now rewrite <- EQq2'.

  + (* update *)
  rewrite <- EQrg;
  destruct EQq2' as [[Hdq'' Hdq'] | EQq2'];
  try rewrite (at_most_one_dead_end_state q' q'' Hdq' Hdq'');
  auto;
  try now rewrite <- EQq2'.
  destruct (finalRA_dec q') as [Hfq' | Hnfq'];
  [ destruct (sigmaRA_q_final q' Hfq') as [Hsq' Hd']
  | destruct (sigmaRA_q_not_final q' Hnfq') as [Hsq' Hd'] ];
  destruct (finalRA_dec q'') as [Hfq'' | Hnfq''];
  [ destruct (sigmaRA_q_final q'' Hfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_not_final q'' Hnfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_final q'' Hfq'') as [Hsq'' Hd'']
  | destruct (sigmaRA_q_not_final q'' Hnfq'') as [Hsq'' Hd''] ];
  rewrite Hsq' in Hsq'sq'';
  rewrite Hsq'' in Hsq'sq''.
  ** split; auto.
  ** injection Hsq'sq''; intros _ He;
  now apply QDVar_is_not_Vend in He.
  ** injection Hsq'sq''; intros _ He;
  symmetry in He;
  now apply QDVar_is_not_Vend in He.
  ** split; intros Hf;
  [apply Hnfq' in Hf | apply Hnfq'' in Hf];
  contradiction.
Qed.

Lemma QDVar_to_QVar_one_step :
  forall q r t theta w q' theta' w',
  disjunction_of_succ (r :: t) ->
  Forall (fun r => In r (deltaq q)) (r :: t) ->
  moveA_plus_without_QVar
    (sigmaRA (QDVar (r :: t)), theta, w)
    (sigmaRA (QVar q'), theta', w') ->
  moveRA (q, theta, w) (q', theta', w').
Proof.
  intros q r t theta w q' theta' w'.
  intros Hdrt Hin Hmo.
  induction (r :: t) as [| r' t' IHt'].
  - inversion Hdrt as [EQsd|].
  rewrite EQsd in Hmo.
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [q1 q2 th w'' Hr (*[EQq1 EQth EQw'] EQq2*)
     |q1 q2 phi th h t' Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r' th h t' Hr (*Hphi [EQq1 EQth EQht] EQq2*)];
  inversion Hr
  as [phi'' EQphi'' EQphi EQr EQsq' | | | |];
  rewrite <- EQphi in Hphi;
  unfold models_phi in Hphi;
  now unfold models_atom in Hphi.
  - inversion Hdrt as [|r'' t'' EQsd Hdt' [EQr'' EQt'']].
  clear r'' EQr'' t'' EQt''.
  rewrite EQsd in Hmo.
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [q1 q2 th w'' Hr [EQq1 EQth EQw'] [EQq2 EQtheta EQw]
     |q1 q2 phi th h t'' Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r'' th h t'' Hr (*Hphi [EQq1 EQth EQht] EQq2*)];
  inversion Hr
  as [(*phi'' EQphi'' EQphi EQr EQsq'*)
  |v1 v2 [EQv1 EQv2] EQe EQr EQq2'
  |v1 v2 [EQv1 EQv2] EQe EQr EQq2'
  |(*v1 phi'' [EQv1 EQphi''] EQphi EQr EQq2'*)
  |rg' v1 phi'' [EQrg' EQv1 EQphi''] EQphi EQr EQq2'].
  + clear c1 EQc1 c2 EQc2;
  clear q1 EQq1 q2 EQq2 w'' EQw' th EQth;
  clear v1 EQv1 v2 EQv2 EQe EQr.
  destruct (sigmaRA_QVar q') as [EQsq' | EQsq'];
  destruct (sigmaRA_RVar r')
  as [EQsr' | [[q1 [p1 EQsr']] | [rg [q1 [p1 EQsr']]]]];
  rewrite EQsq' in EQq2';
  rewrite EQsr' in EQq2';
  discriminate.
  + clear c1 EQc1 c2 EQc2;
  clear q1 EQq1 q2 EQq2 w'' EQw' th EQth;
  clear v1 EQv1 v2 EQv2 EQe EQr.
  inversion Hdt' as [EQsd' EQt'|r'' t'' EQsd' Hdt'' [EQt' EQt'']];
  rewrite <- EQt' in EQq2';
  rewrite EQsd' in EQq2';
  destruct (sigmaRA_QVar q') as [EQsq' | EQsq'];
  rewrite EQsq' in EQq2'; try discriminate;
  injection EQq2';
  intros Hdv Hrv.
  * now apply RVar_is_not_Vend in Hrv.
  * now apply RVar_is_not_QDVar in Hrv.
  + clear c1 EQc1 c3 EQc3;
  clear q1 EQq1 w'' EQw' th EQth;
  clear v1 EQv1 v2 EQv2 EQe EQr.
  rewrite <- EQq2' in EQq2.
  rewrite <- EQq2 in H23.
  inversion Hin as [| x l Hin' Hit' [EQx EQl]].
  clear x EQx l EQl.
  destruct r' as [[[q1 a] rg] q2'].
  apply deltaq_and_q in Hin' as EQq1.
  rewrite EQq1 in H23.
  rewrite EQq1 in Hin'.
  apply deltaq_is_subset_of_delta in Hin'.
  apply RVar_to_QVar_one_step in H23; auto.
  + clear c1 EQc1 c3 EQc3;
  clear q1 EQq1 w'' EQw' th EQth;
  clear v1 EQv1 v2 EQv2 EQe EQr.
  rewrite <- EQq2' in EQq2.
  rewrite <- EQq2 in H23.
  inversion Hin as [| x l Hin' Hit' [EQx EQl]].
  clear x EQx l EQl.
  apply IHt'; auto.
Qed.

Theorem RA_simulates_sigmaRA_one_step :
  forall q theta w q' theta' w',
  moveA_plus_without_QVar
    (sigmaRA (QVar q), theta, w)
    (sigmaRA (QVar q'), theta', w') ->
  moveRA (q, theta, w) (q', theta', w').
Proof.
  intros q theta w q' theta' w'.
  intros Hmo.
  assert (Hdq := q_disjunction_of_succ q).
  inversion Hmo
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3].
  - (* one move *)
  destruct (sigmaRA_QVar q) as [Hsq | Hsq];
  rewrite Hsq in H12;
  inversion H12
  as [q1 q2 th w'' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  clear v1 EQv1 v2 EQv2 EQe EQr;
  try now apply sigmaRA_QDVar_neq_QVar in EQq2'.
  (* sigmaRA Vend = sigmaRA (QVar q') -> ... *)
  rewrite sigmaRA_end in EQq2'.
  symmetry in EQq2'.
  now apply sigmaRA_QVar_neq_end in EQq2'.
  - (* more than one move *)
  remember (deltaq q) as dq.
  destruct (sigmaRA_QVar q) as [Hsq | Hsq];
  rewrite Hsq in H12;
  inversion H12
  as [q1 q2 th w'' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi r th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr
  as [|v1 v2 [EQv1 EQv2] EQe EQr EQq2'
      |v1 v2 [EQv1 EQv2] EQe EQr EQq2' | |];
  clear v1 EQv1 v2 EQv2 EQe EQr;
  clear c1 EQc1 c3 EQc3;
  rewrite <- EQq2' in EQq2;
  rewrite <- EQq2 in H23;
  try rewrite <- Heqdq in H23.
  + (* c2 = (sigmaRA Vend, ...) -> ... *)
  rewrite sigmaRA_end in H23.
  inversion H23
  as [c2' c3' H23'|c2' c2'' c3' Hc2'' H23' H23''];
  inversion H23'
  as [q1' q2' th' w''' Hr'
     |q1' q2' phi th' h t Hr' Hphi
     |q1' q2' phi r th' h t Hr' Hphi];
  inversion Hr' as [phi' EQphi' EQphi| | | |];
  rewrite <- EQphi in Hphi;
  unfold models_phi in Hphi;
  now unfold models_atom in Hphi.
  + (* c2 = (sigmaRA (QDVar ...), ...) -> ... *)
  destruct dq as [| r dq];
  try now apply QDVar_nil_to_QVar in H23.
  apply (QDVar_to_QVar_one_step q r dq); auto.
  rewrite Heqdq; apply incl_Forall_in_iff; apply incl_refl.
  + (* c2 = (sigmaRA (QDVar ...), ...) -> ... *)
  destruct dq as [| r dq];
  try now apply QDVar_nil_to_QVar in H23.
  apply (QDVar_to_QVar_one_step q r dq); auto.
  rewrite Heqdq; apply incl_Forall_in_iff; apply incl_refl.
  + (* c2 = (sigmaRA (QDVar ...), ...) -> ... *)
  destruct dq as [| r dq];
  try now apply QDVar_nil_to_QVar in H23.
  apply (QDVar_to_QVar_one_step q r dq); auto.
  rewrite Heqdq; apply incl_Forall_in_iff; apply incl_refl.
Qed.

End RASimulatesSigma.
