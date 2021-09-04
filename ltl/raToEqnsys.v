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
  (exists v1 v2,
   sigmaRA (QDVar l) = (var v1 .\/ var v2)).
Proof.
  intros l H.
  inversion H as [| r t].
  - now left.
  - right.
  exists (RVar r).
  now exists (QDVar t).
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

End SigmaSimulatesRA.

Section RASimulatesSigma.

Inductive moveA_star_without_QVar
  : Config -> Config -> Prop :=
  | moveA_star_without_QVar_ref :
    forall c1,
    moveA_star_without_QVar c1 c1
  | moveA_star_without_QVar_trans :
    forall c1 c2 c3 : Config,
    (forall q,
     match c2 with (q2, _, _) =>
       (q2 <> (sigmaRA (QVar q))) end) ->
    moveA sigmaRA c1 c2 ->
    moveA_star_without_QVar c2 c3 ->
    moveA_star_without_QVar c1 c3
  | moveA_star_without_QVar_step :
    forall c1 c2,
    moveA sigmaRA c1 c2 ->
    moveA_star_without_QVar c1 c2
  .

Axiom sigmaRA_QVar_dec :
  forall q',
  {exists q, q' = (sigmaRA (QVar q))} +
  {forall q, q' <> (sigmaRA (QVar q))}.

Lemma moveA_star_can_be_split_at_QVar :
  forall c1 c3,
  moveA_star sigmaRA c1 c3 ->
  moveA_star_without_QVar c1 c3 \/
  exists c2,
    (exists q, match c2 with (q2, _, _) =>
               q2 = (sigmaRA (QVar q)) end) /\
    moveA_star_without_QVar c1 c2 /\
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
  -- now apply moveA_star_without_QVar_step.
  * (* (forall q, q2 <> sigmaRA (QVar q)) -> ... *)
  left.
  apply moveA_star_without_QVar_trans
  with (q2, th, w'); auto.
  + (* exists c2', moveA_star_without_QVar c2 c2' /\ ... -> ... *)
  destruct c2 as [[q2 th] w'].
  destruct (sigmaRA_QVar_dec q2) as [[q Hq2] | Hq2].
  * (* q2 = sigmaRA (QVar q) -> ... *)
  right.
  exists (q2, th, w').
  split; [| split]; auto.
  -- now exists q.
  -- now apply moveA_star_without_QVar_step.
  * (* (forall q, q2 <> sigmaRA (QVar q)) -> ... *)
  right.
  exists c2'.
  split; [| split]; auto.
  apply moveA_star_without_QVar_trans
  with (q2, th, w'); auto.
Qed.

Lemma RVar_to_end_without_QVar :
  forall r theta w theta',
  ~ moveA_star_without_QVar
    (sigmaRA (RVar r), theta, w)
    (φ [END], theta', nil).
Proof.
  intros r theta w theta' H.
  inversion H
  as [c1 EQc1 [EQsr EQtheta EQw]
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3
     |c1 c2 H12 EQc1 EQc2].
  - (* sigmaRA (RVar r) = φ [END] -> ... *)
  now apply sigmaRA_RVar_neq_end in EQsr.
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
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3
     |c1 c2 H12 EQc1 EQc2].
  * (* sigmaRA (QDVar (deltaq q)) = (φ [END]) -> ... *)
  rewrite EQsd in EQsd'.
  now apply ff_neq_end in EQsd'.
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
  * (* c2 = (φ [END], theta', nil) -> ... *)
  rewrite EQsd in H12.
  inversion H12
  as [q1 q2 th w' Hr [EQq1 EQth EQw'] EQq2
     |q1 q2 phi th h t Hr Hphi [EQq1 EQth EQht] EQq2
     |q1 q2 phi rg th h t Hr Hphi [EQq1 EQth EQht] EQq2];
  inversion Hr.
  + (* deltaq q = r :: t -> ... *)
  clear r' EQr' t' EQt'.
  inversion H
  as [c1 EQc1 [EQsd' EQtheta EQw]
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3
     |c1 c2 H12 EQc1 EQc2].
  * (* sigmaRA (QDVar (deltaq q)) = (φ [END]) -> ... *)
  rewrite EQsd in EQsd'.
  discriminate.
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
  now apply RVar_to_end_without_QVar in H23.
  -- (* c2 = (sigmaRA (QDVar t), ...) -> ... *)
  now apply IHt.
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
Qed.

Lemma RA_simulates_sigmaRA_end :
  forall q theta w theta',
  moveA_star_without_QVar (sigmaRA (QVar q), theta, w) (φ [END], theta', nil) ->
  finalRA q.
Proof.
  intros q theta w theta' Hmo.
  inversion Hmo
  as [c1 EQc1 [Hsq EQth EQw]
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3
     |c1 c2 H12 EQc1 EQc2].
  - (* sigmaRA (QVar q) = φ [END] -> ... *)
  destruct (finalRA_dec q) as [Hfq | Hnfq];
  try apply Hfq.
  destruct (sigmaRA_q_not_final q Hnfq) as [Hsq' Hd].
  rewrite Hsq' in Hsq.
  discriminate.
  - (* moveA sigmaRA (sigmaRA (QVar q), ...) c2 -> ... *)
  destruct (finalRA_dec q) as [Hfq | Hnfq];
  try apply Hfq.
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
  now apply QDVar_to_end_without_QVar in H23.
  - (* c2 = (φ [END], theta', nil) -> ... *)
  destruct (finalRA_dec q) as [Hfq | Hnfq];
  try apply Hfq.
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
Qed.

End RASimulatesSigma.
