(*
 * Paper for ICTAC 2021: The Realizability Problem over RPDT.
 * PDA simulating RPDA
 *)

Require Export Nat Arith.EqNat.

(* Equivalence Relations *)

Inductive Top : Set := top.
Inductive register :=
  | X  (i : nat)
  | X' (i : nat)
  | Xtop.
Definition X_ (xi : nat + Top) :=
  match xi with
  | inl i => X i
  | inr t => Xtop
  end.
      
Definition Phi := register -> register -> Prop.

Definition is_reflexive  (phi : Phi) : Prop := forall x, phi x x.
Definition is_symmetric  (phi : Phi) : Prop := forall x y, phi x y -> phi y x.
Definition is_transitive (phi : Phi) : Prop :=
  forall x y z, phi x y /\ phi y z -> phi x z.
Definition is_equiv_rel   (phi : Phi) : Prop :=
  is_reflexive phi /\ is_symmetric phi /\ is_transitive phi.

Axiom Phi_extensionality :
  forall phi phi' : Phi,
    (forall x y, phi x y <-> phi' x y) -> phi = phi'.
  
Definition phi_zero (a b : register) := True.

(* Composition *)

Definition composable (phi1 phi2 : Phi) : Prop :=
  forall i j, phi1 (X' i) (X' j) <-> phi2 (X i) (X j).

Definition composableT (phi1 phi2 : Phi) : Prop :=
  composable phi1 phi2 /\
  forall i, phi1 (X' i) Xtop <-> phi2 (X i) Xtop.

(* Assignments *)

Parameter D : Set.
Definition Theta := nat -> D.
Definition Asgn := nat -> bool.  (* a subset of nat *)

Definition update (theta : Theta) (asgn : Asgn) (d : D) : Theta :=
  fun j : nat => if asgn j then d else theta j.

Axiom Theta_extensionality :
  forall theta theta' : Theta,
    (forall i, theta i = theta' i) -> theta = theta'.


Axiom outside_data_exists :
  forall (theta : Theta) e, exists d, d <> e /\ forall i, theta i <> d.

Axiom outside_data_exists' :
  forall theta theta': Theta, exists d : D,
    (forall i, theta i <> d) /\ (forall i, theta' i<> d).

(* Construct a phi from theta, d, theta' *)
Definition phi_matches (theta : Theta) (d : D) (theta' : Theta) : Phi :=
  fun x y : register =>
    match x, y with
    | X i,  X j  => theta i = theta j
    | X i,  Xtop => theta i = d
    | X i,  X' j => theta i = theta' j
    | Xtop, X j  => d = theta j
    | Xtop, Xtop => d = d
    | Xtop, X' j => d = theta' j
    | X' i, X j  => theta' i = theta j
    | X' i, Xtop => theta' i = d
    | X' i, X' j => theta' i = theta' j
    end.

(* Construct a phi' in Phi_eq_j composable with phi *)
Definition phi_to_Phi_eq_j (j : nat) (phi : Phi) : Phi :=
  fun x y : register =>
    match x, y with
    | X i,  X h  => phi (X' i) (X' h)
    | X i,  Xtop => phi (X' i) (X' j)
    | X i,  X' h => phi (X' i) (X' h)
    | Xtop, X h  => phi (X' j) (X' h)
    | Xtop, Xtop => phi (X' j) (X' j)
    | Xtop, X' h => phi (X' j) (X' h)
    | X' i, X h  => phi (X' i) (X' h)
    | X' i, Xtop => phi (X' i) (X' j)
    | X' i, X' h => phi (X' i) (X' h)
    end.


(* Tst *)
Definition Tst := (nat + Top) -> bool.  (* a subset of registers *)

Axiom tst_is_empty_or_not :
  forall tst : Tst, (forall xi, tst xi <> true) \/ exists xi, tst xi = true.
Axiom asgn_is_empty_or_not :
  forall asgn : Asgn, (forall i, asgn i <> true) \/ exists i, asgn i = true.

Axiom Tst_extensionality :
  forall tst tst' : Tst, (forall xi, tst xi = tst' xi) -> tst = tst'.

Definition Phi_tst_asgn (tst : Tst) (asgn : Asgn) (phi : Phi) :=
  (forall xi, tst xi = true ->
     forall xj, tst xj = true <-> phi (X_ xi) (X_ xj)) /\
  (forall i, asgn i = true ->
     forall xj, tst xj = true <-> phi (X_ xj) (X' i)) /\
  (forall i j, asgn i = true /\ asgn j = true -> phi (X' i) (X' j)) /\
  (forall i, asgn i <> true -> phi (X i) (X' i)).

Definition Phi_eq_j (j : nat) (phi : Phi) :=
  phi Xtop (X j) /\ forall i, phi (X i) (X' i).

(* models *)

Class Models (A B : Type) := models : A -> B -> Prop.
Notation "S '|=' T" := (models S T) (at level 59).

Instance Theta_D_D_models_Tst : Models (Theta * D * D) Tst :=
  { models theta_d_e tst :=
      match theta_d_e with
      | (theta, d, e) => (forall i, theta i = d <-> tst (inl i) = true) /\
                         (e = d <-> tst (inr top) = true)
      end }.
Instance two_Theta_D_models_Phi : Models (Theta * D * Theta) Phi :=
  { models triple phi :=
      match triple with
      | (theta, d, theta') =>
          (forall i j, theta  i = theta  j <-> phi (X  i) (X  j)) /\
          (forall i j, theta' i = theta' j <-> phi (X' i) (X' j)) /\
          (forall i j, theta  i = theta' j <-> phi (X  i) (X' j)) /\
          (forall i,   theta  i = d <-> phi (X  i) Xtop) /\
          (forall i,   theta' i = d <-> phi (X' i) Xtop)
      end }.

(* Utilities *)

Lemma not_true_is_false :
  forall b : bool, b <> true <-> b = false.
Proof.
  intros b.
  split.
  - (* b <> true -> b = false *)
  case b; try contradiction; auto.
  - (* b = false -> b <> true *)
  intros H.
  rewrite H.
  discriminate.
Qed.

Lemma false_eq_false :
  forall b1 b2 : bool,
  (b1 = true <-> b2 = true) -> b1 = false -> b2 = false.
Proof.
  intros b1 b2.
  case b2;
  intros [Heq1 Heq2] Hfalse;
  auto.
  assert (H : b1 = true).
  { apply Heq2. reflexivity. }
  rewrite H in Hfalse.
  exact Hfalse.
Qed.

(* Properties *)

Lemma theta_e_theta'_models_phi_matches :
  forall theta theta' e,
  (theta, e, theta') |= phi_matches theta e theta'.
Proof.
  intros theta theta' e.
  unfold models;
  unfold two_Theta_D_models_Phi;
  unfold phi_matches.
  repeat split; auto.
Qed.

Lemma phi_matches_is_equiv_rel :
  forall theta theta' e,
  is_equiv_rel (phi_matches theta e theta').
Proof.
  intros theta theta' e.
  unfold is_equiv_rel.
  split; [ | split].
  - (* is_reflexive *)
    unfold is_reflexive.
    intros x.
    case x; unfold phi_matches; auto.
  - (* is_symmetric *)
    unfold is_symmetric.
    intros x y.
    case x, y; unfold phi_matches; auto.
  - (* is_transitive *)
    unfold is_transitive.
    intros x y z.
    case x, y, z; unfold phi_matches;
    intros [H1 H2]; try rewrite H1; auto.
Qed.

Lemma phi_matches_is_Phi_test_asgn :
  forall theta theta' d e tst asgn,
  (theta, d, e) |= tst /\ theta' = update theta asgn d
  ->
  Phi_tst_asgn tst asgn (phi_matches theta e theta').
Proof.
  intros theta theta' d e tst asgn.
  intros [Hmo Hup].
  unfold models in Hmo;
  unfold Theta_D_D_models_Tst in Hmo.
  destruct Hmo as [Hmo_th Hmo_e].

  unfold Phi_tst_asgn.
  split; [| split; [| split]].
  - (* forall xi, tst xi = true -> forall xj, tst xj = true <-> phi xi xj *)
    intros xi.
    case xi; clear xi.
  + (* xi = inl i *)
    intros i Hxi xj.
    apply Hmo_th in Hxi.
    case xj; clear xj;
    unfold X_;
    unfold phi_matches.
  * (* xj = inl j *)
    intros j.
    rewrite<- (Hmo_th j).
    rewrite Hxi.
    split; auto.
  * (* xj = inr top *)
    intros t;
    case t; clear t.
    rewrite<- Hmo_e.
    rewrite Hxi.
    split; auto.
  + (* xi = top *)
    intros t; case t; clear t.
    intros Htop.
    apply Hmo_e in Htop.
    rewrite Htop.
    intros xj;
    case xj; clear xj;
    unfold X_;
    unfold phi_matches.
  * (* xi = top, xj = inl j *)
    intros j.
    rewrite<- (Hmo_th j).
    split; auto.
  * (* xi = top, xj = top *)
    intros t; case t; clear t.
    rewrite<- Hmo_e.
    split; auto.

  - (* forall i, asgn i = true -> forall xj, tst xj = true <-> phi ... *)
    rewrite Hup.
    intros i Ha xj.
    case xj; clear xj;
    unfold X_;
    unfold phi_matches;
    unfold update;
    rewrite Ha.
  + (* xj = inl j *)
    intros j.
    rewrite (Hmo_th j).
    reflexivity.
  + (* xj = inr top *)
    intros t; case t; clear t.
    rewrite Hmo_e.
    reflexivity.

  - (* forall i j, asgn i = true /\ asgn j = true -> phi X'i X'j *)
    intros i j [Hai Haj].
    rewrite Hup;
    unfold phi_matches;
    unfold update.
    rewrite Hai;
    rewrite Haj.
    reflexivity.

  - (* forall i, asgn i <> true -> phi Xi X'i *)
    intros i Hai.
    rewrite Hup;
    unfold phi_matches;
    unfold update.
    case_eq (asgn i); try contradiction;
    auto.
Qed.

Lemma meanings_of_phi_tst_asgn_1 :
  forall theta theta' e tst asgn,
  (exists phi,
     is_equiv_rel phi /\
     Phi_tst_asgn tst asgn phi /\
     (theta, e, theta') |= phi)
  ->
  (exists d,
    (theta, d, e) |= tst /\ theta' = update theta asgn d).
Proof.
  intros theta theta' e tst asgn.

  intros [phi [Peq [Hph Hmo]]].
  destruct Peq as [Pref [Psym Ptra]].
  unfold Phi_tst_asgn in Hph.
  destruct Hph as [HpL [HpLR [HpR HpThru]]].
  unfold models in Hmo;
  unfold two_Theta_D_models_Phi in Hmo.
  destruct Hmo as [HmL [HmR [HmLR [HmLT HmRT]]]].

  destruct (tst_is_empty_or_not tst) as [Temp | Tnotemp].
  destruct (asgn_is_empty_or_not asgn) as [Aemp | Anotemp].

  - (* tst & asgn are empty *)
    destruct (outside_data_exists theta e) as [d [Hout_e Hout_th]].
    exists d.  (* outside data *)
    split.
  + (* (theta, d, e) |= tst *)
    unfold models.
    unfold Theta_D_D_models_Tst.
    split.
  * (* forall i, theta i = d <-> tst i = true *)
    intros i.
    split.
  -- intros H;
    apply Hout_th in H; contradiction.
  -- intros H;
    apply Temp in H; contradiction.
  * (* e = d <-> tst top = true *)
    split.
  -- auto.
  -- intros H;
    apply Temp in H; contradiction.
  + (* theta' = update theta asgn d *)
    apply Theta_extensionality.
    intros i.
    unfold update.
    case_eq (asgn i).
  * (* asgn i = true -> theta' i = d *)
    intros H;
    apply Aemp in H; contradiction.
  * (* asgn i = false -> theta' i = theta i *)
    intros H.
    symmetry.
    apply HmLR.
    apply HpThru.
    auto.
  - (* tst is empty, asgn is not empty *)
    destruct Anotemp as [j Anotemp].
    exists (theta' j).
    split.
  + (* (theta, theta' j, e) |= tst *)
    unfold models.
    unfold Theta_D_D_models_Tst.
    split.
  * (* forall i, theta i = theta' j <-> tst i = true *)
    intros i.
    split.
  -- (* theta i = theta' j -> tst i = true *)
    intros H.
    apply HmLR in H.
    apply (HpLR j Anotemp (inl i)) in H.
    exact H.
  -- (* tst i = true -> theta i = theta' j *)
    intros H.
    apply HmLR.
    apply (HpLR j Anotemp (inl i)).
    exact H.
  * (* e = theta' j <-> tst top = true *)
    split.
  -- (* e = theta' j -> tst top = true *)
    intros H.
    symmetry in H.
    apply HmRT in H.
    apply Psym in H.
    apply (HpLR j Anotemp (inr top)) in H.
    exact H.
  -- (* tst top = true -> e = theta' j *)
    intros H;
    apply Temp in H; contradiction.
  + (* theta' = update theta asgn (theta' j) *)
    apply Theta_extensionality.
    intros i.
    unfold update.
    case_eq (asgn i).
  * (* asgn i = true -> theta' i = theta' j *)
    intros H.
    apply HmR.
    apply HpR.
    auto.
  * (* asgn i = false -> theta' i = theta i *)
    intros H.
    symmetry.
    apply HmLR.
    apply HpThru.    
    rewrite H.
    discriminate.
  - (* tst is not empty *)
    destruct Tnotemp as [xi Hxi].
    generalize Hxi;  (* for doing case xi *)
    clear Hxi.
    case xi.
  + (* tst i = true -> exists d, ... *)
    intros i Hxi; clear xi.
    exists (theta i).
    split.
  * (* (theta, theta i, e) |= tst *)
    unfold models;
    unfold Theta_D_D_models_Tst.
    split.
  -- (* theta j = theta i <-> tst j = true *)
    intros j.
    split.
  ++ (* theta j = theta i -> tst j = true *)
    intros H.
    apply HmL in H.
    apply Psym in H.
    apply (HpL (inl i) Hxi (inl j)) in H.
    exact H.
  ++ (* tst j = true -> theta j = theta i *)
    intros H.
    apply HmL.
    apply Psym.
    apply (HpL (inl i) Hxi (inl j)).
    exact H.
  -- (* e = theta i <-> tst top = true *)
    split.
  ++ (* e = theta i -> tst top = true *)
    intros H.
    symmetry in H.
    apply HmLT in H.
    apply (HpL (inl i) Hxi (inr top)) in H.
    exact H.
  ++ (* tst top = true -> e = theta i *)
    intros H.
    symmetry.
    apply HmLT.
    apply (HpL (inl i) Hxi (inr top)).
    exact H.
  * (* theta' = update theta asgn (theta i) *)
    apply Theta_extensionality.
    intros j.
    unfold update.
    case_eq (asgn j).
  -- (* asgn j = true -> theta' j = theta i *)
    intros H.
    symmetry.
    apply HmLR.
    apply (HpLR j H (inl i)).
    exact Hxi.
  -- (* asgn j = false -> theta' j = theta j *)
    intros H.
    symmetry.
    apply HmLR.
    apply (HpThru j).
    rewrite H.
    discriminate.
  + (* tst top = true -> exists d, ... *)
    intros t; case t; clear t.
    intros Htop; clear xi.
    exists e.
    split.
  * (* (theta, e, e) |= tst *)
    unfold models;
    unfold Theta_D_D_models_Tst.
    split.
  -- (* forall i, theta i = e <-> tst i = true *)
    intros i.
    split.
  ++ (* theta i = e -> tst i = true *)
    intros H.
    apply HmLT in H.
    apply Psym in H.
    apply (HpL (inr top) Htop (inl i)) in H.
    exact H.
  ++ (* tst i = true -> theta i = e *)
    intros H.
    apply HmLT.
    apply Psym.
    apply (HpL (inr top) Htop (inl i)).
    exact H.
  -- (* e = e <-> tst top = true *)
    split; auto.
  * (* theta' = update theta asgn e *)
    apply Theta_extensionality.
    intros j.
    unfold update.
    case_eq (asgn j).
  -- (* asgn j = true -> theta' j = e *)
    intros H.
    apply HmRT.
    apply Psym.
    apply (HpLR j H (inr top)).
    exact Htop.
  -- (* asgn j = false -> theta' j = theta j *)
    intros H.
    symmetry.
    apply HmLR.
    apply HpThru.
    rewrite H.
    discriminate.
Qed.

Lemma meanings_of_phi_tst_asgn_2 :
  forall theta theta' e tst asgn,
  (exists d,
    (theta, d, e) |= tst /\ theta' = update theta asgn d)
  ->
  (exists phi,
     is_equiv_rel phi /\
     Phi_tst_asgn tst asgn phi /\
     (theta, e, theta') |= phi).
Proof.
  intros theta theta' e tst asgn.
  intros [d Hmo_up].
  exists (phi_matches theta e theta').
  split; [| split].
  - (* is_equiv_rel *)
    apply phi_matches_is_equiv_rel.
  - (* Phi_tst_asgn tst asgn phi *)
    generalize Hmo_up.
    apply phi_matches_is_Phi_test_asgn.
  - (* (theta, e, theta') |= phi_matches theta e theta' *)
    apply theta_e_theta'_models_phi_matches.
Qed.

Theorem meanings_of_phi_tst_asgn :
  forall theta theta' e tst asgn,
  (exists phi,
     is_equiv_rel phi /\
     Phi_tst_asgn tst asgn phi /\
     (theta, e, theta') |= phi)
  <->
  (exists d,
    (theta, d, e) |= tst /\ theta' = update theta asgn d).
Proof.
  split.
  - apply meanings_of_phi_tst_asgn_1.
  - apply meanings_of_phi_tst_asgn_2.
Qed.

(* Phi_eq_j *)

Lemma phi_matches_is_Phi_eq_j :
  forall theta j,
  Phi_eq_j j (phi_matches theta (theta j) theta).
Proof.
  intros theta j.
  unfold Phi_eq_j.
  unfold phi_matches.
  auto.
Qed.

Lemma meanings_of_phi_eq_j_1 :
  forall theta theta' e j,
  (exists phi,
     is_equiv_rel phi /\
     Phi_eq_j j phi /\
     (theta, e, theta') |= phi)
  ->
  (theta = theta' /\ theta j = e).
Proof.
  intros theta theta' e j.
  intros [phi [Heq [Hphi Hmo]]].
  unfold is_equiv_rel in Heq.
  destruct Heq as [Pref [Psym Ptra]].
  unfold Phi_eq_j in Hphi.
  destruct Hphi as [HphiT Hphi].
  unfold models in Hmo;
  unfold two_Theta_D_models_Phi in Hmo.
  destruct Hmo as [HmoL [HmoR [HmoLR [HmoLT HmoRT]]]].

  split.
  - (* theta = theta' *)
  apply Theta_extensionality.
  intros i.
  apply HmoLR.
  apply Hphi.
  - (* theta j = e *)
  apply HmoLT.
  apply Psym.
  apply HphiT.
Qed.

Lemma meanings_of_phi_eq_j_2 :
  forall theta theta' e j,
  (theta = theta' /\ theta j = e)
  ->
  (exists phi,
     is_equiv_rel phi /\
     Phi_eq_j j phi /\
     (theta, e, theta') |= phi).
Proof.
  intros theta theta' e j.
  intros [Hth' Hthj].
  exists (phi_matches theta e theta).
  split; [| split].
  - (* is_equiv_rel phi *)
  apply phi_matches_is_equiv_rel.
  - (* Phi_eq_j j phi *)
  symmetry in Hthj.
  rewrite Hthj.
  apply phi_matches_is_Phi_eq_j.
  - (* (theta, e, theta') |= phi *)
  symmetry in Hth'.
  rewrite Hth'.
  apply theta_e_theta'_models_phi_matches.
Qed.

Theorem meanings_of_phi_eq_j :
  forall theta theta' e j,
  (exists phi,
     is_equiv_rel phi /\
     Phi_eq_j j phi /\
     (theta, e, theta') |= phi)
  <->
  (theta = theta' /\ theta j = e).
Proof.
  split.
  - apply meanings_of_phi_eq_j_1.
  - apply meanings_of_phi_eq_j_2.
Qed.

(* Composable *)

Theorem at_most_one_Phi_tst_asgn :
  forall tst asgn phi phi1 phi2,
  is_equiv_rel phi1 /\ is_equiv_rel phi2 ->
  composableT phi phi1 /\ Phi_tst_asgn tst asgn phi1 ->
  composableT phi phi2 /\ Phi_tst_asgn tst asgn phi2
  -> phi1 = phi2.
Proof.
  intros tst asgn phi phi1 phi2.
  intros [P1eq P2eq].
  intros [Hco1 Hphi1] [Hco2 Hphi2].

  unfold is_equiv_rel in P1eq.
  destruct P1eq as [P1ref [P1sym P1tra]].
  unfold is_equiv_rel in P2eq.
  destruct P2eq as [P2ref [P2sym P2tra]].

  unfold composableT in Hco1.
  unfold composable in Hco1.
  destruct Hco1 as [Hco1 Hco1T].
  unfold composableT in Hco2.
  unfold composable in Hco2.
  destruct Hco2 as [Hco2 Hco2T].

  unfold Phi_tst_asgn in Hphi1;
  destruct Hphi1 as [Hp1L [Hp1LR [Hp1R Hp1Thru]]].
  unfold Phi_tst_asgn in Hphi2;
  destruct Hphi2 as [Hp2L [Hp2LR [Hp2R Hp2Thru]]].

  assert (Haf: forall i, asgn i = false -> asgn i <> true).
  { intros i1 Haf. rewrite Haf. discriminate. }

  assert (HXjX'i: forall i j, phi1 (X j) (X' i) <-> phi2 (X j) (X' i)).
  {
  intros i j.
  case_eq (asgn i); intro Hai.
  + (* asgn i = true -> ... *)
  assert (Hp1' := Hp1LR i Hai (inl j)).
  unfold X_ in Hp1'.
  rewrite<- Hp1'.
  assert (Hp2' := Hp2LR i Hai (inl j)).
  unfold X_ in Hp2'.
  rewrite<- Hp2'.
  reflexivity.
  + (* asgn i = false -> ... *)
  assert (Hai': asgn i <> true).
  { rewrite Hai. discriminate. }
  assert (Hp1' := Hp1Thru i Hai').
  assert (Hp2' := Hp2Thru i Hai').
  apply P1sym in Hp1'.
  apply P2sym in Hp2'.
  split.
  * intros H'.
  apply (P2tra _ (X i)).
  split.
  -- apply Hco2.
  apply Hco1.
  apply (P1tra _ (X' i)).
  auto.
  -- apply Hp2Thru.
  auto.
  * intros H'.
  apply (P1tra _ (X i)).
  split.
  -- apply Hco1.
  apply Hco2.
  apply (P2tra _ (X' i)).
  auto.
  -- apply Hp1Thru.
  auto.
  }

  assert (HX'iXtop : forall i, phi1 (X' i) Xtop <-> phi2 (X' i) Xtop).
  {
  intro i.
  case_eq (asgn i);
  intros Hai.
  + (* asgn i = true -> ... *)
  assert (Hp1' := Hp1LR i Hai (inr top)).
  unfold X_ in Hp1'.
  assert (Hp2' := Hp2LR i Hai (inr top)).
  unfold X_ in Hp2'.
  rewrite Hp1' in Hp2'.
  split;
  intros H';
  [apply P2sym | apply P1sym];
  apply Hp2';
  auto.
  + (* asgn i = false -> ... *)
  apply Haf in Hai.
  assert (Hp1i : phi1 (X i) (X' i)).
  { apply Hp1Thru. auto. }
  assert (Hp2i : phi2 (X i) (X' i)).
  { apply Hp2Thru. auto. }
  split.
  * intros H'.
  apply (P2tra _ (X i)).
  split; auto.
  apply Hco2T.
  apply Hco1T.
  apply (P1tra _ (X' i)).
  split; auto.
  * intros H'.
  apply (P1tra _ (X i)).
  split; auto.
  apply Hco1T.
  apply Hco2T.
  apply (P2tra _ (X' i)).
  split; auto.
  }

  apply Phi_extensionality.
  intros x y.
  case x; case y;
  try intro i; try intro j;
  try (rewrite<- Hco1; rewrite<- Hco2);
  try (rewrite<- Hco1T; rewrite<- Hco2T);
  try reflexivity.

  - (* phi1 (X j) (X' i) <-> phi2 (X j) (X' i) *)
  apply HXjX'i.
  - (* phi1 (X' j) (X i) <-> phi2 (X' j) (X i) *)
  split.
  + intros Hp1.
  apply P2sym.
  apply HXjX'i.
  apply P1sym.
  exact Hp1.
  + intros Hp2.
  apply P1sym.
  apply HXjX'i.
  apply P2sym.
  exact Hp2.

  - (* phi1 (X' j) (X' i) <-> phi2 (X' j) (X' i) *)
  case_eq (asgn i); case_eq (asgn j);
  intros Haj Hai.
  + (* asgn j = true, asgn i = true -> ... *)
  split;
  intros H';
  [apply Hp2R | apply Hp1R];
  auto.
  + (* asgn j = false, asgn i = true -> ... *)
  apply Haf in Haj.
  assert (Hp1' : phi1 (X j) (X' j)).
  { apply Hp1Thru. auto. }
  assert (Hp2' : phi2 (X j) (X' j)).
  { apply Hp2Thru. auto. }

  assert (Hp1'' := Hp1LR i Hai (inl j)).
  unfold X_ in Hp1''.
  assert (Hp2'' := Hp2LR i Hai (inl j)).
  unfold X_ in Hp2''.
  rewrite Hp1'' in Hp2''.
  split.
  * intros H'.
  apply (P2tra _ (X j)).
  split; [| apply Hp2'']; auto.
  apply (P1tra _ (X' j)).
  split; auto.
  * intros H'.
  apply (P1tra _ (X j)).
  split; [| apply Hp2'']; auto.
  apply (P2tra _ (X' j)).
  split; auto.

  + (* asgn j = true, asgn i = false -> ... *)
  apply Haf in Hai.
  assert (Hp1' : phi1 (X i) (X' i)).
  { apply Hp1Thru. auto. }
  assert (Hp2' : phi2 (X i) (X' i)).
  { apply Hp2Thru. auto. }

  assert (Hp1'' := Hp1LR j Haj (inl i)).
  unfold X_ in Hp1''.
  assert (Hp2'' := Hp2LR j Haj (inl i)).
  unfold X_ in Hp2''.
  rewrite Hp1'' in Hp2''.
  split.
  * intros H'.
  apply (P2tra _ (X i)).
  split; [apply P2sym ; apply Hp2'' |]; auto.
  apply (P1tra _ (X' i)).
  split; auto.
  * intros H'.
  apply (P1tra _ (X i)).
  split; [apply P1sym ; apply Hp2'' |]; auto.
  apply (P2tra _ (X' i)).
  split; auto.

  + (* asgn j = false, asgn i = false -> ... *)
  apply Haf in Hai.
  assert (Hp1i : phi1 (X i) (X' i)).
  { apply Hp1Thru. auto. }
  assert (Hp2i : phi2 (X i) (X' i)).
  { apply Hp2Thru. auto. }
  apply Haf in Haj.
  assert (Hp1j : phi1 (X j) (X' j)).
  { apply Hp1Thru. auto. }
  assert (Hp2j : phi2 (X j) (X' j)).
  { apply Hp2Thru. auto. }
  split.
  * intros H'.
  apply (P2tra _ (X i)).
  split; auto.
  apply P2sym.
  apply HXjX'i.
  apply (P1tra _ (X' i)).
  split; auto.
  * intros H'.
  apply (P1tra _ (X i)).
  split; auto.
  apply P1sym.
  apply HXjX'i.
  apply (P2tra _ (X' i)).
  split; auto.

  - (* phi1 (X' i) Xtop <-> phi2 (X' i) Xtop *)
  apply HX'iXtop.

  - (* phi1 Xtop (X i) <-> phi2 Xtop (X i) *)
  split;
  intros H';
  [apply P2sym | apply P1sym];
  [apply Hco2T | apply Hco1T];
  [apply Hco1T | apply Hco2T];
  auto.

  - (* phi1 Xtop (X' i) <-> phi2 Xtop (X' i) *)
  split;
  intros H';
  [apply P2sym | apply P1sym];
  apply HX'iXtop;
  auto.

  - (* phi1 Xtop Xtop <-> phi2 Xtop Xtop *)
  split;
  intros H';
  [apply P2ref | apply P1ref].
Qed.

Theorem at_most_one_Phi_eq_j :
  forall j phi phi1 phi2,
  is_equiv_rel phi1 /\ is_equiv_rel phi2 ->
  composable phi phi1 /\ Phi_eq_j j phi1 ->
  composable phi phi2 /\ Phi_eq_j j phi2
  -> phi1 = phi2.
Proof.
  intros j phi phi1 phi2.
  intros [P1eq P2eq].
  intros [Hco1 Hphi1] [Hco2 Hphi2].

  unfold is_equiv_rel in P1eq.
  destruct P1eq as [P1ref [P1sym P1tra]].
  unfold is_equiv_rel in P2eq.
  destruct P2eq as [P2ref [P2sym P2tra]].

  unfold composable in Hco1.
  unfold composable in Hco2.

  unfold Phi_eq_j in Hphi1;
  destruct Hphi1 as [Hphi1T Hphi1].
  unfold Phi_eq_j in Hphi2;
  destruct Hphi2 as [Hphi2T Hphi2].

  assert (HXhX'i : forall h i, phi1 (X h) (X' i) <-> phi2 (X h) (X' i)).
  {
  split; intro H.
  + (* phi1 (X h) (X' i) -> phi2 (X h) (X' i) *)
  apply (P2tra _ (X i)).
  split.
  * (* phi2 (X h) (X i) *)
  apply Hco2.
  apply Hco1.
  apply (P1tra _ (X' i)).
  auto.
  * (* phi2 (X i) (X' i) *)
  apply Hphi2.
  + (* phi2 (X h) (X' i) -> phi1 (X h) (X' i) *)
  apply (P1tra _ (X i)).
  split.
  * (* phi1 (X h) (X i) *)
  apply Hco1.
  apply Hco2.
  apply (P2tra _ (X' i)).
  auto.
  * (* phi1 (X i) (X' i) *)
  apply Hphi1.
  }

  assert (HXiXtop : forall i, phi1 (X i) Xtop <-> phi2 (X i) Xtop).
  {
  split; intro H.
  + (* phi1 (X i) Xtop -> phi2 (X i) Xtop *)
  apply (P2tra _ (X j)).
  split.
  * (* phi2 (X i) (X j) *)
  apply Hco2.
  apply Hco1.
  apply (P1tra _ Xtop).
  auto.
  * (* phi2 (X j) Xtop *)
  auto.
  + (* phi2 (X i) Xtop -> phi1 (X i) Xtop *)
  apply (P1tra _ (X j)).
  split.
  * (* phi1 (X i) (X j) *)
  apply Hco1.
  apply Hco2.
  apply (P2tra _ Xtop).
  auto.
  * (* phi1 (X j) Xtop *)
  auto.
  }

  apply Phi_extensionality.
  intros x y.
  case x; case y;
  try intro i; try intro h;
  try (rewrite<- Hco1; rewrite<- Hco2);
  try (rewrite<- Hco1T; rewrite<- Hco2T);
  try reflexivity.

  - (* phi1 (X h) (X' i) <-> phi2 (X h) (X' i) *)
  apply HXhX'i.
  - (* phi1 (X i) Xtop <-> phi2 (X i) Xtop *)
  apply HXiXtop.

  - (* phi1 (X' h) (X i) <-> phi2 (X' h) (X i) *)
  split.
  + intros Hp1.
  apply P2sym.
  apply HXhX'i.
  apply P1sym.
  exact Hp1.
  + intros Hp2.
  apply P1sym.
  apply HXhX'i.
  apply P2sym.
  exact Hp2.

  - (* phi1 (X' h) (X' i) <-> phi2 (X' h) (X' i) *)
  split; intros H.
  + (* phi1 (X' h) (X' i) -> phi2 (X' h) (X' i) *)
  apply (P2tra _ (X h)).
  split.
  * (* phi2 (X' h) (X h) *)
  apply P2sym.
  apply Hphi2.
  * (* phi2 (X h) (X' i) *)
  apply (P2tra _ (X i)).
  split; auto.
  apply Hco2.
  apply Hco1.
  apply (P1tra _ (X' h)).
  split; auto.
  apply (P1tra _ (X' i)).
  split; auto.
  + (* phi2 (X' h) (X' i) -> phi1 (X' h) (X' i) *)
  apply (P1tra _ (X h)).
  split.
  * (* phi1 (X' h) (X h) *)
  apply P1sym.
  apply Hphi1.
  * (* phi1 (X h) (X' i) *)
  apply (P1tra _ (X i)).
  split; auto.
  apply Hco1.
  apply Hco2.
  apply (P2tra _ (X' h)).
  split; auto.
  apply (P2tra _ (X' i)).
  split; auto.

  - (* phi1 (X' i) Xtop <-> phi2 (X' i) Xtop *)
  split; intro H.
  + (* phi1 (X' i) Xtop -> phi2 (X' i) Xtop *)
  apply (P2tra _ (X i)).
  split; auto.
  apply HXiXtop.
  apply (P1tra _ (X' i)).
  split; auto.
  + (* phi2 (X' i) Xtop -> phi1 (X' i) Xtop *)
  apply (P1tra _ (X i)).
  split; auto.
  apply HXiXtop.
  apply (P2tra _ (X' i)).
  split; auto.

  - (* phi1 Xtop (X i) <-> phi2 Xtop (X i) *)
  split; intro H.
  + (* phi1 Xtop (X i) -> phi2 Xtop (X i) *)
  apply P2sym.
  apply HXiXtop.
  auto.
  + (* phi2 Xtop (X i) -> phi1 Xtop (X i) *)
  apply P1sym.
  apply HXiXtop.
  auto.

  - (* phi1 Xtop (X' i) <-> phi2 Xtop (X' i) *)
  split; intro H.
  + (* phi1 Xtop (X' i) -> phi2 Xtop (X' i) *)
  apply P2sym.
  apply (P2tra _ (X i)).
  split; auto.
  apply HXiXtop.
  apply (P1tra _ (X' i)).
  split; auto.
  + (* phi2 Xtop (X' i) -> phi1 Xtop (X' i) *)
  apply P1sym.
  apply (P1tra _ (X i)).
  split; auto.
  apply HXiXtop.
  apply (P2tra _ (X' i)).
  split; auto.

  - (* phi1 Xtop Xtop <-> phi2 Xtop Xtop *)
  split; intro H; auto.
Qed.

Lemma phi_to_Phi_eq_j_is_equiv_rel :
  forall j phi,
  is_equiv_rel phi ->
  is_equiv_rel (phi_to_Phi_eq_j j phi).
Proof.
  intros j phi.
  intros [Pref [Psym Ptra]].
  unfold is_equiv_rel.
  split; [ | split].
  - (* is_reflexive *)
    unfold is_reflexive.
    intros x.
    case x; unfold phi_to_Phi_eq_j; auto.
  - (* is_symmetric *)
    unfold is_symmetric.
    intros x y.
    case x, y; unfold phi_to_Phi_eq_j; auto.
  - (* is_transitive *)
    unfold is_transitive.
    intros x y z.
    case x, y, z; unfold phi_to_Phi_eq_j;
    try apply Ptra; auto.
Qed.

Lemma phi_is_composable_with_phi_to_Phi_eq_j :
  forall j phi,
  is_equiv_rel phi ->
  composable phi (phi_to_Phi_eq_j j phi).
Proof.
  intros j phi.
  intros Peq.
  unfold composable.
  unfold phi_to_Phi_eq_j.
  intros i h.
  reflexivity.
Qed.

Lemma phi_to_Phi_eq_j_is_Phi_eq_j :
  forall j phi,
  is_equiv_rel phi ->
  Phi_eq_j j (phi_to_Phi_eq_j j phi).
Proof.
  intros j phi.
  intros [Pref [Psym Ptra]].
  unfold Phi_eq_j.
  split.
  - (* phi_to_Phi_eq_j j phi Xtop (X j) *)
  unfold phi_to_Phi_eq_j.
  auto.
  - (* forall i, phi_to_Phi_eq_j j phi (X i) (X' i) *)
  intro i.
  unfold phi_to_Phi_eq_j.
  auto.
Qed.

Theorem at_least_one_Phi_eq_j :
  forall j phi,
  is_equiv_rel phi ->
    exists phi1,
    is_equiv_rel phi1 /\
    composable phi phi1 /\ Phi_eq_j j phi1.
Proof.
  intros j phi.
  intros Peq.
  exists (phi_to_Phi_eq_j j phi).
  split; [| split].
  - apply phi_to_Phi_eq_j_is_equiv_rel.
  exact Peq.
  - apply phi_is_composable_with_phi_to_Phi_eq_j.
  exact Peq.
  - apply phi_to_Phi_eq_j_is_Phi_eq_j.
  exact Peq.
Qed.
