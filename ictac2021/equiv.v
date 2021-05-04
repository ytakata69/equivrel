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

(* Tst *)
Definition Tst := (nat + Top) -> bool.  (* a subset of registers *)

Axiom tst_is_empty_or_not :
  forall tst : Tst, (forall xi, tst xi <> true) \/ exists xi, tst xi = true.
Axiom asgn_is_empty_or_not :
  forall asgn : Asgn, (forall i, asgn i <> true) \/ exists i, asgn i = true.

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
