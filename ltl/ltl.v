Require Import Nat Arith.

(* data words *)

Definition Sigma := nat.
Parameter D : Set.  (* a data domain *)
Definition data_word := nat -> (Sigma * D)%type.

(* LTL syntax *)

Definition register := nat.

Inductive ltl_atom :=
  | tt : ltl_atom
  | MATCH : register -> ltl_atom
  | p : Sigma -> ltl_atom  (* an atomic proposition *)
  .

Inductive ltl :=
  | pos : ltl_atom -> ltl  (* a positive literal *)
  | neg : ltl_atom -> ltl  (* a negative literal *)
  | X : ltl -> ltl
  | F : ltl -> ltl
  | G : ltl -> ltl
  | STORE : register -> ltl -> ltl
  | OR  : ltl -> ltl -> ltl
  | AND : ltl -> ltl -> ltl
  | NOT : ltl -> ltl
  | until : ltl -> ltl -> ltl
  | weak_until : ltl -> ltl -> ltl
  .

Notation "'↓' r , phi" := (STORE r phi) (at level 200).
Notation "'↑' r" := (MATCH r) (at level 75).
Notation "a '.\/' b" := (OR  a b) (at level 85, right associativity).
Notation "a './\' b" := (AND a b) (at level 75, right associativity).
Notation  "'[' a ']'" := (pos a).
Notation "'~[' a ']'" := (neg a).
Notation "'.~' a" := (NOT a) (at level 71).
Notation "a 'U' b" := (until a b) (at level 73, right associativity).
Notation "a 'W' b" := (weak_until a b) (at level 73, right associativity).

(* example formulas *)
(*
Check (STORE 1 (X (OR (neg (p 1)) (OR (pos (p 2)) (pos (↑ 1)))))).
Check ( ↓1, X (~[p 1] .\/   [p 2] .\/ [↑1])).
Check ((↓1, X (~[p 1] .\/ F [p 2]) .\/ F [↑1]) .\/ F (X [p 1])).
*)

(* semantics *)

Definition valuation := register -> D.

Definition update
  (v : valuation) (i : register) (d : D) : valuation :=
  fun (r : register) => if r =? i then d else v r.

Definition models_atom
  (sigma : data_word) (i : nat) (v : valuation) (atom : ltl_atom)
  : Prop :=
  match atom with
  | tt  => True
  | p a => fst (sigma i) = a
  | ↑ r => snd (sigma i) = v r
  end.

Fixpoint models
  (sigma : data_word) (i : nat) (v : valuation) (phi : ltl)
  : Prop :=
  match phi with
  | pos atom =>   models_atom sigma i v atom
  | neg atom => ~ models_atom sigma i v atom
  | X phi' => models sigma (S i) v phi'
  | F phi' => exists j : nat, i <= j /\ models sigma j v phi'
  | G phi' => forall j : nat, i <= j -> models sigma j v phi'
  | (↓ r, phi') => models sigma i (update v r (snd (sigma i))) phi'
  | phi1 .\/ phi2 => models sigma i v phi1 \/ models sigma i v phi2
  | phi1 ./\ phi2 => models sigma i v phi1 /\ models sigma i v phi2
  | .~ phi' => ~ models sigma i v phi'
  | phi1 U phi2 => exists j : nat, i <= j /\ models sigma j v phi2 /\
                   forall j': nat, i <= j' < j -> models sigma j' v phi1
  | phi1 W phi2 => (exists j : nat, i <= j /\ models sigma j v phi2 /\
                    forall j': nat, i <= j' < j -> models sigma j' v phi1) \/
                   (forall j': nat, i <= j' -> models sigma j' v phi1)
  end.

Notation "'(' sigma ',' i '|=' v ',' phi ')'"
  := (models sigma i v phi).

(* definition of equality of two ltl formulas *)
Axiom ltl_extensionality :
  forall phi1 phi2 : ltl,
    (forall sigma i v, (sigma, i |= v, phi1) <-> (sigma, i |= v, phi2))
    -> phi1 = phi2.

Axiom valuation_extensionality :
  forall v1 v2 : valuation,
    (forall r, v1 r = v2 r) -> v1 = v2.

(* an auxiliary predicate *)

Fixpoint contains_match
  (r : register) (phi : ltl) : Prop
  :=
  match phi with
  | pos (↑ r') => r' = r
  | neg (↑ r') => r' = r
  | pos _  | neg _ => False
  | X phi'         => contains_match r phi'
  | F phi'         => contains_match r phi'
  | G phi'         => contains_match r phi'
  | (↓ r', phi')   => contains_match r phi'
  | phi1 .\/ phi2  => contains_match r phi1 \/ contains_match r phi2
  | phi1 ./\ phi2  => contains_match r phi1 \/ contains_match r phi2
  | phi1  U  phi2  => contains_match r phi1 \/ contains_match r phi2
  | phi1  W  phi2  => contains_match r phi1 \/ contains_match r phi2
  | .~ phi'        => contains_match r phi'
  end.

Fixpoint contains_store
  (r : register) (phi : ltl) : Prop
  :=
  match phi with
  | pos _  | neg _ => False
  | X phi'         => contains_store r phi'
  | F phi'         => contains_store r phi'
  | G phi'         => contains_store r phi'
  | (↓ r', phi')   => r' = r \/ contains_store r phi'
  | phi1 .\/ phi2  => contains_store r phi1 /\ contains_store r phi2
  | phi1 ./\ phi2  => contains_store r phi1 /\ contains_store r phi2
  | phi1  U  phi2  => contains_store r phi1 /\ contains_store r phi2
  | phi1  W  phi2  => contains_store r phi1 /\ contains_store r phi2
  | .~ phi'        => contains_store r phi'
  end.

(* cancellation *)

Lemma store_match_equals_tt :
  forall r : nat, (↓ r, [↑ r]) = [tt].
Proof.
  intros r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models; unfold models_atom.
  unfold update.
  rewrite <- beq_nat_refl.
  split; intros H; trivial.
Qed.

Lemma store_neg_match_equals_ff :
  forall r : nat, (↓ r, ~[↑ r]) = ~[tt].
Proof.
  intros r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models; unfold models_atom.
  unfold update.
  rewrite <- beq_nat_refl.
  split; intros H; contradiction.
Qed.

(* distribution over OR *)

Lemma distr_X_over_OR :
  forall phi1 phi2,
    (X (phi1 .\/ phi2)) = (X phi1 .\/ X phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  destruct H as [H | H];
  (left; assumption) ||
  (right; assumption).
Qed.

Lemma distr_F_over_OR :
  forall phi1 phi2,
    (F (phi1 .\/ phi2)) = (F phi1 .\/ F phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [H | H]]].
+ left.
  exists j.
  split; assumption.
+ right.
  exists j.
  split; assumption.
- destruct H as [H | H];
  destruct H as [j [ij H]];
  unfold models;
  exists j;
  split; auto.
Qed.

Lemma distr_U_over_OR :
  forall psi phi1 phi2,
    (psi U (phi1 .\/ phi2)) = (psi U phi1 .\/ psi U phi2).
Proof.
  intros psi phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [[H1 | H1] H2]]].
+ left.
  exists j.
  split; try assumption.
  split; try assumption.
+ right.
  exists j.
  split; try assumption.
  split; try assumption.
- destruct H as [H | H];
  destruct H as [j [ij [H1 H2]]];
  exists j;
  split; try assumption;
  split; try assumption;
  (left; assumption) ||
  (right; assumption).
Qed.

Lemma distr_W_over_OR :
  forall psi phi1 phi2,
    (psi W (phi1 .\/ phi2)) = (psi W phi1 .\/ psi W phi2).
Proof.
  intros psi phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [[j [ij [[H1 | H1] H2]]] | H1].
+ left.
  left.
  exists j.
  split; try assumption.
  split; try assumption.
+ right.
  left.
  exists j.
  split; try assumption.
  split; try assumption.
+ left.
  right; assumption.
- destruct H as [H | H];
  destruct H as [[j [ij [H1 H2]]] | H1];
  (left;
   exists j;
   split; try assumption;
   split; try assumption;
   (left; assumption) ||
   (right; assumption)) ||
  (right;
   exists j;
   split; try assumption;
   split; try assumption;
   (left; assumption) ||
   (right; assumption)) ||
  (right; assumption).
Qed.

Lemma distr_STORE_over_OR :
  forall phi1 phi2 r,
    (↓ r, (phi1 .\/ phi2)) = ((↓ r, phi1) .\/ (↓ r, phi2)).
Proof.
  intros phi1 phi2 r.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  destruct H as [H | H];
  unfold models; auto.
Qed.

(* distribution over AND *)

Lemma distr_X_over_AND :
  forall phi1 phi2,
    (X (phi1 ./\ phi2)) = (X phi1 ./\ X phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  destruct H as [H1 H2];
  split; assumption.
Qed.

Lemma distr_G_over_AND :
  forall phi1 phi2,
    (G (phi1 ./\ phi2)) = (G phi1 ./\ G phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- split;
  intros j ij;
  apply (H j ij).
- destruct H as [H1 H2].
  intros j ij.
  split.
+ apply (H1 j ij).
+ apply (H2 j ij).
Qed.

Lemma distr_U_over_AND :
  forall phi1 phi2 psi,
    ((phi1 ./\ phi2) U psi) = (phi1 U psi ./\ phi2 U psi).
Proof.
  intros phi1 phi2 psi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [H1 H2]]].
  split;
  (exists j;
   split; try assumption;
   split; try assumption;
   intros j' ij'j;
   destruct (H2 j' ij'j) as [H3 H4];
   assumption).
- destruct H as [H1' H2'];
  destruct H1' as [j1 [ij1 [H11 H12]]];
  destruct H2' as [j2 [ij2 [H21 H22]]].
  destruct (Nat.le_ge_cases j1 j2) as [j1j2 | j2j1].
+ exists j1.
  split; try assumption;
  split; try assumption.
  intros j' ij'j1.
  split.
* apply H12; assumption.
* apply H22.
  destruct ij'j1 as [ij' j'j1].
  split; try assumption.
  apply (Nat.lt_le_trans _ j1 _); assumption.
+ exists j2.
  split; try assumption;
  split; try assumption.
  intros j' ij'j2.
  split.
* apply H12.
  destruct ij'j2 as [ij' j'j2].
  split; try assumption.
  apply (Nat.lt_le_trans _ j2 _); assumption.
* apply H22; assumption.
Qed.

Lemma distr_W_over_AND :
  forall phi1 phi2 psi,
    ((phi1 ./\ phi2) W psi) = (phi1 W psi ./\ phi2 W psi).
Proof.
  intros phi1 phi2 psi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [[j [ij [H1 H2]]] | H1].
+ split;
  (left;
   exists j;
   split; try assumption;
   split; try assumption;
   intros j' ij'j;
   destruct (H2 j' ij'j) as [H3 H4];
   assumption).
+ split;
  right;
  apply H1.
- destruct H as [H1' H2'];
  destruct H1' as [[j1 [ij1 [H11 H12]]] | H1];
  destruct H2' as [[j2 [ij2 [H21 H22]]] | H2].
  destruct (Nat.le_ge_cases j1 j2) as [j1j2 | j2j1].
+ left.
  exists j1.
  split; try assumption;
  split; try assumption.
  intros j' ij'j1.
  split.
* apply H12; assumption.
* apply H22.
  destruct ij'j1 as [ij' j'j1].
  split; try assumption.
  apply (Nat.lt_le_trans _ j1 _); assumption.
+ left.
  exists j2.
  split; try assumption;
  split; try assumption.
  intros j' ij'j2.
  split.
* apply H12.
  destruct ij'j2 as [ij' j'j2].
  split; try assumption.
  apply (Nat.lt_le_trans _ j2 _); assumption.
* apply H22; assumption.
+ left.
  exists j1.
  split; try assumption;
  split; try assumption.
  intros j' ij'j1.
  split.
* apply H12; apply ij'j1.
* apply H2;  apply ij'j1.
+ left.
  exists j2.
  split; try assumption;
  split; try assumption.
  intros j' ij'j2.
  split.
* apply H1;  apply ij'j2.
* apply H22; apply ij'j2.
+ right.
  intros j ij.
  split.
* apply H1; assumption.
* apply H2; assumption.
Qed.

Lemma distr_STORE_over_AND :
  forall phi1 phi2 r,
    (↓ r, (phi1 ./\ phi2)) = ((↓ r, phi1) ./\ (↓ r, phi2)).
Proof.
  intros phi1 phi2 r.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  destruct H as [H1 H2];
  split; assumption.
Qed.

(* distribution over U, W *)

Lemma distr_X_over_U :
  forall phi1 phi2,
    (X (phi1 U phi2)) = (X phi1 U X phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [sij [H2 H1]]].
  exists (pred j).
  repeat split.
+ apply Nat.le_succ_le_pred; assumption.
+ unfold models.
  rewrite <- (S_pred j i).
    assumption.
  auto. (* i < j *)
+ intros j' [ij' j'predj].
  apply (H1 (S j')).
  split.
    apply le_n_S; assumption.
  apply Nat.lt_succ_lt_pred; assumption.
- destruct H as [j [ij [H2 H1]]].
  exists (S j).
  repeat split.
+ apply le_n_S; assumption.
+ apply H2.
+ intros j' [sij' j'sj].
  assert (Spredj': j' = S (pred j')).
  { apply (S_pred j' i). auto. }
  assert (ij': i <= pred j' < j).
  {
    split.
  - apply Nat.le_succ_le_pred; assumption.
  - apply lt_S_n.
    rewrite <- Spredj'.
    assumption.
  }
  assert (H1' := (H1 (pred j') ij')).
  unfold models in H1'.
  rewrite <- Spredj' in H1'.
  assumption.
Qed.

Lemma distr_X_over_W :
  forall phi1 phi2,
    (X (phi1 W phi2)) = (X phi1 W X phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [[j [sij [H2 H1]]] | H1].
+ left.
  exists (pred j).
  repeat split.
* apply Nat.le_succ_le_pred; assumption.
* unfold models.
  rewrite <- (S_pred j i).
    assumption.
  auto. (* i < j *)
* intros j' [ij' j'predj].
  apply (H1 (S j')).
  split.
    apply le_n_S; assumption.
  apply Nat.lt_succ_lt_pred; assumption.
+ right.
  intros j ij.
  apply H1.
  apply le_n_S; assumption.
- destruct H as [[j [ij [H2 H1]]] | H1].
+ left.
  exists (S j).
  repeat split.
* apply le_n_S; assumption.
* apply H2.
* intros j' [sij' j'sj].
  assert (Spredj': j' = S (pred j')).
  { apply (S_pred j' i). auto. }
  assert (ij': i <= pred j' < j).
  {
    split.
  - apply Nat.le_succ_le_pred; assumption.
  - apply lt_S_n.
    rewrite <- Spredj'.
    assumption.
  }
  assert (H1' := (H1 (pred j') ij')).
  unfold models in H1'.
  rewrite <- Spredj' in H1'.
  assumption.
+ right.
  intros j sij.
  assert (Spredj: j = S (pred j)).
  { apply (S_pred j i). auto. }
  assert (ipredj: i <= pred j).
  { apply Nat.le_succ_le_pred; assumption. }
  assert (H1' := (H1 (pred j) ipredj)).
  unfold models in H1'.
  rewrite <- Spredj in H1'.
  assumption.
Qed.

(* equivalent transformations *)

Lemma FX_equals_XF :
  forall phi, (F (X phi)) = (X (F phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij H]].
  exists (S j).
  split.
    apply le_n_S; assumption.
  assumption.
- destruct H as [j [sij H]].
  exists (pred j).
  split.
    apply Nat.le_succ_le_pred; assumption.
  unfold models.
  rewrite <- (S_pred j i).
    assumption.
  auto. (* i < j *)
Qed.

Lemma GX_equals_XG :
  forall phi, (G (X phi)) = (X (G phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- intros j ij.
  assert (ij': i <= pred j).
  {
    apply le_pred in ij.
    rewrite <- pred_Sn in ij.
    apply ij.
  }
  assert (predj: S (pred j) = j).
  {
    destruct j.
  - apply le_not_gt in ij.
    assert (Hn: S i > 0).
    { apply gt_Sn_O. }
    contradiction.
  - apply pred_Sn.
  }
  unfold models in H.
  assert (H' := (H (pred j) ij')); clear H.
  rewrite predj in H'.
  apply H'.
- intros j ij.
  unfold models in H.
  assert (ij': S i <= S j).
  { apply le_n_S. assumption. }
  assert (H' := (H (S j) ij')); clear H.
  apply H'.
Qed.

Lemma F_equals_phi_or_XF :
  forall phi,
    (F phi) = (phi .\/ X (F phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij H]].
  assert (Hj: i = j \/ S i <= j).
  {
    destruct ij.
  - left; reflexivity.
  - right; apply le_n_S; assumption.
  }
  destruct Hj as [Hj | Hj].
+ left.
  rewrite Hj.
  assumption.
+ right.
  exists j.
  split; assumption.
- destruct H as [H | [j [ij H]]].
+ exists i.
  split.
    trivial.
  assumption.
+ exists j.
  split.
* apply le_S_n.
  apply Nat.le_le_succ_r.
  assumption.
* assumption.
Qed.

Lemma G_equals_phi_and_XG :
  forall phi,
    (G phi) = (phi ./\ X (G phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- split.
+ apply (H i). trivial.
+ intros j sij.
  assert (ij: i <= j).
  { apply le_S_n. apply le_S. assumption. }
  apply (H j ij).
- destruct H as [H1 H2].
  intros j ij.
  apply Nat.lt_eq_cases in ij.
  destruct ij as [ij | ij].
+ apply lt_le_S in ij.
  apply (H2 j ij).
+ rewrite <- ij.
  assumption.
Qed.

Lemma U_equals_phi2_or_phi1_and_XU :
  forall phi1 phi2,
    (phi1 U phi2) = (phi2 .\/ phi1 ./\ X (phi1 U phi2)).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [H2 H1]]].
  assert (Hj: i = j \/ S i <= j).
  {
    destruct ij.
  - left; reflexivity.
  - right; apply le_n_S; assumption.
  }
  destruct Hj as [Hj | Hj].
+ left.
  rewrite Hj.
  assumption.
+ right.
  split.
* apply H1.
  split; trivial.
* exists j.
  split; try assumption.
  split; try assumption.
  intros j' sij'j.
  apply H1.
  destruct sij'j as [sij' j'j].
  apply le_Sn_le in sij'.
  split; assumption.
- destruct H as [H | [H1 [j [ij [H2 H1']]]]].
+ exists i.
  split; try trivial.
  split; try assumption.
  intros j' [ij' j'i].
  apply (Nat.le_lt_trans _ _ _ ij') in j'i.
  apply Nat.lt_irrefl in j'i.
  contradiction.
+ exists j.
  split.
* apply le_S_n.
  apply Nat.le_le_succ_r.
  assumption.
* split.
    assumption.
  intros j' [ij' j'j].
  destruct ij'.
    assumption.
  apply (H1' (S m)).
  split; try assumption.
    apply le_n_S; assumption.
Qed.

Lemma W_equals_phi2_or_phi1_and_XW :
  forall phi1 phi2,
    (phi1 W phi2) = (phi2 .\/ phi1 ./\ X (phi1 W phi2)).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [[j [ij [H2 H1]]] | H1].
+ assert (Hj: i = j \/ S i <= j).
  {
    destruct ij.
  - left; reflexivity.
  - right; apply le_n_S; assumption.
  }
  destruct Hj as [Hj | Hj].
* left.
  rewrite Hj.
  assumption.
* right.
  split.
-- apply H1.
  split; trivial.
-- left.
  exists j.
  split; try assumption.
  split; try assumption.
  intros j' sij'j.
  apply H1.
  destruct sij'j as [sij' j'j].
  apply le_Sn_le in sij'.
  split; assumption.
+ right.
  split.
* apply H1. trivial.
* right.
  intros j sij.
  apply H1.
  apply le_Sn_le; assumption.

- destruct H as [H | [H1 [[j [ij [H2 H1']]] | H1']]].
+ left.
  exists i.
  split; try trivial.
  split; try assumption.
  intros j' [ij' j'i].
  apply (Nat.le_lt_trans _ _ _ ij') in j'i.
  apply Nat.lt_irrefl in j'i.
  contradiction.
+ left.
  exists j.
  split.
* apply le_S_n.
  apply Nat.le_le_succ_r.
  assumption.
* split.
    assumption.
  intros j' [ij' j'j].
  destruct ij'.
    assumption.
  apply (H1' (S m)).
  split; try assumption.
    apply le_n_S; assumption.
+ right.
  intros j ij.
  assert (Hj: i = j \/ S i <= j).
  {
    destruct ij.
  - left; reflexivity.
  - right; apply le_n_S; assumption.
  }
  destruct Hj as [Hj | Hj]; clear ij.
* rewrite <- Hj.
  assumption.
* apply H1'; assumption.
Qed.

(* relationship among F, G, U, W *)

Lemma not_F_equals_G_not :
  forall phi, (.~ F phi) = (G (.~ phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- intros j ij Hn.
  apply H.
  exists j.
  split; assumption.
- intros Hn.
  destruct Hn as [j [ij Hn]].
  apply (H j ij).
  assumption.
Qed.

Lemma F_equals_tt_U :
  forall phi, (F phi) = ([tt] U phi).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij H]].
  exists j.
  repeat split; assumption.
- destruct H as [j [ij [H _]]].
  exists j.
  split; assumption.
Qed.

Lemma G_equals_W_ff :
  forall phi, (G phi) = (phi W ~[tt]).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- right.
  apply H.
- destruct H as [[j [ij [H _]]] | H].
+ unfold models in H;
  unfold models_atom in H.
  contradiction.
+ intros j ij.
  apply (H j ij).
Qed.

Lemma U_is_W_and_F :
  forall phi1 phi2,
    (phi1 U phi2) = (phi1 W phi2 ./\ F phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- split;
  destruct H as [j [ij [H2 H1]]].
+ left.
  exists j.
  repeat split; try assumption.
+ exists j.
  split; assumption.
- destruct H as [H1' H2'];
  destruct H1' as [[j [ij [H11 H12]]] | H1].
+ exists j.
  repeat split; try assumption.
+ destruct H2' as [j [ij H2]].
  exists j.
  repeat split; try assumption.
  intros j' ij'j.
  apply H1.
  apply ij'j.
Qed.

Lemma W_is_U_or_G :
  forall phi1 phi2,
    (phi1 W phi2) = (phi1 U phi2 .\/ G phi1).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [[j [ij [H2 H1]]] | H1].
+ left.
  exists j.
  repeat split; try assumption.
+ right.
  intros j ij.
  apply H1; assumption.
- destruct H as [H | H].
+ destruct H as [j [ij [H1 H2]]].
  left.
  exists j.
  repeat split; try assumption.
+ right.
  apply H.
Qed.

(* idempotency *)

Lemma F_is_idempotent :
  forall phi, (F (F phi)) = (F phi).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [j0 [jj0 H]]]].
  exists j0.
  split.
+ apply (Nat.le_trans _ j _); assumption.
+ assumption.
- destruct H as [j [ij H]].
  exists i.
  split.
    trivial. (* i <= i *)
  exists j.
  split; assumption.
Qed.

Lemma G_is_idempotent :
  forall phi, (G (G phi)) = (G phi).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- intros j ij.
  assert (jj: j <= j).
  { trivial. }
  apply (H j ij j jj).
- intros j0 ij0 j j0j.
  assert (ij: i <= j).
  { apply (Nat.le_trans _ j0 _ ij0 j0j). }
  clear j0 ij0 j0j.
  apply (H j ij).
Qed.

Lemma update_is_idempotent :
  forall v r d,
    update (update v r d) r d = update v r d.
Proof.
  intros v r d.
  apply valuation_extensionality.
  intros r0.
  unfold update.
  case (r0 =? r); trivial.
Qed.

Lemma STORE_is_idempotent :
  forall phi r, (↓ r, (↓ r, phi)) = (↓ r, phi).
Proof.
  intros phi r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models.
  rewrite update_is_idempotent.
  reflexivity.
Qed.

(* commutativity *)

Lemma update_is_commutative :
  forall v r1 r2 d,
    update (update v r1 d) r2 d = update (update v r2 d) r1 d.
Proof.
  intros v r1 r2 d.
  apply valuation_extensionality.
  intros r0.
  unfold update.
  case (r0 =? r2); case (r0 =? r1); trivial.
Qed.

Lemma STORE_is_commutative :
  forall phi r1 r2,
    (↓ r1, (↓ r2, phi)) = (↓ r2, (↓ r1, phi)).
Proof.
  intros phi r1 r2.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models.
  rewrite (update_is_commutative _ r1 r2).
  reflexivity.
Qed.

(* redundant STORE *)

Lemma redundant_STORE_core :
  forall r phi,
  ~ contains_match r phi ->
    forall sigma i v d,
      (sigma, i |= v, phi)
      <-> (sigma, i |= update v r d, phi).
Proof.
  intros r phi;
  intros Hcon.
  induction phi.
- intros sigma i v d.
  destruct l; try reflexivity.
+ unfold models; unfold models_atom.
  unfold update.
  apply Nat.eqb_neq in Hcon.
  rewrite Hcon.
  reflexivity.
- intros sigma i v d.
  destruct l; try reflexivity.
+ unfold models; unfold models_atom.
  unfold update.
  apply Nat.eqb_neq in Hcon.
  rewrite Hcon.
  reflexivity.

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  split; intros H;
  apply (IHphi Hcon' _ _ v d); apply H.

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  split; intros H;
  destruct H as [j [ij H]];
  exists j;
  split;
   assumption ||
  (apply (IHphi Hcon' _ _ v d); assumption).

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  split; intros H;
  intros j ij;
  apply (IHphi Hcon' _ _ v d);
  apply (H _ ij).

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  case_eq (r0 =? r); intros r0r.
+ assert (Hup: forall d', update (update v r d') r d' = update (update v r d) r d').
  {
    intros d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case (r1 =? r); reflexivity.
  }
  apply beq_nat_true in r0r.
  rewrite r0r.
  assert (IH := (IHphi Hcon' sigma i (update v r (snd (sigma i))) (snd (sigma i))));
  clear IHphi Hcon.
  rewrite (Hup (snd (sigma i))) in IH.
  split; intros H;
  apply IH; apply H.
+ assert (Hup: r0 <> r -> forall d', update (update v r0 d') r d = update (update v r d) r0 d').
  {
    intros H d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case_eq (r1 =? r); case_eq (r1 =? r0); intros r1r0 r1r;
    try reflexivity.
  - apply beq_nat_true in r1r0.
    apply beq_nat_true in r1r.
    rewrite r1r0 in r1r.
    elim H; assumption.
  }
  apply beq_nat_false in r0r.
  assert (IH := (IHphi Hcon' sigma i (update v r0 (snd (sigma i))) d));
  clear IHphi Hcon.
  rewrite (Hup r0r (snd (sigma i))) in IH.
  split; intros H;
  apply IH; apply H.

- assert (Hcon': ~ (contains_match r phi1 \/ contains_match r phi2)).
  { intros H; apply Hcon; apply H. }
  apply Decidable.not_or_iff in Hcon'.
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [H | H];
  (left;  apply (IHphi1 Hcon1 _ _ v d); apply H) ||
  (right; apply (IHphi2 Hcon2 _ _ v d); apply H).

- assert (Hcon': ~ (contains_match r phi1 \/ contains_match r phi2)).
  { intros H; apply Hcon; apply H. }
  apply Decidable.not_or_iff in Hcon'.
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [H1 H2];
  split;
  (apply (IHphi1 Hcon1 _ _ v d); apply H1) ||
  (apply (IHphi2 Hcon2 _ _ v d); apply H2).

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  split; intros H;
  intros Hn;
  apply H;
  apply (IHphi Hcon' _ _ v d);
  assumption.

- assert (Hcon': ~ (contains_match r phi1 \/ contains_match r phi2)).
  { intros H; apply Hcon; apply H. }
  apply Decidable.not_or_iff in Hcon'.
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  (destruct H as [j [ij [H2 H1]]];
   exists j;
   split; try assumption;
   split;
   (apply (IHphi2 Hcon2 _ _ v d); apply H2) ||
   (intros j' ij'j;
    apply (IHphi1 Hcon1 _ _ v d);
    apply (H1 j' ij'j))).

- assert (Hcon': ~ (contains_match r phi1 \/ contains_match r phi2)).
  { intros H; apply Hcon; apply H. }
  apply Decidable.not_or_iff in Hcon'.
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [[j [ij [H2 H1]]] | H1];
  (left;
   exists j;
   split; try assumption;
   split;
   (apply (IHphi2 Hcon2 _ _ v d); apply H2) ||
   (intros j' ij'j;
    apply (IHphi1 Hcon1 _ _ v d);
    apply (H1 j' ij'j))) ||
  (right;
   (intros j' ij';
    apply (IHphi1 Hcon1 _ _ v d);
    apply (H1 j' ij'))).
Qed.

Lemma redundant_STORE'_core :
  forall r phi,
    contains_store r phi ->
    forall sigma i v d,
      (sigma, i |= v, phi)
      <-> (sigma, i |= update v r d, phi).
Proof.
  intros r phi;
  intros Hcon.
  induction phi.
- unfold contains_store in Hcon.
  contradiction.
- unfold contains_store in Hcon.
  contradiction.

- assert (Hcon': contains_store r phi).
  { apply Hcon. }
  intros sigma i v d.
  split; intros H;
  apply (IHphi Hcon' _ _ v d); apply H.

- assert (Hcon': contains_store r phi).
  { apply Hcon. }
  intros sigma i v d.
  split; intros H;
  destruct H as [j [ij H]];
  exists j;
  split;
   assumption ||
  (apply (IHphi Hcon' _ _ v d); assumption).

- assert (Hcon': contains_store r phi).
  { apply Hcon. }
  intros sigma i v d.
  split; intros H;
  (intros j ij;
   apply (IHphi Hcon' _ _ v d);
   apply (H j ij)).

- assert (Hcon': r0 = r \/ contains_store r phi).
  { apply Hcon. }
  assert (Hcon'': r0 = r \/ r0 <> r /\ contains_store r phi).
  {
    case_eq (r0 =? r); intros r0r.
  - left.
    apply beq_nat_true; assumption.
  - right.
    split.
  + apply beq_nat_false; assumption.
  + destruct Hcon' as [r0r' | Hcon'].
  * rewrite Nat.eqb_neq in r0r.
    contradiction.
  * assumption.
  }
  clear Hcon'.
  intros sigma i v d.
  destruct Hcon'' as [r0r | [r0r Hcon']].
+ assert (Hup: forall d', update (update v r d) r d' = update v r d').
  {
    intros d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case (r1 =? r); reflexivity.
  }
  rewrite r0r.
  split; intros H.
* unfold models.
  rewrite (Hup (snd (sigma i))).
  apply H.
* unfold models.
  rewrite <- (Hup (snd (sigma i))).
  apply H.
+ assert (Hup: forall d', update (update v r d) r0 d' = update (update v r0 d') r d).
  {
    intros d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case_eq (r1 =? r); case_eq (r1 =? r0); intros r1r0 r1r;
    try reflexivity.
  - apply beq_nat_true in r1r0;
    apply beq_nat_true in r1r.
    symmetry in r1r0;
    rewrite r1r0 in r0r.
    contradiction.
  }
  assert (IH := (IHphi Hcon' sigma i (update v r0 (snd (sigma i))) d));
  clear IHphi Hcon.
  split; intros H.
* unfold models.
  rewrite (Hup (snd (sigma i))).
  apply IH.
  apply H.
* unfold models.
  apply IH.
  rewrite <- (Hup (snd (sigma i))).
  apply H.

- assert (Hcon': contains_store r phi1 /\ contains_store r phi2).
  { apply Hcon. }
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [H | H];
  (left;  apply (IHphi1 Hcon1 _ _ v d); apply H) ||
  (right; apply (IHphi2 Hcon2 _ _ v d); apply H).

- assert (Hcon': contains_store r phi1 /\ contains_store r phi2).
  { apply Hcon. }
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [H1 H2];
  split;
  (apply (IHphi1 Hcon1 _ _ v d); apply H1) ||
  (apply (IHphi2 Hcon2 _ _ v d); apply H2).

- assert (Hcon': contains_store r phi).
  { apply Hcon. }
  intros sigma i v d.
  split; intros H;
  (intros Hn;
   apply H;
   apply (IHphi Hcon' _ _ v d);
   assumption).

- assert (Hcon': contains_store r phi1 /\ contains_store r phi2).
  { apply Hcon. }
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  (destruct H as [j [ij [H2 H1]]];
   exists j;
   split; try assumption;
   split;
   (apply (IHphi2 Hcon2 _ _ v d); apply H2) ||
   (intros j' ij'j;
   apply (IHphi1 Hcon1 _ _ v d);
   apply (H1 j' ij'j))).

- assert (Hcon': contains_store r phi1 /\ contains_store r phi2).
  { apply Hcon. }
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  split; intros H;
  destruct H as [[j [ij [H2 H1]]] | H1];
  (left;
   exists j;
   split; try assumption;
   split;
   (apply (IHphi2 Hcon2 _ _ v d); apply H2) ||
   (intros j' ij'j;
   apply (IHphi1 Hcon1 _ _ v d);
   apply (H1 j' ij'j))) ||
  (right;
   (intros j' ij'j;
   apply (IHphi1 Hcon1 _ _ v d);
   apply (H1 j' ij'j))).
Qed.


Lemma redundant_STORE :
  forall phi r,
    ~ contains_match r phi -> (↓ r, phi) = phi.
Proof.
  intros phi r Hcon.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  (apply (redundant_STORE_core _ _ Hcon _ _ v _) in H ||
   apply (redundant_STORE_core _ _ Hcon _ _ v _));
  assumption.
Qed.

Lemma redundant_STORE' :
  forall phi r,
    contains_store r phi -> (↓ r, phi) = phi.
Proof.
  intros phi r Hcon.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H;
  (apply (redundant_STORE'_core _ _ Hcon _ _ v _) in H ||
   apply (redundant_STORE'_core _ _ Hcon _ _ v _));
  assumption.
Qed.
