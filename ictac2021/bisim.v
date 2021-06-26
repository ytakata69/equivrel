(*
 * Lemmas on bisimulation equivalence
 *)

Section Bisimulation.

Parameters Config Config' : Set.
Parameter moveA : Config -> Config -> Prop.
Parameter moveA' : Config' -> Config' -> Prop.

Parameter config_R_config' : Config -> Config' -> Prop.

Inductive star {A : Type} (p : A -> A -> Prop)
  : A -> A -> Prop :=
  | star_ref : forall c, star p c c
  | star_tran : forall c1 c2 c3,
    p c1 c2 -> star p c2 c3 -> star p c1 c3.

Parameter AccA : Config -> Prop.
Parameter AccA' : Config' -> Prop.

Definition LA (c : Config) : Prop :=
  exists cf, AccA cf /\ star moveA c cf.
Definition LA' (c : Config') : Prop :=
  exists cf, AccA' cf /\ star moveA' c cf.

Hypothesis bisimilar_1 :
  forall (c1 c2 : Config) (c'1 : Config'),
    moveA c1 c2 -> config_R_config' c1 c'1 ->
  exists c'2,
    moveA' c'1 c'2 /\ config_R_config' c2 c'2.
Hypothesis bisimilar_2 :
  forall (c1 : Config) (c'1 c'2 : Config'),
    moveA' c'1 c'2 -> config_R_config' c1 c'1 ->
  exists c2,
    moveA c1 c2 /\ config_R_config' c2 c'2.

Hypothesis bisimilar_3 :
  forall c c',
  config_R_config' c c' -> AccA c <-> AccA' c'.

Lemma bisimilar_implies_same_lang :
  forall c c',
  config_R_config' c c' ->
  LA c <-> LA' c'.
Proof.
  intros c c' HR.
  unfold LA.
  unfold LA'.
  split.
  - (* -> *)
  intros [cf [Hcf Hsm]].
  generalize dependent c'.
  induction Hsm as [c | c c2 c3 Hm Hsm IH].
  + intros c' HR.
  apply (bisimilar_3 c c' HR) in Hcf.
  exists c'; split; auto.
  apply star_ref.
  + intros c' HR.
  apply (bisimilar_1 c c2 c' Hm) in HR.
  destruct HR as [c'2 [HmA' HR']].
  assert (IH' := IH Hcf c'2 HR').
  destruct IH' as [cf' [Hcf' Hsm']].
  exists cf'; split; auto.
  now apply star_tran with c'2.
  - (* <- *)
  intros [cf' [Hcf' Hsm']].
  generalize dependent c.
  induction Hsm' as [c' | c' c'2 c'3 Hm' Hsm' IH].
  + intros c HR.
  apply (bisimilar_3 c c' HR) in Hcf'.
  exists c; split; auto.
  apply star_ref.
  + intros c HR.
  apply (bisimilar_2 c c' c'2 Hm') in HR.
  destruct HR as [c2 [HmA HR']].
  assert (IH' := IH Hcf' c2 HR').
  destruct IH' as [cf [Hcf Hsm]].
  exists cf; split; auto.
  now apply star_tran with c2.
Qed.

End Bisimulation.
