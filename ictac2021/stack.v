(*
 * Usage: You may need "make equiv.vo" before
 * using this file.
 * In vscode, you may also need to add
 * "coqtop.args": [ "-Q", "/path/to/this/dir", "" ]
 * to settings.json.
 *)

Require Export equiv.
Require Export Lists.List.

Local Open Scope type_scope.  (* for '*' *)

(* finite control states *)

Parameter Q : Set.
Definition Q' := Q * Phi.

Inductive Com :=
  | pop
  | skip
  | push (j : nat).
Inductive Com' :=
  | pop'
  | skip'
  | push' (phi : Phi).

(* Stack and configurations *)

Definition Stack  := list (D * Theta).
Definition Stack' := list Phi.

Definition Config  := Q  * Theta * Stack.
Definition Config' := Q' * Stack'.

Definition update_stack (u : Stack) theta com :=
  match com with
  | pop => match u with
             _ :: u' => u' | nil => nil
           end
  | skip => u
  | push j => (theta j, theta) :: u
  end.

Definition update_stack' (u : Stack') com' :=
  match com' with
  | pop' => match u with
              _ :: u' => u' | nil => nil
            end
  | skip' => u
  | push' z => z :: u
  end.

Definition not_contain d (cell: D * Theta) :=
  match cell with
    (_, theta) => forall i, theta i <> d
  end.

Axiom stack_has_outside_data :
  forall (theta: Theta) (e: D) (u: Stack),
  exists d : D,
    d <> e /\ (forall i, theta i <> d) /\
    Forall (not_contain d) u.

Definition is_proper_stack (stack : Stack) :=
  let is_proper_cell cell :=
    match cell with (z, theta) => exists i, z = theta i end
  in Forall is_proper_cell stack.

(* Bisimulation relation between configs *)

(* The stack bottom of a given starting ID *)
Parameter theta_0 : Theta.
Parameter d_0 : D.
Axiom proper_bottom : exists i, d_0 = theta_0 i.

Inductive stack_R_stack'
  : Theta -> Stack -> Phi -> Stack' -> Prop :=
  | Stack_R_stack'_nil :
    forall theta phi,
      (theta_0, d_0, theta) |= phi ->
      stack_R_stack' theta nil phi nil
  | Stack_R_stack'_cons :
    forall theta ptheta d phi pphi u v,
      (ptheta, d, theta) |= phi ->
      stack_R_stack' ptheta u pphi v ->
      stack_R_stack' theta ((d, ptheta) :: u) phi (pphi :: v).

Inductive config_R_config'
  : Config -> Config' -> Prop :=
  | Config_R_config' :
    forall q theta u phi v,
      stack_R_stack' theta u phi v ->
      config_R_config' (q, theta, u) ((q, phi), v).

(* freshness_p on stack *)

Inductive Forall2 {X : Type} (P : X -> X -> Prop)
  : list X -> Prop :=
  | Forall2_nil : Forall2 P nil
  | Forall2_cons x l :
    Forall (P x) l -> Forall2 P l -> Forall2 P (x :: l).

Inductive Forall3 {X : Type} (P : X -> X -> X -> Prop)
  : list X -> Prop :=
  | Forall3_nil : Forall3 P nil
  | Forall3_cons x l :
    Forall2 (P x) l -> Forall3 P l -> Forall3 P (x :: l).

Definition freshness_p_on_triple
  (p3 p2 p1 : D * Theta) :=
  match (p3, p2, p1) with
    ((_, th3), (_, th2), (d, th1))
    => freshness_p th1 d th2 th3
  end.

Definition freshness_p_on_stack theta stack :=
  Forall3 freshness_p_on_triple ((bot, theta) :: stack).

Local Example forall2_example_1 :
  Forall2 le (0 :: 1 :: 3 :: 8 :: nil).
Proof.
  repeat apply Forall2_cons;
  repeat apply Forall_cons;
  repeat (apply le_S; try apply le_n); auto;
  try apply Forall2_nil.
Qed.

(* Lemmas *)

(* Forall, Forall2, Forall3 *)

Lemma Forall_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall p (u1 ++ (a :: u2)) ->
  Forall p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor.
  inversion Hfor as [| x l Hpa Hfor' [EQx EQl]].
  exact Hfor'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor.
  inversion Hfor as [| x l Hpb Hfor' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall_cons; auto.
Qed.

Local Lemma Forall2_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall2 p (u1 ++ (a :: u2)) ->
  Forall2 p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor2.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  exact Hfor2'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor2.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall2_cons.
  + (* Forall ... *)
  now apply Forall_sublist with a.
  + (* Forall2 ... *)
  now apply IHu1.
Qed.

Lemma Forall3_sublist {A : Type} :
  forall p (a : A) u1 u2,
  Forall3 p (u1 ++ (a :: u2)) ->
  Forall3 p (u1 ++ u2).
Proof.
  intros p a u1 u2.
  induction u1 as [| b u1 IHu1].
  - (* u1 = nil -> ... *)
  unfold app.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  exact Hfor3'.
  - (* u1 = b :: u1 -> ... *)
  repeat rewrite<- app_comm_cons.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x EQx l EQl.
  apply Forall3_cons.
  + (* Forall ... *)
  now apply Forall2_sublist with a.
  + (* Forall2 ... *)
  now apply IHu1.
Qed.

Local Lemma Forall2_hd2 {A : Type} :
  forall p (a : A) b u,
  Forall2 p (a :: b :: u) ->
  p a b.
Proof.
  intros p a b u H.
  inversion H as [| x l Hfor Hfor2 [EQx EQl]].
  clear x EQx l EQl H Hfor2.
  inversion Hfor as [| x l H Hfor' [EQx EQl]].
  exact H.
Qed.

Lemma Forall3_hd3 {A : Type} :
  forall p (a : A) b c u,
  Forall3 p (a :: b :: c :: u) ->
  p a b c.
Proof.
  intros p a b c u H.
  inversion H as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x EQx l EQl Hfor3' H.
  apply Forall2_hd2 with u.
  exact Hfor2.
Qed.
 
(* is_proper_stack *)

Lemma substack_is_proper_stack :
  forall a u1 u2,
  is_proper_stack (u1 ++ (a :: u2)) ->
  is_proper_stack (u1 ++ u2).
Proof.
  apply Forall_sublist.
Qed.

(* freshness_p_on_stack *)

Lemma substack_keeps_freshness_p_0 :
  forall theta d th u,
  freshness_p_on_stack theta ((d, th) :: u) ->
  freshness_p_on_stack th u.
Proof.
  intros theta d th u.
  unfold freshness_p_on_stack.
  intros Hfor3.
  inversion Hfor3 as [| x l Hfor2 Hfor3' [EQx EQl]].
  clear x l EQx EQl Hfor3.
  inversion Hfor3' as [| x l Hfor2' Hfor3 [EQx EQl]].
  clear x l EQx EQl Hfor3'.
  now apply Forall3_cons.
Qed.

Lemma substack_keeps_freshness_p :
  forall theta a u1 u2,
  freshness_p_on_stack theta (u1 ++ (a :: u2)) ->
  freshness_p_on_stack theta (u1 ++ u2).
Proof.
  intros theta a u1 u2.
  unfold freshness_p_on_stack.
  repeat rewrite app_comm_cons.
  apply Forall3_sublist.
Qed.

Lemma push_keeps_freshness_p :
  forall theta u z,
  freshness_p_on_stack theta u ->
  freshness_p_on_stack theta ((z, theta) :: u).
Proof.
  intros theta u z.
  unfold freshness_p_on_stack.
  intros H.
  apply Forall3_cons.
  - (* Forall2 ... ((z, theta) :: u) *)
  apply Forall2_cons.
  + (* Forall ... u *)
  apply Forall_forall.
  intros [d1 th1] Hth1.
  unfold freshness_p_on_triple.
  unfold freshness_p.
  split.
  * (* forall i j, th1 i = ... -> ... *)
  intros i j H1.
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  inversion Hfor2 as [EQu | x l Hfor Hfor2' EQx].
  -- (* u = nil -> ... *)
  rewrite<- EQu in Hth1.
  apply in_nil in Hth1.
  contradiction.
  -- (* u = x :: l -> ... *)
  exists j.
  exact H1.
  * (* forall j, d1 = ... -> ... *)
  intros j H1.
  exists j.
  exact H1.
  + (* Forall2 ... u *)
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  exact Hfor2.

  - (* Forall3 ... ((theta j, ) :: u) *)
  apply Forall3_cons.
  + (* Forall2 ... u *)
  induction u as [| [d1 th1] u IHu].
  * (* u = nil -> ... *)
  apply Forall2_nil.
  * (* u = (d1, th1) :: u -> ... *)
  apply Forall2_cons.
  -- (* Forall ... u *)
  apply Forall_forall.
  intros [d2 th2] Hth2.
  unfold freshness_p_on_triple.
  inversion H as [| x l Hfor2 Hfor3 [EQx EQl]].
  clear x EQx l EQl Hfor3.
  inversion Hfor2 as [| x l Hfor Hfor2' [EQx EQl]].
  clear x EQx l EQl Hfor2 Hfor2'.
  rewrite Forall_forall in Hfor.
  unfold freshness_p_on_triple in Hfor.
  apply (Hfor (d2, th2)).
  exact Hth2.
  -- (* Forall2 ... u *)
  apply IHu.
  apply (Forall3_sublist _ (d1, th1) ((bot, theta) :: nil)).
  unfold app.
  exact H.
  + (* Forall3 ... u *)
  apply (Forall3_sublist _ (bot, theta) nil).
  unfold app.
  exact H.
Qed.

(* config_R_config' *)

Lemma config_R_nil_nil_1 :
  forall q theta u phi,
  config_R_config' (q, theta, u) (q, phi, nil) ->
  u = nil.
Proof.
  intros q theta u phi.
  intro H.
  inversion H as [q1 theta1 u1 phi1 v1 HR].
  inversion HR.
  reflexivity.
Qed.

Lemma config_R_nil_nil_2 :
  forall q theta v phi,
  config_R_config' (q, theta, nil) (q, phi, v) ->
  v = nil.
Proof.
  intros q theta v phi.
  intro H.
  inversion H as [q1 theta1 u1 phi1 v1 HR].
  inversion HR.
  reflexivity.
Qed.
