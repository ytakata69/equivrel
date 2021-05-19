(*
 * Usage: You may need "make equiv.vo" before
 * using this file.
 * In vscode, you may also need to add
 * "coqtop.args": [ "-Q", "/path/to/this/dir", "" ]
 * to settings.json.
 *)

Require Import equiv.

(* Rules of RPDA A and PDA A' *)

Local Open Scope type_scope.  (* for '*' *)

Parameter Sigma : Set.  (* finite alphabet *)

Parameter Q : Set.  (* finite control states *)
Definition Q' := Q * Phi.

Inductive Com :=
  | pop
  | skip
  | push (j : nat).
Inductive Com' :=
  | pop'
  | skip'
  | push' (phi : Phi).

Parameter ruleA :
  Q -> Sigma -> Tst -> Q -> Asgn -> Com -> Prop.

Inductive ruleA'
  : Q' -> Sigma -> Phi -> Q' -> Com' -> Prop :=
  | ruleA'_skip :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn skip ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, composition phi2 phi3) skip'
  | ruleA'_pop :
    forall q1 phi2 a phi1 q2 phi3 tst asgn,
    ruleA q1 a tst q2 asgn pop ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, composition (composition phi1 phi2) phi3) pop'
  | ruleA'_push :
    forall q1 phi2 a phi1 q2 phi3 tst asgn j,
    ruleA q1 a tst q2 asgn (push j) ->
    composable phi1 phi2 ->
    composableT phi2 phi3 ->
    Phi_tst_asgn tst asgn phi3 ->
    ruleA' (q1, phi2) a phi1
           (q2, phi_to_Phi_eq_j j phi3) (push' (composition phi2 phi3)).

(* Configurations and transitions between configurations *)

Definition Stack  := list (D * Theta).
Definition Stack' := list Phi.

Definition config  := Q  * Theta * Stack.
Definition config' := Q' * Stack'.

Definition update_stack (u : Stack) theta com :=
  match com with
  | pop =>
    match u with
     | cons _ u' => u'
     | nil => nil
     end
  | skip => u
  | push j => cons (theta j, theta) u
  end.

Definition update_stack' (u : Stack') com' :=
  match com' with
  | pop' =>
    match u with
     | cons _ u' => u'
     | nil => nil
     end
  | skip' => u
  | push' z => cons z u
  end.

Inductive moveA
  : config -> Sigma -> D -> config -> Prop :=
  | MoveA :
    forall tst asgn com q1 q2 a d z u theta theta' zth,
    ruleA q1 a tst q2 asgn com ->
    (theta, d, z) |= tst ->
    theta' = update theta asgn d ->
    moveA (q1, theta,  (cons (z, zth) u)) a d
          (q2, theta', update_stack (cons (z, zth) u) theta' com).

Inductive moveA'
  : config' -> Sigma -> config' -> Prop :=
  | MoveA' :
    forall q1 q2 a z u com',
    ruleA' q1 a z q2 com' ->
    moveA' (q1, (cons z u)) a
           (q2, update_stack' (cons z u) com').

Inductive stack_R_stack'
  : Theta -> Stack -> Phi -> Stack' -> Prop :=
  | Stack_R_stack'_nil :
    forall theta phi,
    (theta_bot, bot, theta) |= phi ->
    stack_R_stack' theta nil phi nil
  | Stack_R_stack'_cons :
    forall theta ptheta d phi pphi u v,
    (ptheta, d, theta) |= phi ->
    stack_R_stack' ptheta u pphi v ->
    stack_R_stack' theta (cons (d, ptheta) u) phi (cons pphi v).

Inductive config_R_config'
  : config -> config' -> Prop :=
  | Config_R_config' :
    forall q theta u phi v,
    stack_R_stack' theta u phi v ->
    config_R_config' (q, theta, u) ((q, phi), v).

(* Utility: sublist, proper_sublist *)

Inductive sublist {X : Type} : list X -> list X -> Prop :=
  | Sublist_nil    : forall l, sublist nil l
  | Sublist_cons_right :
      forall l1 l2 x, sublist l1 l2 -> sublist l1 (cons x l2)
  | Sublist_cons_both :
      forall l1 l2 x, sublist l1 l2 -> sublist (cons x l1) (cons x l2).

Example sublist_example_1 :
  sublist (cons 2 (cons 3 nil)) (cons 1 (cons 2 (cons 3 nil))).
Proof.
  apply Sublist_cons_right.
  apply Sublist_cons_both.
  apply Sublist_cons_both.
  apply Sublist_nil.
Qed.

(* Freshness on stack *)

Inductive freshness_on_stack
  : Theta -> Stack -> Prop :=
  | Freshness_on_stack :
    forall theta stack,
    forall u1 u2 u3 th1 th2 th3 d1 d2 d3,
    sublist (cons (d1, th1) u1) u2 ->
    sublist (cons (d2, th2) u2) u3 ->
    sublist (cons (d3, th3) u3) (cons (bot, theta) stack) ->
    freshness_p th1 d1 th2 th3 ->
    freshness_on_stack theta stack.

(* Theorems *)

Lemma moveA_inversion :
  forall q q' theta theta' u u' a d,
  moveA (q, theta, u) a d (q', theta', u') ->
  exists tst asgn com,
  ruleA q a tst q' asgn com /\
  theta' = update theta asgn d /\
  u' = update_stack u theta' com.
Proof.
  intros q q' theta theta' u u' a d.
  intros Hm.
  inversion Hm as [tst asgn com].
  exists tst, asgn, com.
  split; [| split]; auto.
Qed.

Lemma bisimilar_1 :
  forall q theta_n phi_n v u,
  forall a d q' theta' v',
  config_R_config' (q, theta_n, v) ((q, phi_n), u) ->
  moveA (q, theta_n, v) a d (q', theta', v') ->
  exists phi'' u',
  moveA' ((q, phi_n), u) a ((q', phi''), u') /\
  config_R_config' (q', theta', v') ((q', phi''), u').
Proof.
  intros q theta_n phi_n v u.
  intros a d q' theta' v'.
  intros HR HmA.
  apply moveA_inversion in HmA as HrA.
  destruct HrA as [tst [asgn [com [HrA [Hth' Hv']]]]].
  case_eq u.
Admitted.
(*
  case_eq com.
  - intros Hcom.
  rewrite Hcom in HrA.
  apply (ruleA'_pop q phi_n a _ q' (composition (composition phi_n)) tst asgn) in HrA.
  rewrite Hcom in Hv'.
  unfold update_stack in Hv'.
  *)
