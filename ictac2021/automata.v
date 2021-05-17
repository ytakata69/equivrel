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

Definition ruleA' (q'1 : Q') (a : Sigma) (phi1 : Phi)
                  (q'2 : Q') (com' : Com') : Prop :=
  match q'1, q'2 with
  | (q1, phi2), (q2, phi') =>
    composable phi1 phi2 /\
    exists tst asgn,
    match com' with
    | skip' =>
        ruleA q1 a tst q2 asgn skip /\
        exists phi3,
          composableT phi2 phi3 /\
          Phi_tst_asgn tst asgn phi3 /\
          phi' = composition phi2 phi3
    | pop' =>
        ruleA q1 a tst q2 asgn pop /\
        exists phi3,
          composableT phi2 phi3 /\
          Phi_tst_asgn tst asgn phi3 /\
          phi' = composition (composition phi1 phi2) phi3
    | push' phi'' =>
        exists j,
          ruleA q1 a tst q2 asgn (push j) /\
        exists phi3,
          composableT phi2 phi3 /\
          Phi_tst_asgn tst asgn phi3 /\
          phi' = phi_to_Phi_eq_j j phi3 /\
          phi'' = composition phi2 phi3
    end
  end.

Definition Stack  := list (D * Theta).
Definition Stack' := list Phi.

Definition config  := Q  * Theta * Stack.
Definition config' := Q' * Stack'.

Definition moveA (c1 : config) a d (c2 : config) : Prop :=
  match c1, c2 with
  | (q1, theta, u), (q2, theta', u') =>
    match u with
    | cons (z, th) tl =>
      exists tst asgn,
      (theta, d, z) |= tst /\
      theta' = update theta asgn d /\
      exists com,
      ruleA q1 a tst q2 asgn com /\
      match com with
      | pop  => u' = tl
      | skip => u' = u
      | push j => u' = cons (theta' j, theta') u
      end
    | nil => False
    end
  end.

Definition moveA' (c1 : config') a (c2 : config') : Prop :=
  match c1, c2 with
  | (q1, u), (q2, u') =>
    match u with
    | cons z tl =>
      exists com',
      ruleA' q1 a z q2 com' /\
      match com' with
      | pop'  => u' = tl
      | skip' => u' = u
      | push' z' => u' = cons z' u
      end
    | nil => False
    end
  end.

Fixpoint stack_R_stack' theta u phi v :=
  match u, v with
  | cons (d, ptheta) u', cons pphi v' =>
    (ptheta, d, theta) |= phi /\
    stack_R_stack' ptheta u' pphi v'
  | nil, nil =>
    (theta_bot, bot, theta) |= phi
  | _, _ => False
  end.

Definition config_R_config' (c1 : config) (c2 : config') : Prop :=
  match c1, c2 with
  | (q1, theta, u), ((q2, phi), v) =>
    q1 = q2 /\ stack_R_stack' theta u phi v
  end.

Local Close Scope type_scope.
