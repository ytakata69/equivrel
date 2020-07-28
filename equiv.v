Require Export Nat Arith.EqNat.

(* assignments *)

Parameter D : Set.
Definition assignment := nat -> D.

Definition update (theta : assignment) (i : nat) (d : D) : assignment :=
  fun j : nat => if j =? i then d else theta j.

Axiom outside_data_exists :
  forall theta : assignment, exists d : D, forall i, theta i <> d.

Axiom outside_data_exists' :
  forall theta theta': assignment, exists d : D,
    (forall i, theta i <> d) /\ (forall i, theta' i<> d).

(* guard *)

Definition guard := nat -> Prop.  (* a subset of nat *)

(* note: b_is_empty_or_not can be proved under the classical logic. *)
Axiom b_is_empty_or_not :
  forall b : guard, (forall i, ~ b i) \/ exists i, b i.

(* equivalence relations *)

Inductive register :=
  | X  (i : nat)
  | X' (i : nat).

Definition Rel := register -> register -> Prop.

Definition is_reflexive  (phi : Rel) : Prop := forall x, phi x x.
Definition is_symmetric  (phi : Rel) : Prop := forall x y, phi x y -> phi y x.
Definition is_transitive (phi : Rel) : Prop :=
  forall x y z, phi x y /\ phi y z -> phi x z.
Definition is_equiv_rel   (phi : Rel) : Prop :=
  is_reflexive phi /\ is_symmetric phi /\ is_transitive phi.

Definition lat (phi : Rel) : Rel :=
  fun xi xj : register =>
    match xi, xj with
    | (X i), (X j) => phi (X' i) (X' j)
    | x, y => x = y
    end.

Definition former (phi : Rel) : Rel :=
  fun xi xj : register =>
    match xi, xj with
    | (X i), (X j) => phi (X i) (X j)
    | x, y => x = y
    end.

Definition inv (phi : Rel) (i : nat) : guard :=
  fun l : nat => phi (X l) (X' i).

Definition after (gamma : Rel) (b : guard) (i : nat) : Rel :=
  fun xj xl : register =>
    match xj, xl with
    | (X j), (X l) => if j =? i then b l \/ l = i else
                      if l =? i then b j          else gamma (X j) (X l)
    | x, y => x = y
    end.

Definition afterR (phi : Rel) (b : guard) (i : nat) : Rel -> Prop :=
  fun phi' : Rel =>
    former phi' = former phi /\
    lat phi' = after (lat phi) b i /\
    (forall j l, (phi (X j) (X' l) /\ b l -> phi' (X j) (X' i)) /\
              (~ (phi (X j) (X' l) <-> b l) -> ~ phi' (X j) (X' i))) /\
    forall j l, l <> i -> (phi (X j) (X' l) <-> phi' (X j) (X' l)).

Definition afterL (phi : Rel) (i : nat) : Rel :=
  fun xl xj : register =>
    match xl, xj with
    | (X  l), (X  j) => (after (former phi) (inv phi i) i) xl xj
    | (X' l), (X' j) => phi xl xj
    | (X  l), (X' j) => if l =? i then phi (X' i) (X' j) else phi xl xj
    | (X' l), (X  j) => if j =? i then phi (X' i) (X' l) else phi xl xj
    end.

Definition rel_between (theta1 theta2 : assignment) : Rel :=
  fun xi xj : register =>
    match xi, xj with
    | (X  i), (X  j) => theta1 i = theta1 j
    | (X  i), (X' j) => theta1 i = theta2 j
    | (X' i), (X  j) => theta2 i = theta1 j
    | (X' i), (X' j) => theta2 i = theta2 j
    end.

(* an equivalence relation over (X i)'s *)
Definition is_simpl_rel (phi : Rel) :=
  forall xi xj : register,
    match xi, xj with
    | (X i), (X j) => True
    | x, y => phi x y <-> x = y
    end.

Axiom rel_extensionality :
  forall phi phi' : Rel,
    (forall x y, phi x y <-> phi' x y) -> phi = phi'.

(* models *)

Class Models (A B : Type) := models : A -> B -> Prop.
Notation "S '|=' T" := (models S T) (at level 59).

Instance rel_models_guard : Models Rel guard :=
  { models phi b := forall i, b i ->
                    forall j, b j <-> phi (X i) (X j) }.
Instance assignment_models_rel : Models assignment Rel :=
  { models theta phi := is_simpl_rel phi /\
                        forall i j, theta i = theta j <-> phi (X i) (X j) }.
Instance assignmentD_models_guard : Models (assignment * D) guard :=
  { models theta_d b :=
      match theta_d with
      | (theta, d) => forall i, theta i = d <-> b i
      end }.
Instance two_assignments_model_rel : Models (assignment * assignment) Rel :=
  { models pair phi :=
      match pair with
      | (theta, theta') =>
          forall i j, (theta  i = theta  j <-> phi (X  i) (X  j)) /\
                      (theta' i = theta' j <-> phi (X' i) (X' j)) /\
                      (theta  i = theta' j <-> phi (X  i) (X' j)) /\
                      (theta' i = theta  j <-> phi (X' i) (X  j))
      end }.

(* grammar *)

Local Open Scope type_scope.

Parameter V : Set.  (* nonterminals *)
Definition V' := V * Rel.

Parameter ruleG :
  V' -> (option (guard * nat)) -> (option nat) -> V' -> Prop.

Axiom ruleG_is_normal_form :
  forall A B gamma gamma' jj,
    (ruleG (A, gamma) None jj (B, gamma') -> gamma = gamma') /\
    (forall b i,
     ruleG (A, gamma) (Some (b, i)) jj (B, gamma') ->
       gamma |= b /\ gamma' = after gamma b i).

Definition ruleG' (v1 : V') (gg : option (guard * nat)) (jj : option nat)
                  (v2 : V') : Prop :=
  match v1, v2 with
  | (A, phi), (B, phi') =>
    match gg with
    | Some (b, j) =>
        ruleG (A, lat phi) None (Some j) (B, lat phi') /\
           b = inv phi j /\
        phi' = afterL phi j /\
          jj = Some j
    | None =>
       (ruleG (A, lat phi) None None (B, lat phi') /\
        phi' = phi /\ jj = None) \/
       (exists b i,
        ruleG (A, lat phi) (Some (b, i)) None (B, lat phi') /\
        afterR phi b i phi' /\ jj = None)
    end
  end.

Definition config := V' * assignment.

Definition derivG (c1 : config) (dd : option D) (c2 : config) : Prop :=
  match c1, c2 with
  | ((A, gamma), theta), ((B, gamma'), theta') =>
    match dd with
    | Some d =>
        exists j,
        ruleG (A, gamma) None (Some j) (B, gamma') /\
        theta = theta' /\ d = theta j
    | None =>
       (ruleG (A, gamma) None None (B, gamma') /\
        theta = theta')
        \/
       (exists b i d,
        ruleG (A, gamma) (Some (b, i)) None (B, gamma') /\
        (theta, d) |= b /\ theta' = update theta i d)
    end
  end.

Definition derivG' (c1 : config) (dd : option D) (c2 : config) : Prop :=
  match c1, c2 with
  | ((A, phi), theta), ((B, phi'), theta') =>
    match dd with
    | Some d' =>
        exists b i j d,
        ruleG' (A, phi) (Some (b, i)) (Some j) (B, phi') /\
        (theta, d) |= b /\
        theta' = update theta i d /\
        d' = theta' j
    | None =>
        ruleG' (A, phi) None None (B, phi') /\
        theta = theta'
    end
  end.

Local Close Scope type_scope.
