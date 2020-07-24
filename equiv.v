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
