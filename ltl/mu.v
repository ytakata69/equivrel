Require Import Nat Arith.
Require Import List.

(* data words *)

Parameter D : Set.  (* a data domain *)
Definition At := nat.  (* a finite set of atomic props *)
Definition Sigma := At -> bool.  (* 2^{At} *)
Definition data_word := list (Sigma * D)%type.

(* LTL syntax *)

Definition register := nat.
Parameter V : Set.

Inductive ltl_atom :=
  | tt : ltl_atom
  | MATCH : register -> ltl_atom
  | p : At -> ltl_atom  (* an atomic proposition *)
  | END : ltl_atom
  .

Inductive ltl_phi :=
  | pos : ltl_atom -> ltl_phi  (* a positive literal *)
  | neg : ltl_atom -> ltl_phi  (* a negative literal *)
  .

Inductive ltl :=
  | var : V -> ltl
  | OR  : ltl -> ltl -> ltl
  | AND : ltl -> ltl_phi -> ltl
  | STORE : register -> ltl -> ltl
  | X : ltl -> ltl
  | until : ltl_phi -> ltl -> ltl
  | PHI : ltl_phi -> ltl
  | G : ltl_phi -> ltl
  .

Notation "'↑' r" := (MATCH r) (at level 75).
Notation "a '.\/' b" := (OR   a b) (at level 85, right associativity).
Notation "a './\' b" := (AND  a b) (at level 75, right associativity).
Notation  "'[' a ']'" := (pos a).
Notation "'~[' a ']'" := (neg a).
Notation "'φ' p" := (PHI p) (at level 78).
Notation "a 'U' b" := (until a b) (at level 73, right associativity).
Notation "'↓' r ',' psi" := (STORE r psi) (at level 200).

(*
Check (AND (STORE 1 (X (OR (PHI (neg (p 1))) (PHI (pos (p 2)))))) (pos (↑ 1))).
Check ((↓1, X ((φ ~[p 1]) .\/ (φ [p 2]))) ./\ [↑1]).
*)

(* semantics *)

Definition Theta := register -> D.

Definition update
  (theta : Theta) (i : register) (d : D) : Theta :=
  fun (r : register) => if r =? i then d else theta r.

Definition Env := V -> data_word -> Theta -> bool.

(*
Inductive models_atom :
  data_word -> Theta -> ltl_atom -> Prop :=
  | models_tt : forall w theta, models_atom w theta tt
  | models_p  : forall h t theta a,
      fst h a = true -> models_atom (h::t) theta (p a)
  | models_MATCH : forall h t theta r,
      snd h = theta r -> models_atom (h::t) theta (↑ r)
  | models_END : forall theta, models_atom nil theta END
  .

Inductive models_phi :
  data_word -> Theta -> ltl_phi -> Prop :=
  | models_pos : forall w theta atom,
      models_atom w theta atom ->
      models_phi w theta (pos atom)
  | models_neg : forall w theta atom,
      (~ models_atom w theta atom) ->
      models_phi w theta (neg atom)
  .
*)

Definition models_atom
  (w : data_word) (theta : Theta) (atom : ltl_atom)
  : Prop :=
  match w, atom with
  | _, tt => True
  | h::t, p a => fst h a = true
  | h::t, ↑ r => snd h = theta r
  | nil, END => True
  | _, _ => False
  end.

Definition models_phi
  (w : data_word) (theta : Theta) (phi : ltl_phi)
  : Prop :=
  match phi with
  | pos atom =>   models_atom w theta atom
  | neg atom => ~ models_atom w theta atom
  end.

Inductive Forall_mid_suffix {A : Type} :
  (list A -> Prop) -> list A -> list A -> Prop :=
  | Forall_mid_base : forall p l, Forall_mid_suffix p l l
  | Forall_mid_ind  : forall p s x l,
      Forall_mid_suffix p s l -> p (x::l) ->
      Forall_mid_suffix p s (x::l)
  .
Definition Forall_nonnil_suffix {A : Type}
  (p : list A -> Prop) (l : list A) : Prop :=
  Forall_mid_suffix p nil l.

Inductive models :
  data_word -> Theta -> Env -> ltl -> Prop :=
  | models_PHI : forall w theta u phi,
      models_phi w theta phi ->
      models w theta u (φ phi)
  | models_STORE : forall h t theta u r psi,
      models (h::t) (update theta r (snd h)) u psi ->
      models (h::t) theta u (↓ r, psi)
  | models_X : forall h t theta u psi,
      models t theta u psi ->
      models (h::t) theta u (X psi)
  | models_AND : forall w theta u psi phi,
      models w theta u psi ->
      models_phi w theta phi ->
      models w theta u (AND psi phi)
  | models_OR : forall w theta u psi1 psi2,
      models w theta u psi1 \/
      models w theta u psi2 ->
      models w theta u (OR psi1 psi2)
  | models_G : forall w theta u phi,
      Forall_nonnil_suffix (fun t => models_phi t theta phi) w ->
      models w theta u (G phi)
  | models_U : forall w theta u phi psi,
      (exists w',
       models w' theta u psi /\
       Forall_mid_suffix (fun t => models_phi t theta phi) w' w) ->
      models w theta u (phi U psi)
  | models_var : forall w theta u v,
      u v w theta = true ->
      models w theta u (var v)
  .

Notation "'(' w ',' theta '|=' u ',' psi ')'"
  := (models w theta u psi).

(* Equality of two ltl formulas *)

Axiom ltl_extensionality :
  forall psi1 psi2 : ltl,
    (forall w theta u, (w, theta |= u, psi1) <-> (w, theta |= u, psi2))
    -> psi1 = psi2.

Axiom Theta_extensionality :
  forall theta1 theta2 : Theta,
    (forall r, theta1 r = theta2 r) -> theta1 = theta2.

(* utilities *)

(*
Inductive is_suffix_of {A : Type} :
  list A -> list A -> Prop :=
  | is_suffix_of_base : forall l, is_suffix_of l l
  | is_suffix_of_Ind  : forall s h t,
    is_suffix_of t s -> is_suffix_of (h::t) s
  .

Local Lemma Forall_mid_only_on_suffix {A : Type} :
  forall (p : list A -> Prop) s l,
  Forall_mid_suffix p s l ->
  is_suffix_of l s.
Proof.
  intros p s l.
  induction l as [| x l IH].
  - intros H.
  inversion H.
  apply is_suffix_of_base.
  - intros H.
  inversion H.
  + apply is_suffix_of_base.
  + apply is_suffix_of_Ind.
  now apply IH.
Qed.
*)

(* distribution over OR *)

Lemma distr_X_over_OR :
  forall psi1 psi2,
    (X (psi1 .\/ psi2)) = (X psi1 .\/ X psi2).
Proof.
  intros psi1 psi2.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  apply models_OR.
  inversion H
  as [| | h t th u' psi Hor EQht EQth EQu' EQpsi | | | | |].
  clear th EQth u' EQu' psi EQpsi.
  inversion Hor
  as [| | | | w' th u' p1 p2 Hor' EQw' EQth EQu' [EQp1 EQp2] | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hor' as [Hor' | Hor'].
  + left. now apply models_X.
  + right. now apply models_X.
  - intros H.
  inversion H
  as [| | | | w' th u' p1 p2 Hor EQw' EQth EQu' [EQp1 EQp2] | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hor as [Hor | Hor];
  inversion Hor
  as [| | h t th u' psi Hor' EQht EQth EQu' EQpsi | | | | |];
  clear th EQth u' EQu' psi EQpsi;
  apply models_X;
  apply models_OR.
  + now left.
  + now right.
Qed.

Lemma G_equals_phi_U_end :
  forall phi,
    (G phi) = (phi U (φ [END])).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  inversion H
  as [| | | | | w' th u' p Hsuf EQw' EQth EQu' EQp | |].
  clear w' EQw' th EQth u' EQu' p EQp.
  apply models_U.
  exists nil.
  split.
  + apply models_PHI.
  unfold models_phi.
  now unfold models_atom.
  + apply Hsuf.
  - intros H.
  inversion H
  as [| | | | | | w' th u' p1 p2 Hu EQw' EQth EQu' [EQp1 EQp2]|].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hu as [w' [Hw' Hsuf]].
  inversion Hw'
  as [w'' th u' p Hend EQw'' EQth EQu' EQp | | | | | | |].
  clear w'' EQw'' th EQth u' EQu' p EQp.
  unfold models_phi in Hend.
  unfold models_atom in Hend.
  destruct w'.
  + now apply models_G.
  + contradiction.
Qed.

Lemma U_equals_psi_or_phi_and_XU :
  forall phi psi,
    (phi U psi) = (psi .\/ X (phi U psi) ./\ phi).
Proof.
  intros phi psi.
  apply ltl_extensionality.
  intros w theta.
  split.
  - intros H.
  apply models_OR.
  inversion H
  as [| | | | | | w' th u' p1 p2 Hsuf EQw' EQth EQu' [EQp1 EQp2]|].
  clear H w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hsuf as [w' [Hw' Hsuf]].
  destruct w as [| h t].
  + inversion Hsuf as [p l EQp EQl EQw' |].
  rewrite EQw' in Hw'.
  now left.
  + inversion Hsuf
  as [p l EQp EQl EQw'| p s x l Hsuf' Hp EQp EQs [EQx EQl]].
  * rewrite EQw' in Hw'.
  now left.
  * clear p EQp s EQs x EQx l EQl.
  right.
  apply models_AND; auto.
  apply models_X.
  apply models_U.
  now exists w'.
  - intros H.
  inversion H
  as [| | | | w' th u' p1 p2 Hor EQw' EQu' EQth [EQp1 EQp2] | | |].
  clear H w' EQw' th u' EQu' EQth p1 EQp1 p2 EQp2.
  apply models_U.
  destruct Hor as [H | H].
  + exists w.
  split; auto.
  apply Forall_mid_base.
  + inversion H
  as [| | | w' th u' p1 p2 Hw Hp EQw' EQth EQu' [EQp1 EQp2]| | | |].
  clear w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  inversion Hw
  as [| |h t th u' p1 Ht EQht EQth EQu' EQp1| | | | |].
  clear th EQth u' EQu' p1 EQp1.
  inversion Ht
  as [| | | | | | w' th u' p1 p2 Hsuf EQw' EQth EQu' [EQp1 EQp2]|].
  clear H w' EQw' th EQth u' EQu' p1 EQp1 p2 EQp2.
  destruct Hsuf as [w' [Hw' Hsuf]].
  exists w'.
  rewrite <- EQht in Hp.
  split; auto.
  apply Forall_mid_ind; auto.
Qed.
