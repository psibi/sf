Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Lemma plus_help: forall n m: nat,
  S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [| n].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n].
  Case "n = 0".
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  Case "n = S n".
    simpl.
    rewrite -> IHn.
    rewrite -> plus_help.
    reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.  

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.



