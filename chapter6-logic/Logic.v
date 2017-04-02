Require Export Tactics.

Check 3 = 3.


Check forall n m : nat, n + m = m + n.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Check injective.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B.
  intros HA.
  intros HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  destruct n.
  - simpl.
    intros H.
    apply and_intro.
    + reflexivity.
    + apply H.
  - intros H.
    simpl in H.
    inversion H.
Qed.


