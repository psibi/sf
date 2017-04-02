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

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m.
  intros H.
  destruct H as [Hn Hm].
  rewrite -> Hn.
  rewrite -> Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m.
  intros [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q.
  intros H.
  destruct H as [HP HQ].
  apply HP.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R.
  intros [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite -> Hn.
    reflexivity.
  - rewrite -> Hm.
    rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B.
  intros HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros n.
  destruct n.
  - left.
    reflexivity.
  - right.
    simpl.
    reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  intros H.
  destruct n.
  - left. reflexivity.
  - simpl in H.
    apply and_exercise in H.
    destruct H as [Hm Hnm].
    right.
    apply Hm.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q.
  intros H.
  destruct H.
  - right.
    apply H.
  - left.
    apply H.
Qed.



