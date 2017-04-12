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

Module MyNot.

Definition not (P:Prop) := P -> False.

(* Notation "¬ x" := (not x) : type_scope. *)


Check not.
(* ===> Prop -> Prop *)

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P cont.
  destruct cont.
Qed.


Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P.
  unfold not.
  intros np.
  intros Q.
  intros H.
  apply np in H.
  inversion H.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Check (0 <> 1).

Eval compute in (0 <> 1).
Eval compute in (0 <> 0).

Theorem zero_not_one' : 0 <> 1.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q.
  intros [HP1 HP2].
  unfold not in HP2.
  apply HP2 in HP1.
  inversion HP1.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H.
  intros nQ.
  unfold not in nQ.
  unfold not.
  intros HP.
  apply H in HP.
  apply nQ in HP.
  inversion HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [H1 H2].
  apply H2 in H1.
  inversion H1.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Module MyIff.

Require Import  Coq.Setoids.Setoid.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  intros leq.
  unfold iff in leq.
  unfold iff.
  rewrite -> and_comm.
  apply leq.
Qed.

Theorem iff_sym_1 : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q.
  intros [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H1.
    rewrite -> H1.
    unfold not.
    intros H2.
    inversion H2.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  - intros H.
    apply H.
  - intros H.
    apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros [HPQ HQP].
  intros [HQR HRQ].
  split.
  - intros P1.
    apply HPQ in P1.
    apply HQR in P1.
    apply P1.
  - intros P1.
    apply HRQ in P1.
    apply HQP in P1.
    apply P1.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  unfold iff.
  split.
  - intros H1.
    destruct H1.
    + split.
      * apply or_intro.
        apply H.
      * apply or_intro.
        apply H.
    + split.
      * apply or_commut.
        apply or_intro.
        apply H.
      * apply or_commut.
        apply or_intro.
        apply H.
  - intros [H1 H2].
    destruct H1.
    + apply or_intro.
      apply H.
    + destruct H2.
      * apply or_intro.
        apply H0.
      * apply or_commut.
        apply or_intro.
        split. apply H. apply H0.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.        
  intros n m.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
 intros n m p.
 rewrite mult_0.
 rewrite mult_0.
 rewrite -> or_assoc.
 reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  apply mult_0.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.


Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n.
  intros [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P.
  intros H.
  unfold not.
  intro E.
  inversion E as [ x Hx ].
  apply Hx.
  apply H.
Qed.

Theorem dist_not_exists_2 : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P.
  intros H.
  unfold not.
  intros E.
  destruct E.
  apply H0.
  apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros H.
    destruct H.
    + destruct H.
      * left.
        exists x.
        apply H.
      * right.
        exists x.
        apply H.
  - intros H.
    destruct H.
    + destruct H.
      exists x.
      left.
      apply H.
    + destruct H.
      exists x.
      right.
      apply H.
Qed.

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
    | [] => False
    | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.

Example In_example_2 :
  forall n : nat, In n [2; 4] -> exists n': nat, n = 2 * n'.
Proof.
  simpl.
  intros n.
  intros [H | [H | []]].
  - exists 1.
    simpl. rewrite <- H.
    reflexivity.
  - exists 2.
    simpl.
    rewrite <- H.
    reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - simpl.
    intros [].
  - simpl. intros [H | H].
    left. rewrite -> H. reflexivity.
    apply IHl' in H.
    right. apply H.
Qed.
    
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - induction l as [| x' l' IHl'].
    + simpl.
      intros H.
      inversion H.
    + simpl.
      intros H.
      destruct H as [H1 | H2].
      * exists x'.
        split. apply H1.
        rewrite <- H1 in IHl'.
        left.
        reflexivity.
      * apply IHl' in H2.
        destruct H2.
        exists x.
        split. apply H.
        right.
        apply H.
  - intros H.
    destruct H.
    destruct H as [H1 H2].
    apply In_map with (f := f) in H2.
    rewrite -> H1 in H2.
    apply H2.
Qed.

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - generalize dependent l'.
    induction l as [| x l'' IHl].
    + simpl.
      intros l' H.
      right.
      apply H.
    + simpl.
      intros l' H.
      destruct H as [H1 | H2].
      * left. left. apply H1.
      * apply IHl in H2.
        destruct H2 as [H3 | H4].
        left. right. apply H3.
        right. apply H4.
  - generalize dependent l'.
    induction l as [| x l'' IHl'].
    + intros l' [H1 | H2].
      simpl in H1.
      inversion H1.
      simpl. apply H2.
    + simpl.
      intros l' [[H1 | H2] | H3].
      left. apply H1.
      specialize IHl' with l'.
      right.
      apply IHl'.
      left.
      apply H2.
      specialize IHl' with l'.
      right.
      apply IHl'.
      right.
      apply H3.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
    | [] => True
    | x :: l' => P x /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T), 
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - induction l as [| x l' IHl'].
    + simpl.
      intros H.
      apply I.
    + simpl.
      intros H.
      pose proof (H x) as HS.
      split.
      * apply HS.
        left.
        reflexivity.
      * apply IHl'.
        intros.
        pose proof (H x0) as HS2.
        apply HS2.
        right.
        apply H0.
  - intros H.
    induction l as [| x l' IHl'].
    + simpl.
      intros x.
      intros y.
      inversion y.
    + intros x0.
      simpl.
      simpl in H.
      destruct H as [H1 H2].
      intros H3.
      apply IHl'.
      apply H2.
      destruct H3.
      rewrite <- H.
      (* apply IHl' in H2. *)
Abort.

  

    
