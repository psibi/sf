Require Export Poly.
Require Import Coq.Arith.Mult.

Check mult_assoc.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p.
  intros eq1.
  intros eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m.
  intros eq1.
  intros eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1.
  intros H2.
  apply H1.
  apply H2.
Qed.

Lemma rev_empty : forall (X : Type) (l : list X),
    l = [] -> rev l = [].
Proof.
  intros X l.
  intros H.
  rewrite -> H.
  simpl. reflexivity.
Qed.

Check nil.


Lemma rev_injective : forall (X : Type) (l1 l2 : list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2.
  intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  intros H.
  apply rev_injective.
  rewrite -> rev_involutive.
  symmetry.
  apply H.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f.
  intros eq1.
  intros eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intros eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c; d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros H1.
  intros H2.
  apply trans_eq with (m := m).
  apply H2.
  apply H1.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H. 
  reflexivity. Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H as [Hnm].
  reflexivity. Qed.

 Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
  intros X x y z l j.
  intros H1.
  intros H2.
  inversion H1 as [H11].
  inversion H2 as [H21].
  rewrite -> H11.
  reflexivity.
Qed.


Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl. reflexivity.
  - simpl.
    intros H.
    inversion H.
Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. 
  inversion contra.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example inversion_ex6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
  intros X x y z l j.
  intros H1.
  intros H2.
  inversion H1.
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. 
  intros A B f x y eq.
  rewrite eq.
  reflexivity. Qed.  

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H. 
  apply H. 
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Lemma s_inj_2 : forall n m,
    n = m -> S n = S m.
Proof.
  intros n m.
  induction n as [| n'].
  - intros H1.
    rewrite <- H1.
    reflexivity.
  - intros H1.
    rewrite -> H1.
    reflexivity.
Qed.

Lemma s_inj_3 : forall n m,
    n = m -> S n = S m.
Proof.
  intros n m.
  intros H.
  destruct n as [| n'].
  - simpl. rewrite -> H.
    reflexivity.
  - rewrite -> H.
    reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. 
    intros m H.
    symmetry in H.
    destruct m as [| m'].
    + reflexivity.
    + rewrite -> plus_Sn_m in H.
      inversion H.
  - simpl.
    rewrite <- plus_n_Sm.
    intros m.
    intros H.
    destruct m as [| m'].
    + simpl in H.
      inversion H.
    + rewrite -> plus_Sn_m in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' with (m := m') in H1.
      apply s_inj_2.
      apply H1.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
     double n = double m ->  n = m.
Proof.
  intros n m. 
  induction n as [| n'].
  - simpl.
    intros eq.
    destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - intros eq.
    destruct m as [| m'].
    + inversion eq.
    + apply f_equal.
Abort.

Theorem double_injective : forall n m,
     double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - simpl.
    intros m eq.
    destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - simpl.
    intros m eq.
    destruct m as [| m'].
    + inversion eq.
    + simpl in eq.
      apply f_equal.
      apply IHn'.
      apply S_injective.
      apply S_injective.
      rewrite -> eq.
      reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl.
    destruct m.
    + intros eq1.
      reflexivity.
    + intros eq1.
      inversion eq1.
  - simpl.
    destruct m.
    + intros eq1.
      inversion eq1.
    + intros eq1.
      apply IH in eq1.
      rewrite -> eq1.
      reflexivity.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. 
  induction m as [| m'].
  - simpl.
    intros eq. 
    destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + apply f_equal.
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl.
    destruct n.
    + simpl.
      reflexivity.
    + intros eq.
      inversion eq.
  - simpl.
    destruct n.
    + simpl.
      intros eq.
      inversion eq.
    + simpl.
      intros eq.
      apply S_injective in eq.
      apply S_injective in eq.
      apply IHm' in eq.
      rewrite -> eq.
      reflexivity.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| n' ].
  - simpl.
    intros n eq.
    reflexivity.
  - simpl.
    intros n eq.
    destruct n as [| n''].
    + simpl.
      inversion eq.
    + apply S_injective in eq.
      apply IHl in eq.
      simpl.
      rewrite -> eq.
      reflexivity.
Qed.

Definition square n := n * n.

Check mult_assoc.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| n l'].
  - simpl.
    intros l1 l2 eq.
    inversion eq.
    simpl.
    reflexivity.
  - intros l1 l2.
    intros eq.
Admitted.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Eval compute in sillyfun1 1.
Eval compute in sillyfun1 2.
Eval compute in sillyfun1 3.
Eval compute in sillyfun1 4.
Eval compute in sillyfun1 5.
Eval compute in sillyfun1 6.
Eval compute in sillyfun1 11.
Eval compute in oddb 11.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_nat_true in Heqe3.
    rewrite -> Heqe3.
    unfold oddb.
    reflexivity.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_nat_true in Heqe5.
      rewrite -> Heqe5.
      unfold oddb.
      reflexivity.
    + inversion eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:H1.
  - destruct (f true) eqn:H2.
    + rewrite -> H2.
      reflexivity.
    + destruct (f false) eqn:H3.
      * reflexivity.
      * destruct b in H1.
Abort.        

Theorem bool_fn_applied_thrice_1 :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  + destruct (f true) eqn:H1.
    - rewrite -> H1.
      rewrite -> H1.
      reflexivity.
    - destruct (f false) eqn:H2.
      * rewrite -> H1.
        reflexivity.
      * rewrite -> H2.
        reflexivity.
  + destruct (f false) eqn:H1.
    - destruct (f true) eqn:H2.
      * rewrite -> H2.
        reflexivity.
      * rewrite -> H1.
        reflexivity.
    - rewrite -> H1.
      rewrite -> H1.
      reflexivity.
Qed.
      


    
