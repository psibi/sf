Require Export Poly.

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
      
    
