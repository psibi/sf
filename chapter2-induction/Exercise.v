Require Export Basics.

Print LoadPath.

Check test.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - simpl. rewrite -> plus_comm. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). 
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  rewrite <- plus_assoc.
  reflexivity.
Qed.

Check mult.

Lemma add_n_0: forall n: nat,
    n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma mult_n_1: forall n: nat,
    n * 1 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma mult_n_0: forall n: nat,
    n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'. reflexivity. Qed.

Lemma mult_helper: forall n m : nat,
    m * S n = m + m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. 
    rewrite -> mult_n_1.
    rewrite -> mult_n_0.
    rewrite -> add_n_0.
    reflexivity.
  - simpl.
    destruct m as [| m'].
    simpl. reflexivity.
    rewrite -> IHn'.
Admitted.    


Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite <- IHn'.  
    rewrite <- mult_helper.
    reflexivity. Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H1.
  induction n as [| n' IHn'].
  - simpl.
Admitted.
      
 
