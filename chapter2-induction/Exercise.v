Require Export Basics.
Require Export Induction.

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

Theorem mult_0_n : forall n:nat,
  0 * n = 0.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl.
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

Lemma add_n_1: forall n: nat,
    n + 1 = S n.
Proof.
  intros n.
  rewrite -> plus_comm.
  simpl.
  reflexivity.
Qed.

Lemma add_a_b_c : forall a b c : nat,
    a + (b + c) = (c + a) + b.
Proof.
  intros.
  rewrite -> plus_assoc at 1.
  symmetry.
  rewrite <- plus_assoc at 1.
  rewrite -> plus_comm at 1.
  reflexivity.
Qed.

Theorem add_helper: forall a b: nat,
    S (a + b) = a + S b.
Proof.
  intros a b.
  induction b as [|b' IHb'].
  - simpl. rewrite -> add_n_0. simpl. rewrite <- add_n_1. reflexivity.
  - rewrite <- IHb'. 
    rewrite -> plus_comm with (n := a) (m := S (S b')).
    rewrite <- add_n_1.
    rewrite <- add_n_1.
    rewrite <- add_n_1 with (n := S b').
    rewrite <- add_n_1 with (n := b').
    symmetry.
    rewrite -> plus_comm.
    symmetry.
    assert(H1: b' + 1 + 1 = S (S b')). {
      rewrite -> add_n_1.
      rewrite -> add_n_1.
      reflexivity.
    }
    rewrite -> plus_comm.
    rewrite -> add_n_1 with (n := (a + b')).
    rewrite -> IHb'.
    rewrite -> add_a_b_c at 1.
    rewrite -> add_n_1 with (n := S b').
    rewrite -> H1.
    rewrite -> plus_comm.
    reflexivity.
Qed.

Lemma mult_helper: forall n m : nat,
    m * S n = m * n + m.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - rewrite -> mult_0_n.
    simpl. reflexivity.
  - simpl.
    rewrite -> IHm'.
    rewrite -> add_helper.
    rewrite -> add_helper with (a := m' * n) (b := m').
    rewrite -> plus_comm at 1.
    symmetry.
    rewrite <- add_a_b_c at 1.
    symmetry.
    rewrite <- plus_assoc at 1.
    reflexivity.
Qed.    

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. 
    rewrite <- IHn'.
    rewrite <- plus_comm.
    rewrite -> mult_helper.
    reflexivity.
Qed.

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

Lemma plus_ble_compat_l_helper1 : forall n m : nat,
    leb n (n + m) = true.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma plus_ble_compat_l_helper2 : forall n m p : nat,
    leb (n + p) (n + m) = leb p m.
Proof.
  intros.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H1.
  induction n as [| n' IHn'].
  - simpl. rewrite -> add_n_0. 
    rewrite -> plus_ble_compat_l_helper1.
    reflexivity.
  - simpl.
    rewrite -> plus_ble_compat_l_helper2.
    rewrite -> H1.
    reflexivity.
Qed.



 
