Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
    match d with
      | monday => tuesday
      | tuesday => wednesday
      | wednesday => thursday
      | thursday => friday
      | friday => monday
      | saturday => monday
      | sunday => monday
    end.

Eval compute in (next_weekday friday).

Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Check true.




Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Check (negb true).

Eval compute in (negb true).

Check negb.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Check O.

Definition pred (n:nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
      | O => O
      | S O => O
      | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Eval compute in (minustwo 3).

Eval compute in pred O.
Eval compute in pred (S (S O)).

Eval compute in (minustwo (S (S O))).
Eval compute in (minustwo (S (S (S (S O))))).

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
    | O => m
    | (S n') => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Eval compute in (mult 3 3).

Fixpoint minus (n m: nat) : nat :=
  match n, m with
    | 0, _ => 0
    | S _ , 0 => n
    | S n' , S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => (S O)
    | S p => mult base (exp base p)
  end.

Check ((0 +1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n,m with
    | O,O => true
    | O,(S n') => false
    | S n',O => false
    | S n',S m' => beq_nat n' m'
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n,m with
    | O,O => true
    | O,(S n') => true
    | S n',O => false
    | S n',S m' => ble_nat n' m'
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  match n,m with
    | O,O => false
    | O,(S n') => true
    | (S n'),O => false
    | (S n'),(S m') => andb (ble_nat n' m') (negb (beq_nat n' m'))
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O : forall n, n+0 = n.
Proof.
  simpl.
Abort.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. 
  simpl.
  reflexivity. 
Qed.

Theorem plus_id_example : forall n m: nat,
                            n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Inductive bin : Type :=
  | zero : bin
  | twice : bin -> bin
  | twice_plus_one : bin -> bin.

Fixpoint twice_nat (n:nat) : nat :=
  match n with
    | O => O
    | (S n') => S (S (twice_nat n'))
end.

Fixpoint bin_to_nat (n:bin) : nat :=
  match n with
    | zero => O
    | twice x => twice_nat (bin_to_nat x)
    | twice_plus_one x => S (twice_nat (bin_to_nat x))
end.

Fixpoint incr (n:bin) : bin :=
    match n with
      | zero => twice_plus_one zero
      | twice x => twice_plus_one x
      | twice_plus_one x => twice (incr x)
    end.

Example test_bin_incr1: (bin_to_nat(incr zero)) = (S O).
Proof.
reflexivity.
Qed.
