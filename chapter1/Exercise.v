Require Import Basics.

(* Check that below three functions are working. *)
(* If they don't work, run build.sh *)
Check test.
Check true || true.
Check Basics.test.

(* The function should return true if either or both of its inputs are false. *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match (b1, b2) with
  | (false, false) => true
  | (false, _) => true
  | (_, false) => true
  | _ => false
  end.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* This function should return true when all of its inputs are true, and false otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := andb (andb b1 b2) b3.

(* This doesn't work unless symbols are defined in that module. Why ? *)
(* Definition andb3_symbol (b1:bool) (b2:bool) (b3:bool) : bool := b1 && b2 && b3. *)

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check negb.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S p => mult n (factorial p)
  end.

Compute (factorial 5).
                               
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

(* The blt_nat function tests natural numbers for less-than, yielding a boolean. *)

Fixpoint blt_nat_rec (n m : nat) : bool := 
  match (n,m) with
    | (O,O) => false
    | (O, (S _)) => true
    | ((S _), O) => false
    | ((S n'), (S m')) => blt_nat_rec n' m'
  end.

Check test.

Definition blt_nat (n m : nat) : bool := 
  match (n,m) with
    | (O,O) => false
    | _ => if (beq_nat n m)
           then false
           else leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  reflexivity.
  rewrite <- H.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H1 b.
  rewrite -> H1.
  rewrite -> H1.
  reflexivity.
Qed.

Lemma andb_true_l : forall (b : bool), (true && b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  rewrite -> andb_true_l.
  destruct c.
  reflexivity.
  simpl. simpl. intros H1. rewrite -> H1. reflexivity.
  destruct c.
  simpl. intros H1. rewrite -> H1. reflexivity.
  simpl. reflexivity.
Qed.
    


    


