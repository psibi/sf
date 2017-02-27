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
    | _ => leb n m
  end.


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

  

