Require Import Basics.

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
  

