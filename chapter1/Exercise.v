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
