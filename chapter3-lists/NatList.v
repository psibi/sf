Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 4).

Definition fst (p: natprod) :=
  match p with
      | pair x y => x
  end.

Definition snd (p: natprod) :=
  match p with
      | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).

(* Note the spacings! *)
Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).
Eval compute in (snd (3,5)).

