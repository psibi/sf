Require Export NatList.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 3 (cons nat 3 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons x xs => S (length X xs)
  end.



