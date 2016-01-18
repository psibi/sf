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

Definition fst' (p: natprod) :=
  match p with
    | (x,y) => x
  end.

Definition snd' (p:natprod) :=
  match p with
    | (x,y) => y
  end.

Definition swap_pair (p: natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros n m.
  simpl.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p.
  simpl.
  reflexivity.
Qed.
      

