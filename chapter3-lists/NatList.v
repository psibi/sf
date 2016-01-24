
Require Export Induction.
Require Export Basics.

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

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p.
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist := 
  match count with
    | O => nil
    | (S n') => cons n (repeat n n')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
    | [] => O
    | x :: xs => 1 + length xs
  end.

Check (length mylist).
Eval compute in (length mylist).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
      | nil => l2
      | x :: xs => x :: (app xs l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
              
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
    | nil => default
    | (x :: xs) => x
  end.

Definition tl (l:natlist) : natlist :=
  match l with
    | nil => nil
    | (x::xs) => xs
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint listFilter (l:natlist) (fn: nat -> bool) : natlist :=
  match l with
    | nil => nil
    | (x::xs) => match (fn x) with
                   | true => (x::(listFilter xs fn))
                   | false => listFilter xs fn
                 end
  end.
                      

Definition checkZero (x : nat) : bool :=
  match x with
    | O => false
    | S n => true
  end.

Fixpoint nonzeros (l:natlist) : natlist :=
  listFilter l checkZero.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  listFilter l (fun n => oddb n).

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

               

