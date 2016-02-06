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

Definition singleton (n : nat) : natlist :=
  n :: nil.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | x::xs, y::ys => (x::singleton y ++ alternate xs ys)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  length (listFilter s (fun n => beq_nat n v)).

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
(singleton v) ++ s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
match (count v s) with
  | O => false
  | _ => true
end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
    | nil => nil
    | (x::xs) => match (beq_nat x v) with
                   | true => xs
                   | false => (x::remove_one v xs)
                 end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  listFilter s (fun n => negb (beq_nat v n)).

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | nil => true
    | (x::xs) => match (beq_nat (count x s2) 0) with
                   | true => false
                   | false => subset xs (remove_one x s2)
                 end
  end.
                         
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem same_equal: forall (n: nat),
  beq_nat n n = true.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem bag_theorem: forall n: nat, forall b: bag,
  blt_nat O (count n (add n b)) = true.
Proof.
  intros n b.
  destruct n as [| n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    assert (H1: beq_nat n' n' = true).
      rewrite -> same_equal.
      reflexivity.
    rewrite -> H1.
    simpl.
    reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.

Check pred.
Example pred_one: (pred 3 = 2).
Proof.
  simpl.
  reflexivity.
Qed.

Example pred_two: (pred 0 = 0).
Proof.
  simpl.
  reflexivity.
Qed.
  
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = const n l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
    | nil => [v]
    | (cons n l') => n :: (snoc l' v)
  end.

Example snoc_eg1: (snoc (1::2::3::nil)  4= [1;2;3;4]).
Proof.
  reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist := 
  match l with
    | nil => nil
    | (h :: t) => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof.
  reflexivity.
Qed.
  
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = cons n l'".
    simpl.
    rewrite <- IHl'.
Abort.

Lemma length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l.
  induction l as [| n' l'].
  Case "n = nil".
    reflexivity.
  Case "n = cons n' l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl.
    rewrite -> length_snoc.
    rewrite -> IHl'.
    reflexivity.
Qed.

(* rev_length: forall l : natlist, length (rev l) = length l *)
(* test_rev2: rev [] = [] *)
(* test_rev1: rev [1; 2; 3] = [3; 2; 1] *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Lemma rev_helper : forall l : natlist, forall n: nat,
    rev (snoc l n) = n :: rev l.
Proof.
  intros l n.
  induction l as [| l' n'].
  Case "l = nil".
    reflexivity.
  Case "l = cons l' n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    simpl.
    rewrite -> rev_helper.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  induction l1 as [| n l1'].
  Case "l1 = nil".
    simpl.
    reflexivity.
  Case "l1 = cons n l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.


Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [|n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Lemma distr_snoc_helper : forall l1 l2:natlist, forall n:nat,
  snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
  intros l1 l2 n.
  induction l1 as [| n' l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n' l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  Case "l1 = nil".
    simpl.
    rewrite -> app_nil_end.
    reflexivity.
  Case "l1 = cons n l1'".
    simpl.
    rewrite -> IHl1'.
    rewrite -> distr_snoc_helper.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
Abort.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1,l2 with
    | nil, nil => true
    | _, nil => false
    | nil, _ => false
    | (x::xs), (y::ys) => if (beq_nat x y)
                          then beq_natlist xs ys
                          else false
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.



      


    

