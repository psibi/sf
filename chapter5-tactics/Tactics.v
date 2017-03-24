Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p.
  intros eq1.
  intros eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m.
  intros eq1.
  intros eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1.
  intros H2.
  apply H1.
  apply H2.
Qed.

Lemma rev_empty : forall (X : Type) (l : list X),
    l = [] -> rev l = [].
Proof.
  intros X l.
  intros H.
  rewrite -> H.
  simpl. reflexivity.
Qed.

Check nil.


Lemma rev_injective : forall (X : Type) (l1 l2 : list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2.
  intros H.
  induction l1 as [| n l1' IHl1'].
  - simpl. admit.
  - 




(* Theorem rev_exercise1 : forall (l l' : list nat), *)
(*      l = rev l' -> *)
(*      l' = rev l. *)
(* Proof. *)
(* .  intros l l'. *)
(*   intros H1. *)
(*   induction l as [| x l'' IHl']. *)
(*   - simpl. *)
    


(*   - rewrite -> H1. symmetry. apply rev_involutive. *)
(* Abort. *)

  

