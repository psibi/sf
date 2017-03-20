Require Export NatList.

Check (pair 3 4).

Inductive list (X: Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check nil nat.

Check cons.

Check cons nat.
Check cons nat 3.
Check cons nat 3 (nil nat).


Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.


Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Check d.
Check d nat.
Check e.
Check e nat.

(* d (b a 5 ) is invalid *) 

Check d nat (b a 5).

Check d mumble (b a 5).

Check d bool (b a 5).

Check e bool true.

Check e mumble (b c 0).

(* Check e bool (b c 0). is not valid *)

End MumbleGrumble.










