sf
--

Working [Software Foundations](https://www.cis.upenn.edu/~bcpierce/sf/current/index.html)

Proof General (Emacs plugin) tips:
-----------------------------------

* C-c C-RET
* C-c C-p   : for displaying goals
* C-c C-l   : Refreshes goals
* C-c C-a C-a : Run SearchAbout
* C-c C-;     : Paste SearchAbout response into buffer
* C-/         : Go to the proof end (Very handy!)

Useful functions:
* coq-Print : View the definition of particular function

Notes:
-------

Things which aren't in the book and learned from seeing other's code.

1. You can `rewrite` like this:

``` coq
rewrite <- plus_comm with (n := n' * m) (m := m + m) at 1.
```

See different [styles here](https://www.reddit.com/r/Coq/comments/3be6qg/rewrite_problem/cslc2xj/).

2. [Admmitting asserts](http://stackoverflow.com/questions/42791453/coq-admit-assert)

3. [Symmetry tactic for exchanging LHS and RHS](https://coq.inria.fr/faq)

## apply tactic

### Example 1

``` coq
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
```

Current goals:

``` coq
  H : ....
  ============================
   S n = S m'
```

``` coq
apply f_equal.
```

Current goals:

``` coq
  H : ....
  ============================
   n = m'
```

### Example 2

``` coq
  n' : nat
  IHn' : forall m : nat, n' + n' = m + m -> n' = m
  m' : nat
  H1 : n' + n' = m' + m'
  ============================
   S n' = S m'
```

``` coq
apply IHn' with (m := m') in H1.
```

``` coq
  n' : nat
  IHn' : forall m : nat, n' + n' = m + m -> n' = m
  m' : nat
  H1 : n' = m
  ============================
   S n' = S m'
```

## destruct tactic

### Example 1

``` coq
H : P \/ Q
=============
S n' = S m'
```

``` coq
destruct H as [H1 | H2].
```

``` coq
H1 : P
========
S n' = S m'
```

### Example 2

``` coq
  H2 : exists x : A, f x = y /\ In x l'
  ============================
   exists x : A, f x = y /\ (x' = x \/ In x l')
```

``` coq
destruct H2
```

``` coq
  x : A
  H : f x = y /\ In x l'
  ============================
   exists x0 : A, f x0 = y /\ (x' = x0 \/ In x0 l')
```

### Example 3

``` coq
  H : f x = y /\ In x l
  ============================
   In y (map f l)
```

``` coq
destruct H as [H1 H2].
```

``` coq
  H1 : f x = y
  H2 : In x l
  ============================
   In y (map f l)
```

References:

* [Coq Modules](https://coq.inria.fr/tutorial/3-modules): Very useful for understanding.


