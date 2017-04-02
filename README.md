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

References:

* [Coq Modules](https://coq.inria.fr/tutorial/3-modules): Very useful for understanding.


