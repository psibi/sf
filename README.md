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

Notes:
-------

Things which aren't in the book and learned from seeing other's code.

1. You can `rewrite` like this:

``` coq
rewrite <- plus_comm with (n := n' * m) (m := m + m).
```

2. [Admmitting asserts](http://stackoverflow.com/questions/42791453/coq-admit-assert)

References:

* [Coq Modules](https://coq.inria.fr/tutorial/3-modules): Very useful for understanding.
