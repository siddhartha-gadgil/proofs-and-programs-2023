---
title: "Overview"
date: 2022-12-04T08:51:53+05:30
draft: true
---

Here we sketch the __what__, the __why__, the __how__, and the __why now__ of this course.

<!--more-->
#### What?

Broadly, our goals are the following

* Using programs (_interactive theorem provers_) to
    * verify proofs of results
    * help in generating proofs
* Proving correctness of programs; including writing the programs whose correctness we prove.
* Writing programs to find and/or verify proofs

##### What do these mean?

To make sense of the above, we need to understand:

* What is a _proof_.
* What is a _program_.

Such questions form the _foundations_ of _mathematics_ and of _computation_. There are different foundational systems, and we will look at two classes of these:

* Classical foundations:
  - _First-order logic:_ the usual foundations of mathematics are _Set Theory_ as a theory in first-order logic.
  - _λ-calculus:_ one of the equivalent formulations of the usual foundations of computation.
* _Dependent Type Theory_ (DTT): foundations used by Lean that include both proofs and computations in a unified way.

In practice classical foundations are only useful _in the small_, i.e., for deductions using a relatively small set of axioms. Indeed real-life mathematics is rigorous in only a _local_ or _domain specific_ fashion -- we check that, for instance, calculations involving polynomials are correct in terms of rules and definitions for these, not in terms of polynomials represented in Set Theory.

On the other hand, the foundations building on _Dependent Type theory_ can resemble real-world mathematics as well as form the basis for a real-world programming language.

##### What do theorem proving programs do?

Theorem proving programs vary in the _generality_ in which they work, how _autonomous_ they are and the _complexity and scale_ they can handle.

#### Why?

A large part of this course is about _formalized mathematics_, i.e., mathematics that can be understood and verified by computers. Formalization can also be done in other domains: software, hardware design, networking protocols, encryption schemes, even tax codes. An article by [Patrick Massot](https://www.imo.universite-paris-saclay.fr/~patrick.massot/files/exposition/why_formalize.pdf) gives a beautiful account of the motivation for formalization of mathematics.

Computer verification of proofs in mathematics is intended to replace _human verification_, while in other domains it replaces _testing_. So the reasons for formalizing overlap in some ways but are different in other respects.

#### Correctness