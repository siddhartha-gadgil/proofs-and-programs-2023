---
title: "Overview"
date: 2023-01-04T08:51:53+05:30
draft: false
marp: true
math: katex
theme: gaia
---

### About the course

Here we sketch the __what__, the __why__, the __how__, and the __why now__ of this course.

<!--more-->
--- 
#### What?

Broadly, our goals are the following

* Using programs (_interactive theorem provers_) to
    * verify proofs of results,
    * help in generating proofs.
* Proving correctness of programs;
    - including writing the programs whose correctness we prove.
* Writing programs to find and/or verify proofs.

---

##### What do these mean?

To make sense of the above, we need to understand:

* What is a _proof_?
* What is a _program_?

Such questions form the __foundations__ of _mathematics_ and of _computation_. 

--- 

There are different foundational systems, and we will look at two classes of these:

* Classical foundations:
  - _First-order logic (FOL):_ the usual foundations of mathematics are _Set Theory_ as a theory in First-order logic.
  - _λ-calculus:_ one of the equivalent formulations of the usual foundations of computation.
* _Dependent Type Theory_ (DTT): foundations used by Lean that include both proofs and computations in a unified way.

---

In practice classical foundations are only useful _in the small_, i.e., for deductions using a relatively small set of axioms. 

Indeed real-life mathematics is rigorous in only a _local_ or _domain specific_ fashion -- we check that, for instance, calculations involving polynomials are correct in terms of rules and definitions for these, not in terms of polynomials represented in Set Theory.

On the other hand, the foundations building on _Dependent Type theory_ can resemble real-world mathematics as well as form the basis for a real-world programming language.

--- 

##### What do theorem proving programs do?

Theorem proving programs vary in:

* the _generality_ in which they work, 
* how _autonomous_ they are, and 
* the _complexity and scale_ they can handle.

They can be used for:

* __Automation__
* __Formalization:__ _more_ effort than a human proof.
* __Tooling:__ helping find (possibly human) proofs.

---

* Software like Mathematica, SAGE, GAP handle specific mathematical problems with specific algorithms.
* General problems, but _in the small_, can be solved by
    - SAT/SMT solvers for finite or special classes of infinite problems.
    - FOL solvers such as _Resolution Theorem Provers_ for general problems.
* _Interactive theorem provers_ (ITPs) are used for general problems and _in the large_, but are typically not fully autonomous.
* __AI/ML__ systems can be used to help with automation and can handle _natural language_, but are still not mature.
---

#### Why?

* It is obvious why we would want tooling or automation for mathematics.
* Since formalization takes work, it must be worth it.
* Formalization can also be done in other domains: software, hardware design, networking protocols, encryption schemes, even tax codes. 
* An [article](https://www.imo.universite-paris-saclay.fr/~patrick.massot/files/exposition/why_formalize.pdf) by Patrick Massot gives a beautiful account of the motivation for formalization of mathematics.

---

Formalization of mathematics can:

* Give a super-human level of guarantee of __correctness__.
* Allow __abstraction__ and __modularity__ when working with mathematics.
* Facilitate __automation__, both algorithmic and AI/ML based.
* Allow __tooling__ for mathematics, such as _semantic search_.
* Facilitate collaboration.
* Facilitate using mathematics correctly in other domains (of mathematics). 
---

##### Correctness

* We obviously want to ensure high levels of correctness in all domains, i.e., with __fewer__ and __less serious__ errors.
* This has to be balanced against the extra effort required.
* In software, we use _testing_ to minimize errors.
* In mathematics, we use _refereeing_ and other human checks.
* Both these keep errors from spiralling out of control.
* However, serious and unfixable errors are not uncommon.

* In particular many papers in the _Annals of Mathematics_ have unfixable errors.
---
* In the case of software, hardware, etc there are situations where it is worth taking a lot of effort to avoid (serious) errors.
    - in safety-critical systems,
    - in systems where a mistake is expensive to fix, such as chips,
    - in _systems software_, where a bug is a _vulnerability_.
* As mathematics 
  - builds on other mathematics, and
  - correctness is a defining property, 

it is arguably worth applying at least the same standards as systems software.

---

#### How?

* We use Lean 4, which is a _programming language_ and an _interactive theorem prover_.
* We will formalize mathematics, implement programs for mathematical computation, and prove their correctness.
* We will implement and formalize in Lean 4:
    - a SAT solver (and maybe more)
    - first-order logic
    - λ-calculus 
* We will see glimpses of AI/ML, including using tools under development.

---
#### Why now?

* Mature but still growing areas are:
    - Experimental and Computational Mathematics,
    - SAT/SMT solvers and their use in Mathematics.
* There is explosive growth in Lean and its mathematical library.
* There is even more explosive growth in AI/ML.
* There is great potential in 
    - interactive theorem proving
    - interaction with AI/ML
    - mathematical proofs of programs.
