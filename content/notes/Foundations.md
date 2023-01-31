---
title: "Foundations"
date: 2023-01-31T09:23:40+05:30
marp: true
math: katex
theme: gaia
---

# Foundations

We have seen all the ingredients of the foundations of mathematics as implemented in Lean. Our goal now is to:

* Systematically review them.
* Put them in the context of what we mean by foundations of mathematics.
* Separate the foundations from the syntax parsing and elaboration which help us work efficiently with Lean.

---

## Foundations of foundations

The starting assumption is that we are in agreement with the meaning of syntax, including pattern matching and substitution. For example, we can understand the following definition is valid in Lean, assuming we know what `ℕ` means:

```lean
def cube : ℕ → ℕ := fun n → n * n * n
```

and that we can deduce from the above that `cube 3 = 3 * 3 * 3`.

---

We have __rules__ for foundations based on syntax. We also assume that the rules can be checked _mechanically_, i.e., by a computer program, and we are convinced that some such program is correct. For a flexible syntax, this is a non-trivial task. So we may want to restrict to a simpler syntax (as we will when we consider _classical foundations_).

---

## Context, Rules, Terms

We assume that at any point we have a __Context__. In Lean this means that we have terms that we can refer to by name, and that these terms have a type, though this may be an _expression_.

In any context, we have __Rules__ to 

* form _expressions_ from _terms_ and _expressions_, with a well-formed expression representing a term.
* make two kinds of __judgments__:
  * `e : t` means that `e` is an expression of type `t`.
  * `e = e'` means that `e` and `e'` are equal expressions.

---

## Generative grammars

Expressions and Rules are based on a _generative_ grammar. Thus, we do not specify whether an expression or judgement is valid or not. Instead, we specify how we can make well-formed expressions and valid judgements.

### Local Contexts

In addition to the names in the context, we can have some names that are only valid in a particular expression. These are called __local variables__.

---

## Initial Context

Even an empty Lean file does not have an empty context. Instead the context has [Foundational Types](http://math.iisc.ac.in/~gadgil/proofs-and-programs-2023/doc/foundational_types.html).

## Axioms

We can add axioms to the context. This means that we introduce a term and give an expression for its type. This should be done with care so that the context does not become inconsistent.

--- 

## Rules for Lean

The rules for Lean let us introduce expressions and at the same time make judgements about them.

* Function types
* Function application
* Function definitions by λ-abstraction.
* Π-types
* Dependent function definition and application
* Inductive types
* Indexed inductive types

---

## Propositions as Types

Remarkably, the same set of rules let us encode both objects of mathematics and statements about them. The statements (called __propositions__) are encoded as types with a proof of the proposition being a term of that type. 

Logical connectives are encoded as _function types_, _Π-types_, and _inductive types_. The rules for deduction follow from the rules for Lean.

