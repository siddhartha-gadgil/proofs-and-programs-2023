import Mathlib
/-!
## Foundations

We have seen all the ingredients of the foundations of mathematics as implemented in Lean. Our goal now is to:

* Systematically review them.
* Put them in the context of what we mean by foundations of mathematics.
* Separate the foundations from the syntax parsing and elaboration which help us work efficiently with Lean.

### Foundations of foundations

The starting assumption is that we are in agreement with the meaning of syntax, including pattern matching and substitution. For example, we can understand the following definition is valid in Lean, assuming we know what `ℕ` means:

```lean
def cube : ℕ → ℕ := fun n → n * n * n
```

and that we can deduce from the above that `cube 3 = 3 * 3 * 3`.

We have __rules__ for foundations based on syntax. We also assume that the rules can be checked _mechanically_, i.e., by a computer program, and we are convinced that some such program is correct. For a flexible syntax, this is a non-trivial task. So we may want to restrict to a simpler syntax (as we will when we consider _classical foundations_).

We have to also check that we correctly represent the corresponding "real world" concept.


### Context, Rules, Terms

We assume that at any point we have a __Context__. In Lean this means that we have terms that we can refer to by name, and that these terms have a type, though this may be an _expression_.

In any context, we have __Rules__ to 

* form _expressions_ from _terms_ and _expressions_, with a well-formed expression representing a term.
* make two kinds of __judgments__:
  * `e : t` means that `e` is an expression of type `t`.
  * `e = e'` means that `e` and `e'` are equal expressions.

### Generative grammars

Expressions and Rules are based on a _generative_ grammar. Thus, we do not specify whether an expression or judgement is valid or not. Instead, we specify how we can make well-formed expressions and valid judgements.

### Local Contexts

In addition to the names in the context, we can have some names that are only valid in a particular expression. These are called __local variables__.

### Initial Context

Even an empty Lean file does not have an empty context. Instead the context has [Foundational Types](https://math.iisc.ac.in/~gadgil/proofs-and-programs-2023/doc/foundational_types.html).

### Axioms

We can add axioms to the context. This means that we introduce a term and give an expression for its type. This should be done with care so that the context does not become inconsistent.

### Rules for Lean

The rules for Lean let us introduce expressions and at the same time make judgements about them.

* Function types
* Function application
* Function definitions by λ-abstraction.
* Π-types
* Dependent function definition and application
* Inductive types
* Indexed inductive types

### Propositions as Types

Remarkably, the same set of rules let us encode both objects of mathematics and statements about them. The statements (called __propositions__) are encoded as types with a proof of the proposition being a term of that type. 

Logical connectives are encoded as _function types_, _Π-types_, and _inductive types_. The rules for deduction follow from the rules for Lean.

In Lean, there is an additional rule for a proposition `α : Prop`, namely if `p : α` and `q : α` then `p = q`. 
-/

-- already in the context
#check ℕ -- ℕ : Type
#check Nat.succ -- Nat.succ : ℕ → ℕ

/-!
We use various rules:
* Given types `α` and `β`, we can form the type of functions from `α` to `β`, written `α → β`.
* We can form a function application `f x` from a function `f` and an argument `x`.
* We can form a function definition `fun x ↦ e` from a variable `x` and an expression `e`, where `e` is defined in the local context with the additional expression `x`.
* When defining a function using `x ↦ e`, we also introduce a rule that the function applied to `a` is the result of substituting `a` for `x` in `e`.
* In the definition below, types should match.
* Often Lean can infer some of the types.
-/

/-- Adding `2` to a natural number.
-/
def addTwo -- adding a term named `add_two` 
    : ℕ → ℕ -- specified the type
      := -- specified the value 
        fun (n : ℕ) ↦ -- started a λ-expression
            -- now `n : ℕ` is in the local context
            Nat.succ -- applying the function `Nat.succ` (from the context)
              (Nat.succ -- again, applying the function  `Nat.succ`
                -- `n` is in the local context
                n) -- the body of the function

/-! 
A `theorem` is just like a definition, except

* The type must be a proposition, i.e. the type of the type must be `Prop`.
* The type must be fully inferred from the left-hand side.
* The value is then a proof of the proposition.
-/

/-- one plus two is three -/
theorem one_addTwo : addTwo 1 = 3 := rfl

-- the lhs does involve some type inference
set_option pp.all true in
#reduce 1 = 3 -- @Eq.{1} Nat 1 3

/-!

## Π-types

These can be viewed as:

* products of a family of types indexed by a type.
* a type corresponding to functions whose codomain _depends_ on the argument.
* these are sections of a bundle.

We consider an example
-/

def NatTuple: ℕ → Type
| 0 => Unit
| n + 1 => ℕ × (NatTuple n) 

/-! 
We define a dependent function associating to a natural number `n` the tuple of `n` natural numbers `(n, n-1, ..., 0)`.

* this has type `(n: ℕ) → NatTuple (n + 1)`.
-/

def descending : (n: ℕ) → NatTuple (n + 1) -- := fun n ↦
-- match n with
| 0 => (0, ())
| n + 1 => (n + 1, descending n)

#eval descending 3 -- (3, 2, 1, 0, ())

#check descending 3 -- NatTuple (3 + 1)

#eval descending 13 -- (13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, ())
#check descending 13 -- NatTuple (13 + 1)


#check () -- Unit

#check (() : NatTuple 0) -- Unit 
