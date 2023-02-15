import Mathlib

/-!
# Propositions as Types

* We can represent propositions as types, or interpret (slightly restricted) types as propositions. 
* A proof of a proposition is a term of the corresponding type.
* Defining and proving are essentially the same thing.
* The same foundational rules let us construct propostions and proofs as well as terms and types.
-/

/-!
## Main correspondence

* `A → B` is functions from `A` to `B` as well as `A` implies `B`.
* Function application is the same as *modus ponens*.
* So if we have propositions `A` and `B`, we can construct a proposition `A → B` corresponding to implication.
-/

universe u

def functionApplication {A B : Type u} (f : A → B) (a : A) : B := f a

def modus_ponens {A B : Prop} (h₁ : A → B) (h₂ : A) : B := h₁ h₂

/-!
## Other Combination

* `A ∧ B` is the conjunction of `A` and `B`.
* `A ∨ B` is the disjunction of `A` and `B`.
* `¬ A` is the negation of `A`.

All these can be constructed by our rules.


-/

#check And
#check Prod

/-!
## Conjuction and Product

```lean
structure And (a b : Prop) : Prop where
  /-- `And.intro : a → b → a ∧ b` is the constructor for the And operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`. -/
  right : b
```

This is the same as the product type:

```lean
structure Prod (α : Type u) (β : Type v) where
  /-- The first projection out of a pair. if `p : α × β` then `p.1 : α`. -/
  fst : α
  /-- The second projection out of a pair. if `p : α × β` then `p.2 : β`. -/
  snd : β
```
-/

inductive MyOr (A B : Prop) : Prop
| inl : A → MyOr A B
| inr : B → MyOr A B

#check Or
#check Sum

/-!
# Disjunction and Sum

```lean
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b
```

This is the same as the sum type:

```lean
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β
```
-/

#check True
#check False

/-!
## True and False

These are analogues of `Unit` and `Empty`:

```lean
inductive True : Prop where
  /-- `True` is true, and `True.intro` (or more commonly, `trivial`)
  is the proof. -/
  | intro : True

inductive False : Prop
```
-/

/-!
## Negation

The negation of a type (or proposition) `A` is `¬ A`, which is the type (or proposition) `A → False`.

-/

theorem everything_implies_true (A : Prop) : A → True := fun _ => True.intro

theorem false_implies_everything (A : Prop) : False → A := fun h => nomatch h

#check False.rec -- False.rec.{u} (motive : False → Sort u) (t : False) : motive t

#check False.rec (motive := fun _ => 1 = 2) -- False → 1 = 2

example {A B : Prop}: A → B → A :=
  fun a _ ↦ a

#check Iff

/-!
## If and only if

```lean
structure Iff (a b : Prop) : Prop where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a
```
-/

example {A B : Prop}: (A ↔  B) =
      ((A → B) ∧ (B → A)) := by
  apply propext
  apply Iff.intro
  case a.mp => 
    intro h
    apply And.intro
    · exact h.mp
    · exact h.mpr
  case a.mpr => 
    intro h
    apply Iff.intro
    · exact h.left
    · exact h.right

/-!
## Universal Quantifiers

* A proposition associated to each term of a type `A` is a function `A → Prop`.
* The propostion `∀ x : A, P x` is the proposition that `P x` is true for all `x : A`, which is the dependent function type
`(x: A) → P x`.

-/


#check Exists

/-!
## Existential Quantifiers

```lean
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  /-- Existential introduction. If `a : α` and `h : p a`,
  then `⟨a, h⟩` is a proof that `∃ x : α, p x`. -/
  | intro (w : α) (h : p w) : Exists p
```
-/

#check Nat.le
#check Eq

/-! 
## Basic types

We have seen `≤` can be constructed as indexed inductive type:

```lean
inductive Nat.le (n : Nat) : Nat → Prop
  /-- Less-equal is reflexive: `n ≤ n` -/
  | refl     : Nat.le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m} : Nat.le n m → Nat.le n (succ m)
```

The equality type is also indexed inductive type:

```lean
inductive Eq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : Eq a a
```
-/

example {α β : Type}{f g : α → β} (x y : α ): 
  f = g → x = y → f x = g y := by
  intro hfg hxy
  match f, g, hfg, x, y, hxy with
  | f, .(f), rfl, x, .(x), rfl => rfl