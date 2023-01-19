import Mathlib

/-!
# Subtraction: example of intertwined proofs and definitions. 

The difference of natural numbers is not a natural number. We see three ways of overcoming this problem, which illustrate various important concepts in Lean. 

The first two are in this module while the third is in a sequel. The first two are in fact available in functional programming langauges such as `scala` and `Haskell`. 

To begin with, we see how Lean deals with subtraction on `ℕ`.

```lean
#eval 4 - 3 -- 1

#eval 3 - 4 -- 0
```

The first example is as expected, but the second may be surprising. According to the documentation of Lean 4,  `Nat.sub` is:
> (Truncated) subtraction of natural numbers. Because natural numbers are not closed under subtraction, we define `m - n` to be 0 when `n < m`.

-/

#eval 4 - 3 -- 1

#eval 3 - 4 -- 0

#check Nat.sub

/-!
## Subtraction with panic

Our first remedy is to define subtraction as Lean does but with an error message when the result is incorrect. 

```lean
def Nat.sub! (m n: Nat) :=
match m, n with 
| m, 0 => m
| m + 1, n + 1 => Nat.sub! m n
| 0, _ + 1 => panic! "cannot subtract a larger number from a smaller one"

#eval Nat.sub! 4 3 -- 1
#eval Nat.sub! 3 4 -- 0 (but with an error message)
```
-/

/-- Subtraction of natural numbers; panics when difference is negative. -/
def Nat.sub! (m n: Nat) :=
match m, n with 
| m, 0 => m
| m + 1, n + 1 => Nat.sub! m n
| 0, _ + 1 => panic! "cannot subtract a larger number from a smaller one"

#eval Nat.sub! 4 3 -- 1
-- #eval Nat.sub! 3 4 -- 0

/-! 
A brief digression: Lean 4 lets us easily introduce new notation for our variant of subtraction. 

```lean
infix:64 "-!" => Nat.sub!
```
-/

/-- infix notation for subtraction with panic. -/
infix:64 "-!" => Nat.sub!

#eval 4 -! 3

/-!
## More on panicking

The intriguing fact about the illegal subtraction is that, while it gave an error, it still had a value. Indeed, we see more of the underlying phenomenon in the following examples. 

```lean
def panicNat : ℕ  := panic! "I like to panic"

#check panicNat  -- ℕ 
-- #eval panicNat -- 0 (with error)
```

Note that `panicNat` had a type, and the computation of the type did not give an error. Hence for logical consistency, the value of `panicNat` must be a term of type `ℕ`.

Indeed, if we try to make an analogous definition for `Empty` we get an error. 

```lean
def badPanic : Empty :=
  panic! "sometimes we are not even allowed to panic"
```
gives the error message:
```lean
failed to synthesize instance
  Inhabited Empty
```

Indeed the empty type has no inhabitants so allowing a definition of `badPanic` would be a contradiction.
-/

/-- A natural number obtained by panicking. -/
def panicNat : ℕ  := panic! "I like to panic"

#check panicNat  -- ℕ 
-- #eval panicNat -- 0 (with error)

#check Empty -- Type

-- def badPanic : Empty :=
--   panic! "sometimes we are not even allowed to panic"

/-!
## Default values and typeclasses

The value returned when panicing is the `default` value of the type. Not every type has a default value. For example, the `Empty` type has no default value. 

Default values can be _synthesized_ from other default values by so called _typeclass_ inference. First we see some examples of default values. 

```lean

-/

/-- The default value in `ℕ`. -/
def defaultNat : ℕ := default
/-!
```lean
#eval defaultNat -- 0
```

As we have seen earlier, the default value of `ℕ` is `0`. 
-/

#eval defaultNat -- 0


/-!
As we saw in the case of panic, the default value of `Empty` is not defined. The following gives an error message.

```lean
def defaultEmpty : Empty := default
```

-/
-- def defaultEmpty : Empty := default

/-- The default value in `ℕ × ℕ`. -/
def default₁ : ℕ × ℕ := default

/-!
A more interesting example is the default value of a product type. 

```lean
#eval default₁ -- (0, 0)
```

This is inferred from the default values of the components.
-/

#eval default₁ -- (0, 0)

/-!
### Typeclasses

We sketch the basic ideas of typeclasses and how they are used here. The `default` value of a type `α` is based on `Inhabited α`.

* if `α` is a type `Inhabited α` is a type.
* `Inhabited` is called a _typeclass_.
* a term of type `Inhabited α` (called an _instance_) corresponds to a default term of type `α`.
* Lean _infers_ instances from other instances.
-/

/-- The default value in `ℕ × String × (String → ℕ)`. -/
def default₂ : ℕ × String × (String → ℕ) :=
      default

#reduce default₂ -- (Nat.zero, "", fun x => Nat.zero)

/-- The default value in `ℕ × (String → ℕ) × (Empty → Empty)`. -/
def default₃ : ℕ × (String → ℕ) × 
  (Empty → Empty) := default

#reduce default₃ -- (Nat.zero, fun x => Nat.zero, fun a => False.rec (fun x => Empty) (_ : False))

/-!
Some more examples of typeclass inference. 

```lean
#reduce default₂ -- (Nat.zero, "", fun x => Nat.zero)

#reduce default₃ -- (Nat.zero, fun x => Nat.zero, fun a => False.rec (fun x => Empty) (_ : False))
```

In the first example, we see that default functions are inferred if the codomains are inhabited, with a constant function used as a default. 

Lean has inferred a default function from `Empty` to `Empty` by using the default function from `Empty` to `False`. To illustrate introducing new  defaults we introduce a new type `MyEmpty` which is also an empty type.
-/

/-- An empty type. -/
inductive MyEmpty where

/-- An instance of `Inhabited` corresponding to the identity function from any type to itself. -/
instance (priority := low)(α : Type) : Inhabited (α → α) :=
    ⟨id⟩

/-- The default value in `ℕ × (String → ℕ) × (ℕ → MyEmpty → MyEmpty)`. -/
def default₄  : ℕ × (String → ℕ) × 
  (ℕ → MyEmpty → MyEmpty) := default

/-!
We see this picked up in the following construction. Note that defining a default for `MyEmpty` gives an error. 


```lean
#reduce default₄ -- (Nat.zero, fun x => Nat.zero, fun x a => a)
```
-/

#reduce default₄ -- (Nat.zero, fun x => Nat.zero, fun x a => a)


/-- The default value in `ℕ × String (String → ℕ) × (Empty × Empty)` in the presence of the identity default instance. -/
def default₅ : ℕ × (String → ℕ) × 
  (Empty → Empty) := default

#reduce default₅ -- (Nat.zero, fun x => Nat.zero, fun a => a)

/-- The default value in `ℕ × String (ℕ → ℕ) × (MyEmpty × MyEmpty)` in the presence of the identity default instance. -/
def default₆  : ℕ × (ℕ  → ℕ) × 
  (ℕ → MyEmpty → MyEmpty) := default

#reduce default₆ -- (Nat.zero, fun x => Nat.zero, fun x a => a)

/-!
The following example shows the effect of priorities of instances. 

```lean
#reduce default₆ -- (Nat.zero, fun x => Nat.zero, fun x a => a)
```

Observe that the second component is the constant function `fun x => Nat.zero` and not the identity function `id`.
-/

/-! 
## Second rectification: `Option` 

The second choice is to essentially return values only when they are valid, by wrapping them in an `Option`. 

* Given `α` a type `Option α` is a type
* Terms of type `Option α` are of two forms
   - `some x` where `x : α`
   - `none`
-/

/-- Option valued subtraction of natural numbers -/
def Nat.sub? : ℕ → ℕ → Option ℕ
| m, 0 => some m
| m + 1, n + 1 => Nat.sub? m n
| 0, _ + 1 => none

infix:64 "-?" => Nat.sub?

/-!
Some examples of subtraction returning option types. 

```lean
#eval 4 -? 3 -- some 1

#eval 3 -? 4 -- none
```
-/

#eval 4 -? 3 -- some 1

#eval 3 -? 4 -- none

/-!
If we return option types we need to be able to handle them. We illustrate this by defining a function that returns the double of the difference if it is defined. 

```lean
def Nat.doubleSub? (m n : ℕ) : Option ℕ :=
  (m -? n).map (·  * 2)

#eval Nat.doubleSub? 5 3 -- some 4

#eval Nat.doubleSub? 5 32 -- none
```
-/

/-- Optionally return `(m - n) * 2` if `m ≥ n`. -/
def Nat.doubleSub? (m n : ℕ) : Option ℕ :=
  (m -? n).map (·  * 2)

#eval Nat.doubleSub? 5 3 -- some 4

#eval Nat.doubleSub? 5 32 -- none

/-!
A convenient way to handle option types is to use the `do` notation. 

```lean
def Nat.tripleSub? (m n : ℕ) : Option ℕ := 
  do
    let d ← m -? n 
    return d * 3

#eval Nat.tripleSub? 5 3 -- some 6
```
-/

/-- Optionally return `(m - n) * 3` if `m ≥ n`. -/
def Nat.tripleSub? (m n : ℕ) : Option ℕ := 
  do
    let d ← m -? n 
    return d * 3

#eval Nat.tripleSub? 5 3 -- some 6

/-- Optionally return `a - b - c` if this is non-negative. -/
def Nat.sub_sub? (a b c : ℕ) : Option ℕ :=
  do
    let d₁ ← a -? b
    let d₂ ← d₁ -? c
    return d₂ 

/-!
The `do` notation is even more convenient when we compose option valued functions. 

```lean
def Nat.sub_sub? (a b c : ℕ) : Option ℕ :=
  do
    let d₁ ← a -? b
    let d₂ ← d₁ -? c
    return d₂ 
```
-/