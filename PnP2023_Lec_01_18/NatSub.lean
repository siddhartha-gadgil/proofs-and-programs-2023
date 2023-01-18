import Mathlib

/-!
# Subtraction: example of intertwined proofs and definitions. 
-/

#eval 4 - 3

#eval 3 - 4

#check Nat.sub

/-!
First remedy: fail but with a warning.
-/

def Nat.sub! (m n: Nat) :=
match m, n with 
| m, 0 => m
| m + 1, n + 1 => Nat.sub! m n
| 0, _ + 1 => panic! "cannot subtract"

#eval Nat.sub! 4 3
-- #eval Nat.sub! 3 4

infix:64 "-!" => Nat.sub!

#eval 4 -! 3

def panicNat : ℕ  := panic! "I like to panic"

#check panicNat  
-- #eval panicNat

#check Empty

-- def badPanic : Empty :=
--   panic! "sometimes we are not even allowed to panic"

def defaultNat : ℕ := default

#eval defaultNat

-- def defaultEmpty : Empty := default

def default₁ : ℕ × ℕ := default

#eval default₁

/-!
* if `α` is a type `Inhabited α` is a type.
* `Inhabited` is called a *typeclass*.
* a term of type `Inhabited α` (called an *instance*) corresponds to a default.
* Lean *infers* instances from other instances.
-/

def default₂ : ℕ × String × (String → ℕ) :=
      default

#reduce default₂

def default₃ : ℕ × (String → ℕ) × 
  (Empty → Empty) := default

#reduce default₃

inductive MyEmpty where

instance (priority := high)(α : Type) : Inhabited (α → α) :=
    ⟨id⟩

def default₄  : ℕ × (String → ℕ) × 
  (ℕ → MyEmpty → MyEmpty) := default

#reduce default₄

def default₅ : ℕ × (String → ℕ) × 
  (Empty → Empty) := default

#reduce default₅

def default₆  : ℕ × (ℕ  → ℕ) × 
  (ℕ → MyEmpty → MyEmpty) := default

#reduce default₆

/-! Second rectification: `Option` 
* Given `α` a type `Option α` is a type
* Terms of type `Option α` are of two forms
   - `some x` where `x : α`
   - `none`
-/

def Nat.sub? : ℕ → ℕ → Option ℕ
| m, 0 => some m
| m + 1, n + 1 => Nat.sub? m n
| 0, _ + 1 => none

infix:64 "-?" => Nat.sub?

#eval 4 -? 3

#eval 3 -? 4

def Nat.doubleSub? (m n : ℕ) : Option ℕ :=
  (m -? n).map (·  * 2)

#eval Nat.doubleSub? 5 3

#eval Nat.doubleSub? 5 32

def Nat.tripleSub? (m n : ℕ) : Option ℕ := 
  do
    let d ← m -? n 
    return d * 3

#eval Nat.tripleSub? 5 3

def Nat.sub_sub? (a b c : ℕ) : Option ℕ :=
  do
    let d₁ ← a -? b
    let d₂ ← d₁ -? c
    return d₂ 