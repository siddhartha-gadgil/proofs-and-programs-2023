import Mathlib
import LeanAide

/-!
## A bit of AI

We use `leanaide` for a bit of AI. For more direct use (such as debugging), can use

```lean
#eval translateViewM "There are infinitely many odd numbers"
```
-/


/- There are infinitely many odd numbers -/
example : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := by
  intro n
  use 2 * n + 1
  apply And.intro
  · linarith 
  · simp [Nat.add_mod]
