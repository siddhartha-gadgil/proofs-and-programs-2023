import Mathlib
import LeanAide

/-!
## A bit of AI

We use `leanaide` for a bit of AI. For more direct use (such as debugging), can use

```lean
#eval translateViewM "There are infinitely many odd numbers"
```

For more details on using the AI, please see the [README](https://github.com/siddhartha-gadgil/LeanAide#readme) of the LeanAide project.

We also complete the proof as an example.
-/


/- There are infinitely many odd numbers -/
example : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := by
  intro n -- introduce a variable n
  use 2 * n + 1 -- use `m = 2 * n + 1`
  apply And.intro -- apply the constructor of `∧` to split goals
  · linarith -- solve the first goal using `linarith` 
  · simp [Nat.add_mod] -- solve the second goal using `simp` with the lemma `Nat.add_mod`
