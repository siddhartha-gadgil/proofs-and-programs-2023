import Mathlib
import LeanAide

/- There are infinitely many odd numbers -/
example : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := by sorry

/- Every prime number is either `2` or odd -/
example : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], p = 2 ∨ p % 2 = 1 := by sorry