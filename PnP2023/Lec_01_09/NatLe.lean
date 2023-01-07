import Mathlib
/-!
# Examples of Proofs

We see our next proofs, most of which involve the `≤` relation on natural numbers. 

We will see that the natural numbers are "defined" in terms of the `zero` and `succ` constructors.

* `Nat.zero : ℕ` 
* `Nat.succ : ℕ → ℕ`

Analogous to this, (modulo renaming) the `≤` relation is defined in terms of the `le_refl` and `le_step` constructors.

* `Nat.le : ℕ → ℕ → Prop`
* `Nat.le_refl : ∀ n : ℕ, n ≤ n`
* `Nat.le_step : ∀ {n m : ℕ}, n ≤ m → n ≤ Nat.succ m`
-/


#check Nat.zero
#check Nat.succ

#check Nat.le
#check Nat.le_step
#check Nat.le_refl

