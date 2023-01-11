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

/-!
The first proof we see is of `3 ≤  3`. This is a direct application of `Nat.le_refl`. This is analogous to applying `Nat.le_refl` as a function to the argument `3`.

```lean
theorem three_le_three : 3 ≤ 3 :=
  Nat.le_refl 3
```

Our second result is similar and has a similar proof. 
However in the proof we did not specify the argument `4`
and instead used the *placeholder* `_`. Lean deduced that 
the unique way to get types correct is to fill in `4`.

```lean
/-- The result `4 ≤ 4`. -/
def four_le_four : 4 ≤ 4 :=
  Nat.le_refl _
```
-/

/-- The result `3 ≤ 3`. -/
theorem three_le_three : 3 ≤ 3 :=
  Nat.le_refl 3

/-- The result `4 ≤ 4`. -/
def four_le_four : 4 ≤ 4 :=
  Nat.le_refl _

#eval Nat.succ 0

-- #eval succ 0

open Nat in
#eval succ 0

#check le_refl

/-!
Some more complex proofs. In the first case the proof is given fully while in the second we allow a parameter to be inferred

```lean
theorem three_le_five : 3 ≤ 5 :=
  Nat.le_step (Nat.le_step (Nat.le_refl 3))

theorem three_le_six : 3 ≤ 6 :=
  Nat.le_step (
    Nat.le_step 
     (Nat.le_step (Nat.le_refl _))) 
```
-/

theorem three_le_five : 3 ≤ 5 :=
  Nat.le_step (Nat.le_step (Nat.le_refl 3))

theorem three_le_six : 3 ≤ 6 :=
  Nat.le_step (
    Nat.le_step 
     (Nat.le_step (Nat.le_refl _))) 

/-!
In the next proof we use tactics, specifically the `apply`
tactic. We also see a case where it fails.

```lean
theorem four_le_seven : 4 ≤ 7 := by
  apply Nat.le_step
  -- apply Nat.le_refl 
  /-tactic 'apply' failed, failed to unify
  ?n ≤ ?n
    with
  4 ≤ 6-/ 
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl
```

-/


theorem four_le_seven : 4 ≤ 7 := by
  apply Nat.le_step
  -- apply Nat.le_refl 
  /-tactic 'apply' failed, failed to unify
  ?n ≤ ?n
    with
  4 ≤ 6-/ 
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

/-!
Note that the proofs produced by tactics are proofs in the usual sense.

```lean
#print four_le_seven /- theorem four_le_seven : 4 ≤ 7 :=
 Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 4))) -/
```
-/

#print four_le_seven -- theorem four_le_seven : 4 ≤ 7 :=
-- Nat.le_step (Nat.le_step (Nat.le_step (Nat.le_refl 4)))

/-!
Lean has many powerful tactics. The `decide` tactic can prove propositions that (are true and) can be decided by
an algorithm corresponding to the `Decidable` typeclass (which we see later).

```lean
theorem four_le_ten : 4 ≤ 10 :=
  by decide
```

The proof produced by the `decide` tacic is similar to the above proofs.
```lean
def four_le_ten' : 4 ≤ 10 :=
  by decide


#reduce four_le_ten' /- Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl)))))
-/
```
-/

theorem four_le_ten : 4 ≤ 10 :=
  by decide

def four_le_ten' : 4 ≤ 10 :=
  by decide


#reduce four_le_ten' /- Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl)))))
-/

/-!
We can combine tactics. `repeat` applies a tactic as long as it is valid; `first` applies the first applicable tactic.

```lean
example : 4 ≤ 10 :=
  by
    -- repeat (apply Nat.le_step) -- goal: 4 ≤ 0
    repeat (first | 
          apply Nat.le_refl | 
          apply Nat.le_step)
    done
```
-/
example : 4 ≤ 10 :=
  by
    -- repeat (apply Nat.le_step) -- goal: 4 ≤ 0
    repeat (first | 
          apply Nat.le_refl | 
          apply Nat.le_step)
    done

example : 3 ≤ 6 := by
  apply Nat.le_step
  apply three_le_five

/-! We will write some basic tactics
-/

/-- A tactic for proving `≤` for natural numbers -/
macro "nat_le" : tactic =>
  `(tactic| repeat (first | 
          apply Nat.le_refl | 
          apply Nat.le_step))

example : 3 ≤ 33 := by nat_le

/-- A tactic where we try repeatedly to finish with a theorem or take a step with another. -/
macro "finish_with" x:term 
  "steps" y:term : tactic => do
  `(tactic| repeat (first | 
          apply ($x:term) | 
          apply $y))

/-! 
We can use our more general tactic in different ways.

```lean
example : 4 ≤ 44 := by
  finish_with Nat.le_refl steps Nat.le_step

#check Nat.succ_le_succ -- ∀ {n m : ℕ}, n ≤ m → Nat.succ n ≤ Nat.succ m
#check Nat.zero_le -- ∀ (n : ℕ), 0 ≤ n

example : 4 ≤ 44 := by
  finish_with Nat.zero_le steps Nat.succ_le_succ
```
-/

example : 4 ≤ 44 := by
  finish_with Nat.le_refl steps Nat.le_step

#check Nat.succ_le_succ -- ∀ {n m : ℕ}, n ≤ m → Nat.succ n ≤ Nat.succ m
#check Nat.zero_le -- ∀ (n : ℕ), 0 ≤ n

example : 4 ≤ 44 := by
  finish_with Nat.zero_le steps Nat.succ_le_succ
