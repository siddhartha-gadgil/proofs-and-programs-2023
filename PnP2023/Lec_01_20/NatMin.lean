import Mathlib

/-!
# Minimum of a list of natural numbers

Our next example is an algorithm to find the minimum of a non-empty list of natural numbers, with a proof of correctness. The proof of correctness consists of two statements about the algorithm: (1) the minimum is in the list, and (2) the minimum is less than or equal to each element in the list.

To avoid name collisions we will use the name `smallest`
-/

/-- The smallest element in a non-empty list of natural numbers  -/
def smallest (l : List ℕ)(_: l ≠ []) : ℕ := 
  match l with
  | head :: tail => 
      if c:tail = [] then head
      else 
       Nat.min head (smallest tail c) 

/-!
An example

```lean
#eval smallest [7, 8, 1,2,3,4,5] (by decide)
```
-/

#eval smallest [7, 8, 1,2,3,4,5] (by decide)

/-- the result of `smallest` applied to a list is a member of that list -/
theorem smallest_in_list 
  (l : List ℕ)(hyp : l ≠ []) : 
    smallest l hyp ∈ l := by
  match l with
  | head :: tail => 
      by_cases c:tail = []
      · simp [smallest, c]
      · simp [smallest, c]
        by_cases c':head ≤ smallest tail (by simp [c])
        · left
          assumption
        · right
          have lem : 
            Nat.min head (smallest tail (by simp [c])) = smallest tail (by simp [c]) := by
              apply Nat.min_eq_right
              apply Nat.le_of_not_le 
              assumption
          rw [lem]
          simp [smallest_in_list]

#check Nat.min_eq_right -- Nat.min_eq_right {a b : ℕ} (h : b ≤ a) : min a b = b         

/-- An example of using `left` and `right` tactics. -/
def egNat : ℕ := by
  right
  left

#eval egNat -- 1