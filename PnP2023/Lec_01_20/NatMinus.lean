import Mathlib

/-!
# Subtraction: example of intertwined proofs and definitions. 

The difference of natural numbers is not a natural number. We see three ways of overcoming this problem, which illustrate various important concepts in Lean. 

The first two are in an earlier module while the third is in this one. 

Here we subtract natural numbers only when given a proof that the second is less than or equal to the first. Note that as any two terms whose type is the same proposition are equal by definition, the value will not depend on the specific proof.
-/

namespace Nat

/-- Subtract `m` and `n` in the presence of a proof that `n ≤ m`. -/
def minus (m n : ℕ)(hyp : n ≤ m) : ℕ := 
  match m, n, hyp with
  | m, 0, _ => m
  | 0, _ +1, pf => nomatch pf
  | m + 1, n + 1 , pf =>
    minus m n (le_of_succ_le_succ pf)

/-!
An example using `minus` (using `decide` for the proof).

```lean
#eval minus 5 3 (by decide) -- 2
```

-/

#eval minus 5 3 (by decide) -- 2


/-- Subtraction (when valid) and addition are inverses
-/
theorem minus_add_cancel 
  (m n : ℕ)(hyp : n ≤ m) : 
    minus m n hyp + n = m := by
  match m, n, hyp with
  | m, 0, _ => simp [minus]
  | 0, _ +1, pf => contradiction
  | m + 1, n + 1 , pf =>
    simp [minus]
    rw [← add_assoc]
    simp [minus_add_cancel]
    
#check Nat.sub_add_cancel -- Nat.sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n

/-!
Note that in `Lean 4` there is a result `Nat.sub_add_cancel` which is analogous to `minus_add_cancel` above. However the statement of the result requires that the subtraction is valid.

```lean
#check Nat.sub_add_cancel -- Nat.sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n
```
-/
    

end Nat