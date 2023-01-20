import Mathlib

/-!
# Subtraction: example of intertwined proofs and definitions. 

The difference of natural numbers is not a natural number. We see three ways of overcoming this problem, which illustrate various important concepts in Lean. 

The first two are in an earlier module while the third is in this one. 
-/

namespace Nat

def minus (m n : ℕ)(hyp : n ≤ m) : ℕ := 
  match m, n, hyp with
  | m, 0, _ => m
  | 0, _ +1, pf => nomatch pf
  | m + 1, n + 1 , pf =>
    minus m n (le_of_succ_le_succ pf)

#eval minus 5 3 (by decide)

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
    
#check Nat.sub_add_cancel
    

end Nat