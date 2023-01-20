import Mathlib

/-!
# Minimum of a list of natural numbers
-/

def smallest (l : List ℕ)(_: l ≠ []) : ℕ := 
  match l with
  | head :: tail => 
      if c:tail = [] then head
      else 
       Nat.min head (smallest tail c) 

#eval smallest [7, 8, 1,2,3,4,5] (by decide)

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

#check Nat.min_eq_right          

def egNat : ℕ := by
  right
  left

#eval egNat