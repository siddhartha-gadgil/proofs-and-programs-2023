import Mathlib

def sumTo (n: ℕ)  := match n with
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sum_formula (n: ℕ) : 2 * sumTo n = n * (n + 1):= 
  by -- 2 * sumTo n = n * (n + 1)
  induction n with
  | zero => -- 2 * sumTo Nat.zero = Nat.zero * (Nat.zero + 1)
    rfl
  | succ n ih => 
    simp [sumTo] -- 2 * (n + 1 + sumTo n) = Nat.succ n * (Nat.succ n + 1)
    simp [left_distrib, ih] 
    -- 2 * n + 2 + (n * n + n) = Nat.succ n * Nat.succ n + Nat.succ n
    linarith
