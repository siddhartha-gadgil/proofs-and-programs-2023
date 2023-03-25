import Mathlib

def sumTo (n: ℕ)  := match n with
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sum_formula (n: ℕ) : 2 * sumTo n = n * (n + 1):= by
  induction n with
  | zero => 
    simp [sumTo]
  | succ n ih => 
    simp [sumTo, ih]
    linarith
