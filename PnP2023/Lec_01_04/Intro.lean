import Mathlib
/-!
# Welcome to the course

We start with a quick tour, where we:

* Use Lean as a calculator
* Define some functions and call them.
* Look at some types.
* Look at some proofs.

We will then see
* A glimpse of AI.
* A detailed example with programs and proofs.
-/

/-!
## Lean as a calculator.
-/
#eval 1 + 2

#eval "Hello " ++ "world!"

def some_number := 42

#eval some_number + 23

/-! We next define some functions -/
def add_two (n : ℕ) : ℕ := n + 2

def cube (n : ℕ) : ℕ := n * n * n

#eval cube (add_two 3)

def cube' := fun (n : ℕ) ↦ n * n * n

def cube'' : ℕ → ℕ := fun n ↦ n * n * n

example := λ (n : ℕ) => n * n * n

/-! Terms in Lean, including functions, have types, which can be seen using `#check` -/

#check 1 + 2

#check "Hello " ++ "world!"

#check add_two
#check cube 

#check ℕ
#check Type 
#check ℕ → ℕ

def sum_of_squares (x y : ℕ) : ℕ := x * x + y * y

#check sum_of_squares -- ℕ → (ℕ → ℕ)

#check sum_of_squares 3 -- ℕ → ℕ

def sum_of_squares' : ℕ → ℕ → ℕ := 
  fun x ↦ fun y ↦  x * x + y * y