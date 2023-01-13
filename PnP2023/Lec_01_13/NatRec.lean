import Mathlib

/-!
# Recursive functions

We have defined functions in terms of other functions. Besides this essentially the only way to define functions is _recursion_. In __Dependent Type Theory__ recursion/induction is very powerful.

In particular, unlike imperative programming all loops are implemented in terms of recursion.
-/

def fctrl(n : ℕ):  ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * (fctrl n)

#eval fctrl 5

/-!
## Fibonacci numbers:

* `fib 0 = 1`
* `fib 1 = 1`
* `fib (n + 2) = fib n + (fib (n + 1))` 
-/
def fib : ℕ → ℕ 
| 0 => 1
| 1 => 1
| n + 2 => fib n + (fib (n + 1))
 
/-!
We can instead define pairs, so
if  `(a, b) = (fib n, fib (n + 1))`
then `(fib (n + 1), fib (n + 2)) = (b, a+ b)` 
-/
def fibAux (a b n : ℕ) : ℕ × ℕ  :=
  match n with
  | 0 => (a, b)
  | k + 1 => fibAux b (a + b) k

def fib'(n) := (fibAux 1 1 n).1

#eval fib' 42

partial def silly_fib : ℕ → ℕ 
| 0 => 1
| 1 => 1
| n + 2 => silly_fib n + (silly_fib (n + 3))

partial def hcf (a b : ℕ) : ℕ :=
  if b < a then hcf b a
  else
    if a = 0 then b
    else hcf a (b - a)

#eval hcf 18 12