import Mathlib

/-!
# Monads and randomness
We will first recall the `Option` monad and its properties.

* If `α` is a type `Option α` is a type.
* Given `a: α` we get a term of type `Option α` by writing `some a`.
-/

example : Option ℕ := pure 42 -- `pure` is terminology from any Monad.

/-!
* Given `a: Option α` and `f : α → β` we get a term of type `Option β` by writing `a.map f`.
* Given `a: Option α` and `f: α → Option β` we get a term of type `Option β` by writing `a.bind f`.

For both these it is more pleasant to use the `do` notation.

Equivalent to the second is that there is a function `Option Option α → Option α` called `join`.
-/

#check Option.join

#check Task.spawn 

/-!
## IO Monad

Roughly wraps with the state of the *real world*.

For example, a random number is wrapped in this.
-/

#check IO.rand -- IO.rand (lo hi : ℕ) : IO ℕ

/-!
**Question::** Why not just `ℕ`?

* Otherwise we will violate the principle that the value of a function is determined by its arguments.

We still do want a natural number. To get this we can `run` the `IO` computation.
-/

/-- A random natural number -/
def rnd (lo hi : ℕ) : ℕ := 
  ((IO.rand lo hi).run' 
      (() : IO.RealWorld)).get!

/-!
This does not lead to a contradiction, though in a way that may be somewhat surprising.
-/

/-- A random number between 0 and 100-/
def a : ℕ := rnd 0 100
/-- A random number between 0 and 100-/
def b : ℕ := rnd 0 100

/-!
We can run these (every run gives a different result).
```lean
#eval a -- 23
#eval b -- 96
```

Interestingly, we can also run the pair of them and get a result on the diagonal.
```lean
#eval (a, b) -- (87, 87)
```
-/

#eval a -- 23
#eval b -- 96

#eval (a, b) -- (87, 87)

/-- A random pair -/
def rndPair (lo hi : ℕ) : IO <| ℕ × ℕ := do
  let a ← IO.rand lo hi
  let b ← IO.rand lo hi
  pure (a, b)

#eval rndPair 0 100 -- (47, 30)
/-!
```lean
#eval a -- 23
#eval b -- 96

#eval (a, b) -- (87, 87)
```
-/


#check IO.RealWorld

#check Unit

example : a = b := by rfl

-- #reduce a -- times out

-- example : a = 23 := by rfl -- fails

#check Option.orElse

#eval (some 3).orElse 
          (fun _ ↦ some 4) -- some 3

#eval (none).orElse 
          (fun _ ↦ some 4) -- some 4