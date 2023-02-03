import Mathlib
import PnP2023.Lec_02_01.Foundations

/-!
# Inductive Types

We see more precisely what are valid (and not valid) definitions for inductive types. We will also see the weak and strong generalizations: 
_parametric inductive types_ and  _indexed inductive types_.

We have constructed a few examples. We first see some more from Lean core.-/

#check Bool

/-!
Simplest ones are enumerations

```lean
inductive Bool : Type where
  | false : Bool
  | true : Bool
```
-/

#check Nat

/-!
In general, the construtors let us construct terms of the inductive type being introduced using terms of that type.

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

#check Nat.zero -- ℕ 
#check Nat.succ -- ℕ → ℕ 
-/

#check Nat.zero -- ℕ 
#check Nat.succ -- ℕ → ℕ 

#check Unit
#check Empty 

/-!
Two more inductive types:

```lean
abbrev Unit : Type := PUnit

inductive PUnit : Sort u where
  | unit : PUnit

inductive Empty : Type
```
-/

/-!
## Disallowed types
 
- constructors should have resulting type the inductive type being introduced.
-/
-- inductive Silly where
--  | what_is_this: ℕ /- unexpected constructor resulting type
--   ℕ -/

-- inductive Cantor where
--   | mk : (Cantor → Bool) → Cantor
--   /-(kernel) arg #1 of 'Cantor.mk' has a non positive occurrence of the datatypes being declared -/

/-!
The above is disallowed because with a construction of the above form, we would have an injection (in this case a biection) from the power set on the Cantor set to itself.

If we had such an inductive type, we could define

```lean
diag (x :Cantor): Bool :=  match x with
| Cantor.mk f => ¬ f x
```

Apply this to `x:= Cantor.mk diag` to get
```lean
diag (Cantor.mk diag) = ¬ diag (Cantor.mk diag)
``` 
-/

/-!
A non-trivial __positive__ occurence, which is hence allowed, is in the following binary tree.
-/

inductive NatBinTree where 
| leaf : ℕ → NatBinTree
| node : (Bool → NatBinTree) → NatBinTree

/-!
## Parametrized inductive types

Here we define a family of inductive types. However each member of the family is "separately defined", i.e., all constructors only involve that parameter.
-/

universe u

inductive InfiniteTree (α : Type u) where
| leaf (label: α) : InfiniteTree α
| node : (ℕ → InfiniteTree α) → InfiniteTree α

/-!
# Indexed inductive type

We define types `Vec α n` for `α : Type u` and `n: ℕ` with terms of `Vec α n` n-tuples in `α`.

* `α` will be a parameter.
* `n` will be an index.
-/

inductive Vec (α : Type u) : 
            ℕ → Type (u + 1) where
| nil : Vec α 0
| cons : {n : ℕ} →  
  (head : α) → (tail : Vec α n) → Vec α (n + 1)  

example : Vec ℕ 0 := Vec.nil

example : Vec ℕ 1 := Vec.cons 3 (Vec.nil)
