import Mathlib
import PnP2023.Lec_02_01.Foundations
import PnP2023.Lec_01_13.NatRec


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

inductive FiniteTree (α : Type u) where
| leaf (label: α) : FiniteTree α
| node : (List <| FiniteTree α)  → FiniteTree α

-- Does terminate, but Lean does not have enough support yet
partial def FiniteTree.flatten {α : Type u} : FiniteTree α → List α
| FiniteTree.leaf label => [label]
| FiniteTree.node children => 
  children.foldl (fun acc child => acc ++ FiniteTree.flatten child) []


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

#check List

def Vec.to_list {α : Type u} {n : ℕ} : Vec α n → List α
| Vec.nil => []
| Vec.cons head tail => head :: tail.to_list

/-!
## `List` is a parametrized inductive type

```lean
inductive List (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : List α) : List α
```
-/

#check Fin

/-!
Sometimes types include conditions

```lean
structure Fin (n : Nat) where
  /-- If `i : Fin n`, then `i.val : ℕ` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : Nat
  /-- If `i : Fin n`, then `i.2` is a proof that `i.1 < n`. -/
  isLt : LT.lt val n
```
-/

#check Vector

/-!
Conditions can be given by a *subtype* of the type.

```lean
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
```
-/
 
#check Subtype.property
#check Subtype.val
#check Subtype.mk

/-!
When an (indexed) inductive type is introduced,

* the type (or family of types) is defined.
* the constructors are defined.
* a *recursor* is defined.
* a rule for simplification of applications of the recursor is introduced.

The recursor can be conveniently used by pattern matching.
-/

def Bool.disagree (b: Bool) : Bool :=
  match b with
  | Bool.false => Bool.true
  | Bool.true => Bool.false

#check Bool.rec -- {motive : Bool → Sort u} → motive false → motive true → (t : Bool) → motive t

def egFamily (b: Bool) : Type :=
  match b with
  | Bool.false => Unit
  | Bool.true => ℕ

def egDepFunction (b: Bool) : egFamily b :=
  match b with
  | Bool.false => ()
  | Bool.true => by
    simp [egFamily]
    exact 3

set_option pp.motives.all true in
#reduce egDepFunction

set_option pp.motives.all true in
#reduce Bool.disagree