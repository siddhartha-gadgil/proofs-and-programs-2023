import PnP2023.Lec_01_20.NatMin

/-!
# Selection sort

Selection sort is a simple sorting algorithm. It works by repeatedly finding the minimum element and moving it to the front. In this lab, you will implement selection sort in Lean (building on the `smallest` function defined in the lectures) and prove its basic properties. 
-/

/-!
## Removing the smallest element

The first step will be to use the `List.remove` function to remove an element from a list. The function is already defined.
```lean
def remove (a : α) : List α → List α
  | [] => []
  | (b :: bs) => if a = b then remove a bs else b :: remove a bs
```
-/

#check List.remove -- {α : Type u_1} → [inst : DecidableEq α] → α → List α → List α

/-! 
We will work throughout with lists of natural numbers.

- Problem 1: Prove the following theorem (remove the sorry)
-/

/-- Removing an element from a list shortens the list -/
theorem remove_mem_length {a : ℕ} {l : List ℕ} (h : a ∈ l) : (List.remove a l).length < l.length  := by sorry

/-!
- Problem 2: Prove termination of the following definition (remove the sorry). You may wish to remove the `decreasing_by` line.
-/
/-- The selection sort function -/
def selectionSort (l : List ℕ) : List ℕ := 
    if c: l=[] then [] else
    let m := smallest l c
    m :: selectionSort (List.remove m l)
termination_by _ _ => l.length
decreasing_by sorry

/-!
We now define recursively when a list is sorted. -/

/-- A direct definition of an element being below all members of a list. -/
def List.le_all (a : ℕ) (l : List ℕ) : Prop := ∀ b: ℕ, b ∈ l → a ≤ b

/-- Whether a given list is sorted. -/
def List.sorted: List ℕ →  Prop 
| [] => True 
| h :: t => (t.le_all h) ∧ (t.sorted)

/-!
- Problem 3 show that the selection sort function preserves sortedness (remove sorry). 
-/

/-- Selection sort is sorted -/
theorem selectionSort_sorted (l : List ℕ) : (selectionSort l).sorted := by sorry

/-!
- Problems 4, 5: Prove that the selection sort function preserves membership (remove both the sorries).
-/
theorem selectionSort_mem (l : List ℕ) (a : ℕ) : a ∈ l ↔ a ∈ selectionSort l := by 
  apply Iff.intro
  · sorry
  · sorry