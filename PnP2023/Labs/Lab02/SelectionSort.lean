import PnP2023.Lec_01_20.NatMin

/-!
# Selection sort (part 1)

Selection sort is a simple sorting algorithm. It works by repeatedly finding the minimum element and moving it to the front. In this lab, you will implement selection sort in Lean (building on the `smallest` function defined in the lectures) and prove its basic properties. 

You will implement this in two labs (this one and the next). In this lab, you will implement the `selectionSort` function and prove termination. In the next lab, you will prove that the function is correct, i.e., `selectionSort` preserves membership list and the result is sorted.

__Note:__ If the list has duplicates the sorted list will erase these. For example, `[1, 1, 2, 3]` will be sorted to `[1, 2, 3]`. For the purposes of this exercise, this is fine.
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

-- For your convenience, here are some definitions/theorems that may be useful in the two labs. Clicking on them takes you to the source, where you may find other useful results.
#check List.remove -- {α : Type u_1} → [inst : DecidableEq α] → α → List α → List α
#check List.length_cons -- ∀ {α : Type u_1} (a : α) (as : List α), List.length (a :: as) = Nat.succ (List.length as)
#check List.mem_cons -- ∀ {α : Type u_1} {a b : α} {l : List α}, a ∈ b :: l ↔ a = b ∨ a ∈ l
#check List.mem_of_mem_remove -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as → b ∈ as
#check List.remove_eq_of_not_mem -- ∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {as : List α}, ¬a ∈ as → List.remove a as = as
#check List.mem_remove_iff -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as ↔ b ∈ as ∧ b ≠ a


/-! 
We will work throughout with lists of natural numbers.

- Problem 1: Prove the following theorem (remove the sorry)
-/

/-- Removing an element from a list does not increase length -/
theorem remove_length_le (a : ℕ) (l : List ℕ) : (List.remove a l).length ≤ l.length := by 
  sorry


/-- Removing a member from a list shortens the list -/
theorem remove_mem_length {a : ℕ} {l : List ℕ} (hyp : a ∈ l) : (List.remove a l).length < l.length  := by 
  sorry

/-!
- Problem 3: Prove termination of the following definition (remove the sorry). You may wish to remove the `decreasing_by` line.
-/
/-- The selection sort function -/
def selectionSort (l : List ℕ) : List ℕ := 
    if c: l=[] then [] else
    (smallest l c) :: selectionSort (List.remove (smallest l c) l)
termination_by _ _ => l.length
decreasing_by sorry

