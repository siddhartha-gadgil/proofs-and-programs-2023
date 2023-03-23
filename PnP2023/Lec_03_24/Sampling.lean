import Mathlib

/-!
# Random sampling for an element

We implement sampling to find an element with a given property, for instance being prime or being coprime to a given number. For this we need a hypothesis that such an element exists. 

We use the `IO` monad to generate random numbers. This is because a random number is not a function, in the sense of having value determined by arguments.
-/

/-!
The basic way we sample is to choose an element at random from the list, and then check if it satisfies the property. If it does, we return it. If not, we remove it from the list and try again. To show termination we see (following a lab) that the length of the list decreases by at least one each time.
-/

universe u
/-- Removing an element from a list does not increase length -/
theorem remove_length_le {α :  Type u} [DecidableEq α](a : α) (l : List α) : (List.remove a l).length ≤ l.length := by 
  induction l with
  | nil => 
    simp [List.remove]
  | cons h' t ih => 
      simp [List.remove]
      split
      · apply Nat.le_step
        assumption
      · rw [List.length_cons]
        apply Nat.succ_le_succ
        exact ih


/-- Removing a member from a list shortens the list -/
theorem remove_mem_length  {α :  Type u} [DecidableEq α]{a : α } {l : List α} (hyp : a ∈ l) : (List.remove a l).length < l.length  := by 
  induction l with
  | nil => 
    contradiction
  | cons h' t ih => 
      simp [List.remove]
      split 
      · apply Nat.lt_succ_of_le
        apply remove_length_le
      · rw [List.length_cons]
        apply Nat.succ_lt_succ
        have in_tail: a ∈ t := by 
          have : ¬ a = h' := by assumption
          simp [List.mem_cons, this] at hyp
          assumption
        exact ih in_tail


/-!
We pick an index of the list `l`, which is of type `Fin l.length`. Rather than proving that the random number generator has this property we pass `mod n`.
-/

/-- A random finite number -/
def IO.randFin (n : ℕ)(h : n > 0) : IO <| Fin n   := do
  let r ← IO.rand 0 n
  pure ⟨r % n, Nat.mod_lt r h⟩

#check List.mem_remove_iff -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as ↔ b ∈ as ∧ b ≠ a
#check List.length_pos_of_mem -- ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0 < List.length l
#check List.get_mem -- ∀ {α : Type u_1} (l : List α) (n : ℕ) (h : n < List.length l), List.get l { val := n, isLt := h } ∈ l

/-- A random element with a given property from a list, within `IO`  -/
def pickElemIO [DecidableEq α](l: List α)(p: α → Bool)(h : ∃t : α, t ∈ l ∧ p t = true) : IO {t : α // t ∈ l ∧ p t = true} := sorry

/-- A random element with a given property from a list. As IO may in principle give an error, we specify a default to fallback -/
def pickElemD [DecidableEq α](l: List α)(p: α → Bool)
  (default: {t : α // t ∈ l ∧ p t = true}) : 
    {t : α // t ∈ l ∧ p t = true} := (pickElemIO l p ⟨default.val, default.prop⟩).run' () |>.getD default

/-!
## Random Monad

We used the 
-/