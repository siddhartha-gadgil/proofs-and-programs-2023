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

/-- A random number in `Fin n` -/
def IO.randFin (n : ℕ)(h : 0 < n ) : IO <| Fin n   := do
  let r ← IO.rand 0 (n - 1)
  pure ⟨r % n, Nat.mod_lt r h⟩

#check List.mem_remove_iff -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as ↔ b ∈ as ∧ b ≠ a
#check List.length_pos_of_mem -- ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → 0 < List.length l
#check List.get_mem -- ∀ {α : Type u_1} (l : List α) (n : ℕ) (h : n < List.length l), List.get l { val := n, isLt := h } ∈ l


/-- A random element with a given property from a list, within `IO`  -/
def pickElemIO [DecidableEq α](l: List α)(p: α → Bool)(h : ∃t : α, t ∈ l ∧ p t = true) : IO {t : α // t ∈ l ∧ p t = true} := do
  have h' : 0 < l.length := by 
    have ⟨t, h₀⟩ := h
    apply List.length_pos_of_mem h₀.left
  let index ← IO.randFin l.length h' 
  let a := l.get index
  if c:p a = true then
    return ⟨a, by 
      simp [c]
      apply List.get_mem
      ⟩
  else
    let l' := l.remove a
    have h' : ∃t : α, t ∈ l' ∧ p t = true :=
      by
        have ⟨t, h₁, h₂⟩ := h
        use t
        simp [List.mem_remove_iff, h₁, h₂]
        simp at c
        intro contra
        simp [contra, c] at h₂
    have : l'.length < l.length := by
      apply remove_mem_length
      apply List.get_mem
    let ⟨t, h₁, h₂⟩ ←  pickElemIO l' p h'
    have m : t ∈ l := 
      List.mem_of_mem_remove h₁
    return ⟨t, m, h₂⟩
termination_by _ _ _ l _ _ => l.length  
    
/-- A random element with a given property from a list. As IO may in principle give an error, we specify a default to fallback and the conditions that this is in the list and has the property `p` -/
def pickElemD [DecidableEq α](l: List α)(p: α → Bool)(default : α)(h₁ : default ∈ l)(h₂ : p default = true)
  : 
    {t : α // t ∈ l ∧ p t = true} := (pickElemIO l p ⟨default, h₁, h₂⟩).run' () |>.getD ⟨default, h₁, h₂⟩

/-!
## Random Monad

We used the IO Monad which has a lot of stuff besides randomness.
-/