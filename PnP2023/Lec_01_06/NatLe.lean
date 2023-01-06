import Mathlib
/-!
# Examples of Proofs

We see our first proofs, most of which involve the `≤` relation on natural numbers. 

We will see that the natural numbers are "defined" in terms of the `zero` and `succ` constructors.

* `Nat.zero : ℕ` 
* `Nat.succ : ℕ → ℕ`

Analogous to this, (modulo renaming) the `≤` relation is defined in terms of the `le_refl` and `le_step` constructors.

* `Nat.le : ℕ → ℕ → Prop`
* `Nat.le_refl : ∀ n : ℕ, n ≤ n`
* `Nat.le_step : ∀ {n m : ℕ}, n ≤ m → n ≤ Nat.succ m`
-/


#check Nat.zero
#check Nat.succ

#check Nat.le
#check Nat.le_step
#check Nat.le_refl

/-- The theorem that `1 + 1 = 2` -/
theorem one_plus_one_is_two :
   1 + 1 = 2 := rfl

#check rfl  -- rfl.{u} {α : Sort u} {a : α} : a = a
/- `rfl : a = a` is the unique constructor of the equality type. This is the same as `Eq.refl` except that it takes `a` implicitly instead of explicitly.

This is a more powerful theorem than it may appear at first, because although the statement of the theorem is `a = a`, lean will allow anything that is definitionally equal to that type. So, for instance, `2 + 2 = 4` is proven in lean by `rfl`, because both sides are the same up to definitional equality.-/

#check Eq.refl -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a


-- example : 2 = 2 := 2 = 2

-- theorem wrong : 1 + 2 = 2 := rfl

example : 1 + 2 = 3 := Eq.refl _

-- example : 1 ≤ 2 := rfl

-- def not_a_nat : ℕ := "you cannot fool me"

def two : ℕ := 2
-- def two' : ℕ := ℕ 

example : 2 = 2 := Eq.refl 2

example : 3 = 3 := @Eq.refl ℕ 3

example : 3  = 3 := @Eq.refl _ 3

#check 1 = 1 -- 1 = 1 : Prop
#check ℕ -- ℕ : Type

/- The universe of propositions. Prop ≡ Sort 0-/
#check Prop -- Prop : Type

/- A type universe. Type ≡ Type 0, Type u ≡ Sort (u + 1)-/
#check Type -- Type : Type 1

