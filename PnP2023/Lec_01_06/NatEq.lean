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

However, we will first focus on a simpler relation.
-/


#check Nat.zero
#check Nat.succ

#check Nat.le
#check Nat.le_step
#check Nat.le_refl

/-!
### Example: a proof by reflexivity of equality

Our first example is simpler: just a proof of equality. Note that a proof of a theorem in lean is very similar, both conceptually and syntactically, to a definition. 

In a definition, we give a name, a type and a value (though sometimes the type is inferred so can be omitted). In a theorem, we give a name, a statement and a proof. The statement is essentially a type, and the proof is a value of that type.

Technically a statement is a proposition which is slightly different from a type as we see below, but in these examples it is best to think of it as a type.
-/

/-- The theorem that `1 + 1 = 2` -/
theorem one_plus_one_is_two : 1 + 1 = 2 := rfl

/-!
We look more closely at the right hand side, i.e., the _proof_. Below is the description in Lean of `rfl`, which corresponds to _reflexivity of equality_, i.e., the fact that any term is equal to itself:

> `rfl : a = a` is the unique constructor of the equality type. This is the same as `Eq.refl` except that it takes `a` implicitly instead of explicitly.

> This is a more powerful theorem than it may appear at first, because although the statement of the theorem is `a = a`, lean will allow anything that is definitionally equal to that type. So, for instance, `2 + 2 = 4` is proven in lean by `rfl`, because both sides are the same up to definitional equality.

To clarify what is meant by _implicit_ and _explicit_ parameters, we look at the types of `rfl` and `Eq.refl`. Both  these represent the statement that if `α` is a type and `a : α` is a term of type `α` then `a = a`.

```lean
#check rfl  -- rfl.{u} {α : Sort u} {a : α} : a = a

#check Eq.refl -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
```

Notice that in `rfl` _both_ the arguments `α` and `a` are in braces while in `Eq.refl` the argument `α` is in braces while `a` in in parenthesis. When calling a function, the arguments in parenthesis are to be specified, while those in braces are to be _inferred_ (if possible). 

If we prepend `@` to a function name then all arguments become explicit. Conversely we can ask Lean to infer arguments by using `_`. The following examples of similar proofs should clarify these.

```lean
/- argument `a` given explicitly -/
example : 2 = 2 := Eq.refl 2

/- notation `@` used and both `α` and `a` are given explicitly-/
example : 3 = 3 := @Eq.refl ℕ 3

/- the argument `a` is inferred-/
example : 1 + 2 = 3 := Eq.refl _

/- notation `@` used but `α` is inferred-/
example : 3  = 3 := @Eq.refl _ 3
```

### Incorrect proofs

Of course the right hand side may not be a proof of the statement in the left hand side. As mentioned above, this is equivalent to the term on the right-hand side having the _type_ specified in the left hand side.

For example, consdier the following (incorrect) proof. 
```lean
theorem wrong : 1 + 2 = 2 := rfl
```

We get the following error message:
```lean
type mismatch
  rfl
has type
  1 + 2 = 1 + 2 : Prop
but is expected to have type
  1 + 2 = 2 : Prop
```

This is because Lean inferred that `a` is `1 + 2` (and `α` is `ℕ`) and deduced that the type of the right hand side is `1 + 2 = 1 + 2`. This is not equal to the type specified in the left hand side, `1 + 2 = 2`.

We get a different type of error if the statement we are trying to prove is not an equality. For example, consider the following (incorrect) proof.
```lean
example : 1 ≤ 2 := rfl
```

Here Lean is not able to infer `a` (or even `α`) and so we get the following error message:

```lean
type mismatch
  rfl
has type
  ?m.690 = ?m.690 : Prop
but is expected to have type
  1 ≤ 2 : Prop
```

All that Lean knows about `rfl` is that it is a proof that `a = a`, but the statement is not an equality. So Lean assign a _metavariable_ `?m.690` to `a` and cannot _solve_ for the metavariable, giving an error as above.
-/

#check rfl  -- rfl.{u} {α : Sort u} {a : α} : a = a

#check Eq.refl -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a


-- example : 2 = 2 := 2 = 2

-- theorem wrong : 1 + 2 = 2 := rfl

example : 1 + 2 = 3 := Eq.refl _

-- example : 1 ≤ 2 := rfl

-- def not_a_nat : ℕ := "you cannot fool me"

/-!
### Proofs versus Definitions; Sorts and Types

To clarify the similarities and differences between a definition and a theorem, as well as sorts and types, we look at the following example.
-/
/-- Definition of `two` for comparison -/
def two : ℕ := 2
-- def two' : ℕ := ℕ 
/-!
As we have remarked, this is formally very similar to the proof of a theorem. To see the differences, we see some associated types:

```lean
#check 1 = 1 -- 1 = 1 : Prop
#check ℕ -- ℕ : Type

/- The universe of propositions. Prop ≡ Sort 0-/
#check Prop -- Prop : Type

/- A type universe. Type ≡ Type 0, Type u ≡ Sort (u + 1)-/
#check Type -- Type : Type 1
```

The main difference between the two cases is that the type of a theorem is a _proposition_ (i.e., a type in `Prop`). The type of `Prop` is `Type`, which is a type in the next universe up and is the type of `ℕ`. The universes form so called _Sorts_, with all but the first being _Types_.

In other closely related foundational systems (such as _Homotopy Type Theory_), this distinction is not present and all uninverses are _Types_. In Lean _propositions_, i.e., elements of `Prop` (such as `1 = 1`) have a special property that two terms (i.e., proofs) of a proposition are equal by definition.
-/


example : 2 = 2 := Eq.refl 2

example : 3 = 3 := @Eq.refl ℕ 3

example : 3  = 3 := @Eq.refl _ 3

#check 1 = 1 -- 1 = 1 : Prop
#check ℕ -- ℕ : Type

/- The universe of propositions. Prop ≡ Sort 0-/
#check Prop -- Prop : Type

/- A type universe. Type ≡ Type 0, Type u ≡ Sort (u + 1)-/
#check Type -- Type : Type 1

