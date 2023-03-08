import Mathlib
/-!
## Linear Diaphontine Equations

We solve linear diaphontine equations of the form `a * x + b * y = c` where `a`, `b`, `c` are integers if they have a solution with proof. Otherwise, we return a proof that there is no solution.
-/

inductive DiaphontineSolution (a b c : ℤ) where
    | solution : (x y : ℤ) →  a * x + b * y = c → DiaphontineSolution a b c
    | unsolvable : (∀ x y : ℤ, ¬ (a * x + b * y = c)) → DiaphontineSolution a b c

/-!
This has a solution if and only if the gcd of `a` and `b` divides `c`.
* If the gcd of `a` and `b` divides `c`, by Bezout's Lemma there are integers `x` and `y` such that `a * x + b * y = gcd a b`. Further, as `gcd a b` divides `c`, we have an integer `d` such that `(gcd a b) * d = c`. Then `x * d` and `y * d` are integers such that `a * (x * d) + b * (y * d) = c`.
* The converse follows as `gcd a b` divides `a` and `b`, hence `c = a * x + b * y`.
-/

#check Int.gcd_dvd_left


#check Nat.mul_div_cancel

#check Int.dvd_iff_emod_eq_zero

#check Int.emod_add_ediv -- ∀ (a b : ℤ), a % b + b * (a / b) = a
#check Int.emod_eq_zero_of_dvd -- ∀ {a b : ℤ}, a ∣ b → b % a = 0
#check Int.gcd_eq_gcd_ab -- ∀ (x y : ℤ), ↑(Int.gcd x y) = x * Int.gcdA x y + y * Int.gcdB x y

#check dvd_add /-∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [inst_2 : LeftDistribClass α] {a b c : α},
  a ∣ b → a ∣ c → a ∣ b + c-/

/--
Given `a b : ℤ` such that `b ∣ a`, we return an integer `q` such that `a = b * q`.
-/
def dvdQuotient (a b: Int)(h : b ∣ a) : {q : Int // a = b * q} := 
    let q := a / b
    ⟨q, by 
        rw [← Int.emod_add_ediv a b, Int.emod_eq_zero_of_dvd h, zero_add]
        ⟩

lemma eqn_solvable_divides (a b c : ℤ) :
    (∃ x : ℤ, ∃ y : ℤ,  a * x + b * y = c) →  ↑(Int.gcd a b) ∣ c := by
    intro ⟨x, y, h⟩
    rw [← h]
    apply dvd_add
    · trans a
      · apply Int.gcd_dvd_left  
      · apply Int.dvd_mul_right
    · trans b
      · apply Int.gcd_dvd_right  
      · apply Int.dvd_mul_right

def DiaphontineSolution.solve (a b c : ℤ) : DiaphontineSolution a b c := 
    if h : ↑(Int.gcd a b) ∣ c  
    then 
    by
        let ⟨d, h'⟩ := dvdQuotient (c: Int) (Int.gcd a b)  h 
        rw [Int.gcd_eq_gcd_ab a b] at h'
        rw [add_mul, mul_assoc, mul_assoc] at h'
        let x := (Int.gcdA a b * d)
        let y := (Int.gcdB a b * d)
        exact DiaphontineSolution.solution x y h'.symm         
    else
        by  
        apply DiaphontineSolution.unsolvable
        intro x y contra
        apply h
        apply eqn_solvable_divides a b c
        use x, y
        assumption   

theorem And.mp {q : Prop}(p : Prop) (h : p ∧ (p → q)) : q := by
    simp_all only

example : 1 = 1 := by
    apply And.mp (2 = 2)
    simp

def Vector.dot (n : Nat) (a a' : Vector Int n) : Int :=  
    match n, a, a' with 
    | 0, _, _ => 0
    | n+1, ⟨h :: t, pf⟩, ⟨h' :: t', pf'⟩  =>
        have q : t.length = n := by 
            simp [List.length] at *
            assumption
        have q' : t'.length = n := by 
            simp [List.length] at *
            assumption
        h * h' + Vector.dot n ⟨t, q⟩ ⟨t', q'⟩ 

#check List.elem

#check List.mem_cons


def List.gcd (l : List Int) : Int := 
    match l with 
    | [] => 0
    | h :: t => Int.gcd h (List.gcd t)

