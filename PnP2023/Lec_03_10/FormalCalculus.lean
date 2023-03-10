import Mathlib
/-!
# Formal Calculus

We introduce formal structures for integration and differentiation. Properties should be added to make these mathematically sound. But correctness can be ensured temporarily by makig sure individual definitions are correct.
-/

class Integrable (f: ℝ → ℝ) where
  integral (a b : ℝ) : ℝ  
  interval_union (a b c : ℝ) :
    integral a c = integral a b + integral b c

def integral (f: ℝ → ℝ)[int : Integrable f]
  (a b : ℝ ) :=
  int.integral a b

theorem integral_point(f: ℝ → ℝ)[int : Integrable f]
  (a : ℝ ) : integral f a a = 0 := by
    unfold integral
    have l := int.interval_union a a a
    simp  at l
    assumption

structure OneJet where
  value : ℝ
  derivative : ℝ

#check FunLike

structure SmoothFunction where
  jet: ℝ → OneJet 

def SmoothFunction.derivative (f: SmoothFunction) : ℝ → ℝ := 
  fun x ↦ f.jet (x) |>.derivative

def SmoothFunction.value (f: SmoothFunction) : ℝ → ℝ := 
  fun x ↦ f.jet (x) |>.value


instance fundThm (f: SmoothFunction) :
  Integrable (f.derivative) where
  integral (a b) := f.value b - f.value a
  interval_union (a b c) := by
    simp [integral]
