import Mathlib
/-!
# Formal Calculus

We introduce formal structures for integration and differentiation. Properties should be added to make these mathematically sound. But correctness can be ensured temporarily by making sure individual definitions are correct.

## Formal Integrals
-/

/--
Integrability of `f`, i.e., given an interval `[a, b]`, we can compute the integral of `f` over that interval. Additivity over intervals is also required.
-/
class Integrable (f: ℝ → ℝ) where
  integral (a b : ℝ) : ℝ  
  interval_union (a b c : ℝ) :
    integral a c = integral a b + integral b c

/-- The integral of a function, with the typeclass derived -/
def integral (f: ℝ → ℝ)[int : Integrable f]
  (a b : ℝ ) :=
  int.integral a b

/-- The integral over a single point is zero, proved as an illustration. -/
theorem integral_point(f: ℝ → ℝ)[int : Integrable f]
  (a : ℝ ) : integral f a a = 0 := by
    unfold integral
    have l := int.interval_union a a a
    simp  at l
    assumption

/-!
As an exercise, prove that flip ends of an interval gives the negative of the integral.
-/

/-!
## Formal Derivatives

We define so called __one-jets__ as a value and a derivative at a point. A differentiable function has values a one-jet at each point.
-/

/--
A _one-jet_ is a value and a derivative at a point.
-/
structure OneJet where
  value : ℝ
  derivative : ℝ

/--
A differentiable function is a function that has a one-jet at each point.
-/
structure SmoothFunction where
  jet: ℝ → OneJet 

/--
Derivative of a smooth function, i.e., the derivative of the one-jet at a point.
-/
def SmoothFunction.derivative (f: SmoothFunction) : ℝ → ℝ := 
  fun x ↦ f.jet (x) |>.derivative

/-- 
The value of a smooth function, i.e., the value of the one-jet at a point.
-/
def SmoothFunction.value (f: SmoothFunction) : ℝ → ℝ := 
  fun x ↦ f.jet (x) |>.value

/--
Integrable functions can be obtained from smooth functions via the fundamental theorem of calculus.
-/
instance fundThm (f: SmoothFunction) :
  Integrable (f.derivative) where
  integral (a b) := f.value b - f.value a
  interval_union (a b c) := by
    simp [integral]

/-!
## Constructions of smooth functions

To use the above we need to construct a few smooth functions
-/

namespace SmoothFunction

/--
Constant functions as smooth functions.
-/
def constant (c : ℝ) : SmoothFunction := 
  ⟨fun _ ↦ ⟨c, 0⟩⟩

/--
Sum of smooth functions.
-/
def sum (f g : SmoothFunction) : SmoothFunction := 
  ⟨fun x ↦ ⟨f.value x + g.value x, f.derivative x + g.derivative x⟩⟩

/--
Product of smooth functions using Liebnitz rule.
-/
def prod (f g : SmoothFunction) : SmoothFunction :=
  ⟨fun x ↦ ⟨f.value x * g.value x, f.derivative x * g.value x + f.value x * g.derivative x⟩⟩

/--
Product of a scalar and a smooth function.
-/
def scalarProd (c : ℝ) (f : SmoothFunction) : SmoothFunction :=
  ⟨fun x ↦ ⟨c * f.value x, c * f.derivative x⟩⟩

/-- Addition operation on smooth functions -/
instance : Add SmoothFunction := ⟨sum⟩
/-- Multiplication operation on smooth functions -/
instance : Mul SmoothFunction := ⟨prod⟩
/-- Scalar multiplication for smooth functions -/
instance : SMul ℝ SmoothFunction := ⟨scalarProd⟩

/-!
This gives polynomial functions as a special case. As an exercise, prove that smooth functions form a Ring (indeed an Algebra over ℝ).

We will define some polynomials as smooth functions as an example.
-/

/-- The coordinate function -/
def x : SmoothFunction := ⟨fun x ↦ ⟨x, 1⟩⟩

/-- The power function for a smooth function (automatic if ring is proved) -/
def pow (f: SmoothFunction): ℕ →  SmoothFunction
| 0 => constant 1
| n + 1 => f * (pow f n)

instance : HPow SmoothFunction ℕ SmoothFunction  := ⟨pow⟩ 

instance : Coe ℝ SmoothFunction := ⟨constant⟩

/-- A polynomial. We can have cleaner notation but the goal is to illustrate the construction -/
def poly := (2 : ℝ) •  x + (3 : ℝ) • x^3 + (7: ℝ)


end SmoothFunction
