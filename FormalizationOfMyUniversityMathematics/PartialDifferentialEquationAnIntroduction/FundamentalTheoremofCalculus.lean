import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace FundamentalTheoremofCalculus

open intervalIntegral
open scoped Topology
-- -- Interval integral notation
example (f : ℝ → ℝ) (hab : a ≤ b)
  : ∫ x in a..b, f x = ∫ x in Set.Ioc a b, f x := by
  -- simp [intervalIntegral, hab]
  exact integral_of_le hab

example (f : ℝ → ℝ) (hab : a ≤ b)
  : ∫ x in a..b, f x ∂μ= ∫ x in Set.Ioc a b, f x ∂μ:= by
  exact integral_of_le hab

example (f : ℝ → ℝ)
  : ∫ x in a..b, f x = ∫ x in a..b, f x ∂MeasureTheory.volume := by
  rfl

-- FTC Part I in Lean
#check integral_hasDerivAt_right
#check StronglyMeasurableAtFilter
#check IntervalIntegrable
#check MeasureTheory.Integrable
#check Continuous.intervalIntegrable

example (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)
  : StronglyMeasurableAtFilter f (𝓝 x) MeasureTheory.volume := by
  exact Continuous.stronglyMeasurableAtFilter hf MeasureTheory.volume (𝓝 x)

example (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f MeasureTheory.volume)
  : IntervalIntegrable f MeasureTheory.volume a b := by
  exact MeasureTheory.Integrable.intervalIntegrable hf

example (f : ℝ → ℝ) (hf : Continuous f)
  : IntervalIntegrable f MeasureTheory.volume a b := by
  exact Continuous.intervalIntegrable hf a b

#check integral_log
#check integral_id
#check integral_const_mul
#check integral_pow
example (x : ℝ) : HasDerivAt (fun x' ↦ x' ^ 2) (2 * x) x := by
  convert integral_hasDerivAt_right (f := fun x' ↦ 2 * x') (a := 0) (b := x) _ _ _
  . rw [integral_const_mul, integral_id]
    ring
  . apply Continuous.intervalIntegrable
    continuity
  . apply Continuous.stronglyMeasurableAtFilter
    continuity
  . apply Continuous.continuousAt
    continuity

#check hasDerivAt_deriv_iff
example (x : ℝ) : HasDerivAt (fun x' ↦ x' ^ 2) (2 * x) x := by
  convert (hasDerivAt_deriv_iff (f := fun x' ↦ x' ^ 2)).mpr _
  . ext x'
    rw [deriv_pow_field]
    ring
  . fun_prop

/-
f' = 0
f = c
∫ x in a..b, f'
= f a - f b
= ∫ x in a..b, 0
= 0

f a = f b
-/
example (c x : ℝ) : ∫ _ in 0..x, c = c * x  := by
  rw [integral_const]
  ring
  rfl

#check Continuous.deriv_integral
#check Continuous.integral_hasStrictDerivAt




#check integral_eq_sub_of_hasDerivAt
example (f : ℝ → ℝ) (hderiv : ∀ x, HasDerivAt f 0 x)
  : ∃ c, ∀ x, f x = c := by
  use f 0
  intro x
  rw [← sub_eq_zero]
  calc f x - f 0
    _ = ∫ (y : ℝ) in 0..x, 0 := by
      rw [integral_eq_sub_of_hasDerivAt (f := f) (f' := fun _ ↦ 0)]
      . intro t ht
        exact hderiv t
      . apply Continuous.intervalIntegrable (by continuity)
    _ = 0 := by
      rw [integral_zero]

/-
f' = c
∫ x in a..b, f'
= f b - f a
= ∫ x in a..b, c
= c * (b - a)
= c * b - c * a
= c * x - c * 0

-/
example (f : ℝ → ℝ) (c : ℝ) (hderiv : ∀ x, HasDerivAt f c x)
  : ∃ d, ∀ x, f x = c * x + d := by
  use f 0
  intro x
  have : f x - f 0 = c * x :=
    calc f x - f 0
    _ = ∫ (y : ℝ) in 0..x, c := by
      rw [integral_eq_sub_of_hasDerivAt (f := f) (f' := fun _ ↦ c)]
      . intro t ht
        exact hderiv t
      . apply Continuous.intervalIntegrable (by continuity)
    _ = c * x := by
      rw [integral_const]
      ring
      rfl
  rw [← this]
  ring

example (f : ℝ → ℝ) (hdiff : Differentiable ℝ f) (hderiv' : ∀ x, deriv f x = 0)
  : ∃ c, ∀ x, f x = c := by
  have hderiv : ∀ x, HasDerivAt f 0 x := by
    intro x
    rw [← hderiv' x]
    exact DifferentiableAt.hasDerivAt (hdiff x)
  use f 0
  intro x
  rw [← sub_eq_zero]
  calc f x - f 0
    _ = ∫ (y : ℝ) in 0..x, 0 := by
      rw [integral_eq_sub_of_hasDerivAt (f := f) (f' := fun _ ↦ 0)]
      . intro t ht
        exact hderiv t
      . apply Continuous.intervalIntegrable (by continuity)
    _ = 0 := by
      rw [integral_zero]


#check ContinuousOn
#check ContinuousOn.intervalIntegrable
#check Set.uIcc
#check Set.Icc
example (a b : ℝ) (h : a ≤ b) : Set.uIcc a b = Set.Icc a b := by
  exact Set.uIcc_of_le h

example (a b : ℝ) (f : ℝ → ℝ) : ∫ x in a..b, f x = - ∫ x in b..a, f x := by
  exact integral_symm b a


#check ContinuousOn.intervalIntegrable
#check integral_comp_mul_deriv


#check is_const_of_deriv_eq_zero
theorem example1
  (u : ℝ → ℝ → ℝ) (ux : ℝ → ℝ → ℝ) (uxx : ℝ → ℝ → ℝ)
  (ux_def : ∀ x y, ux x y = deriv (u . y) x)
  (uxx_def : ∀ x y, uxx x y = deriv (ux . y) x)
  (u_diff_along_x : ∀ y, Differentiable ℝ (u . y))
  (ux_diff_along_x : ∀ y, Differentiable ℝ (ux . y))
  (u_equation : ∀ x y, uxx x y = 0)
  : ∃ f g : ℝ → ℝ, ∀ x y, u x y = f y * x + g y := by
  have step1 : ∀ y, ∃ c, ∀ x, (ux . y) x = c := by
    intro y
    have hderiv : ∀ x, HasDerivAt (ux . y) 0 x := by
      intro x
      convert DifferentiableAt.hasDerivAt _
      rw [← uxx_def, u_equation]
      apply ux_diff_along_x
    let f := (ux . y)
    use f 0
    intro x
    rw [← sub_eq_zero]
    calc f x - f 0
      _ = ∫ (y : ℝ) in 0..x, 0 := by
        rw [integral_eq_sub_of_hasDerivAt (f := f) (f' := fun _ ↦ 0)]
        . intro t ht
          exact hderiv t
        . apply Continuous.intervalIntegrable (by continuity)
      _ = 0 := by
        rw [integral_zero]
  have step2 : ∃ f : ℝ → ℝ, ∀ x y, ux x y = f y := by
    have ⟨f, hf⟩ := Classical.axiomOfChoice step1
    use f
    intro x y
    exact hf y x
  have step3 : ∃ f : ℝ → ℝ, ∀ y, ∃ d, ∀ x, (u . y) x = f y * x + d := by
    have ⟨f, hf⟩ := step2
    use f
    intro y
    have hderiv : ∀ x, HasDerivAt (u . y) (f y) x := by
      intro x
      convert DifferentiableAt.hasDerivAt _ using 1
      rw [← ux_def, hf]
      apply u_diff_along_x
    let g := (u . y)
    use g 0
    intro x
    have : g x - g 0 = f y * x :=
      calc g x - g 0
      _ = ∫ (z : ℝ) in 0..x, f y := by
        rw [integral_eq_sub_of_hasDerivAt (f := g) (f' := fun _ ↦ f y)]
        . intro t ht
          exact hderiv t
        . apply Continuous.intervalIntegrable (by continuity)
      _ = f y * x := by
        rw [integral_const]
        ring
        rfl
    rw [← this]
    ring
  have step4 : ∃ f g: ℝ → ℝ, ∀ x y, u x y = f y * x + g y := by
    have ⟨f, hf⟩ := step3
    have ⟨g, hg⟩ := Classical.axiomOfChoice hf
    use f, g
    intro x y
    exact hg y x

  exact step4
