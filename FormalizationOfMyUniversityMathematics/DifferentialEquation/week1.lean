import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

open Real (exp) -- write exp instead of Real.exp

-- 20250901 two in class example

/-

y' = ay + b, y(0) = y₀
→ y' - ay = b
→ (y' - ay) exp(-at) = b exp (-at)
→ (exp(-at)y)' = b exp(-at)
→ exp(-as)y - y(0) = b/(-a) (exp(-as) - 1)
→ y = b/a (exp(as) - 1) + y(0) exp(as)

y' = y ^ 2
→ y ^ -2 * y' = 1
→ (-1 / y)' = 1
→ (-1/y(s)) - (-1/y(0)) = s
→ y = 1 / (1/y(0) - s)

use lean to check the missing hypothesis
-/


-- need fundamental thm of calculus for f is C¹
-- 1. (fun u ↦ ∫ t in 0..u, f(t))' (x) = f(x)
#check intervalIntegral.deriv_integral_right
#check (ContDiff.continuous _).intervalIntegrable
#check (ContDiff.continuous _).stronglyMeasurableAtFilter
#check (ContDiff.continuous _).continuousAt
-- 2. f(b) - f(a) = ∫ x in a..b, f'(x)
#check intervalIntegral.integral_deriv_of_contDiffOn_uIcc
#check ContDiff.contDiffOn
#check intervalIntegral.integral_deriv_eq_sub'

#check integral_exp_mul_complex
lemma integral_exp_mul {a b c : ℝ} (hc : c ≠ 0) :
  ∫ (x : ℝ) in a..b, exp (c * x) = (exp (c * b) - exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => exp (c * y) / c) (exp (c * x)) x := by
    intro x
    convert ((Real.hasDerivAt_exp (c * x)).comp x ((hasDerivAt_id x).const_mul c)).div_const c using 1
    rw [mul_one, mul_div_cancel_right₀ (exp (c * x)) hc]
  rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  · ring
  · fun_prop

theorem first_example
  (a b : ℝ) (y : ℝ → ℝ) (h_smooth: ContDiff ℝ 1 y) :
  (∀ t, deriv y t = a * (y t) + b)
  ↔
  (∀ t, y t = if a = 0
              then b * t + y 0
              else b / a * (Real.exp (a * t) - 1) + (y 0) * Real.exp (a * t)) := by
  let y' t := deriv y t


  calc
    ∀ t, y' t = a * (y t) + b
    _ ↔ ∀ t, y' t - a * (y t) = b := by
      congr! 1 with t
      exact Iff.symm sub_eq_iff_eq_add'
    _ ↔ ∀ t, ((y' t) - a * (y t)) * (exp (-a * t)) = b * (exp (-a * t)) := by
      congr! 1 with t
      refine (mul_left_inj' ?_).symm
      exact Real.exp_ne_zero (-a * t)
    _ ↔ ∀ t, ((y' t) * (exp (-a * t)) + (y t) * (-a * exp (-a * t))) = b * (exp (-a * t)) := by
      congr! 2 with t
      ring
    _ ↔ ∀ t, deriv (fun t ↦ (y t) * (exp (-a * t))) t = b * (exp (-a * t)) := by
      congr! 2 with t
      rw [deriv_fun_mul, deriv_exp, deriv_const_mul, deriv_id'']
      dsimp [y']
      ring
      . fun_prop
      . fun_prop
      . exact h_smooth.differentiable_one.differentiableAt
      . fun_prop
    _ ↔ ∀ s,
      ∫ t in 0..s, deriv (fun t ↦ (y t) * (exp (-a * t))) t
      = ∫ t in 0..s, b * (exp (-a * t)) := by
      constructor
      . intro h s
        simp_rw [h]
      . intro h
        let f t := deriv (fun t ↦ y t * exp (-a * t)) t
        let g t := b * exp (-a * t)
        let F s := ∫ t in 0..s, f t
        let G s := ∫ t in 0..s, g t
        change ∀ s, F s = G s at h
        change ∀ t, f t = g t
        replace h : ∀ t, deriv F t = deriv G t := by simp [funext h]
        have f_smooth : Continuous f := by fun_prop
        have g_smooth : Continuous g := by fun_prop
        replace h : ∀ t, f t = g t := by
          intro t
          have := h t
          rwa [intervalIntegral.deriv_integral_right,
              intervalIntegral.deriv_integral_right] at this
          . exact g_smooth.intervalIntegrable _ _
          . exact g_smooth.stronglyMeasurableAtFilter _ _
          . exact g_smooth.continuousAt
          . exact f_smooth.intervalIntegrable _ _
          . exact f_smooth.stronglyMeasurableAtFilter _ _
          . exact f_smooth.continuousAt
        exact h
    _ ↔ ∀ s,
      (y s) * (exp (-a * s)) - (y 0) * (exp (-a * 0))
      = ∫ t in 0..s, b * (exp (-a * t)) := by
        congr! 2 with s
        rw [intervalIntegral.integral_deriv_of_contDiffOn_uIcc]
        fun_prop
    _ ↔ ∀ s,
      (y s) * (exp (-a * s)) - (y 0)
      = ∫ t in 0..s, b * (exp (-a * t)) := by
        congr! 3 with s
        rw [mul_zero, Real.exp_zero, mul_one]
    _ ↔ ∀ s,
      y s = ((∫ t in 0..s, b * (exp (-a * t))) + y 0) * exp (a * s) := by
        congr! 1 with s
        rw [sub_eq_iff_eq_add,
            neg_mul, Real.exp_neg, mul_inv_eq_iff_eq_mul₀]
        exact Real.exp_ne_zero (a * s)
    _ ↔ ∀ s,
      y s = ((if a = 0 then b * s else b / a * (1 - Real.exp (-a * s))) + y 0) * exp (a * s) := by
        congr! 2 with s
        by_cases h : a = 0
        . simp [h, mul_comm]
        . simp [h]
          simp_rw [← neg_mul]
          rw [integral_exp_mul (neg_ne_zero.2 h)]
          field_simp [neg_ne_zero.2 h]
          ring
          sorry
    _ ↔ ∀ t,
    y t = if a = 0
          then b * t + y 0
          else b / a * (Real.exp (a * t) - 1) + (y 0) * Real.exp (a * t) := by
        congr! 2 with s
        by_cases h : a = 0
        . simp [h]
        . simp [h]
          rw [add_mul, mul_assoc, sub_mul,
            one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

  -- f = g ↔? ∀ s, ∫ t in 0..s, f t = ∫ t in 0..s, g t

theorem first_example_method_2
  (a b : ℝ) (y : ℝ → ℝ) (h_smooth: ContDiff ℝ 1 y) :
  (∀ t, deriv y t = a * (y t) + b)
  ↔
  (∀ t, y t = if a = 0
              then b * t + y 0
              else b / a * (Real.exp (a * t) - 1) + (y 0) * Real.exp (a * t)) := by
  let y' t := deriv y t
  by_cases ha : a = 0

  . simp_rw [ha, zero_mul, zero_add, ite_true]
    change (∀ t, y' t = b) ↔ (∀ t, y t = b * t + y 0)
    constructor
    . intro h t
      have step₁ : ∀ s, ∫ t in 0..s, y' t = ∫ t in 0..s, b := by
        intro s
        rw [← funext_iff] at h
        apply_fun (fun f : ℝ → ℝ ↦ ∫ t in 0..s, f t) at h
        exact h
        -- intro s
        -- simp_rw [h]
      have step₂ : ∀ s, y s - y 0 = b * s := by
        intro s
        replace step₁ := step₁ s
        rwa [intervalIntegral.integral_deriv_eq_sub' y,
            intervalIntegral.integral_const,
            sub_zero, smul_eq_mul, mul_comm] at step₁
        . rfl
        . exact fun _ _ ↦ h_smooth.differentiable_one.differentiableAt
        . fun_prop
      have step₃ : ∀ s, y s = b * s + y 0 := by
        simp_rw [sub_eq_iff_eq_add] at step₂
        exact step₂
      have step₄ : y t = b * t + y 0 := by
        exact step₃ t
      exact step₄
    . intro h t
      unfold y'
      rw [funext h, deriv_add_const, deriv_const_mul, deriv_id'', mul_one]
      . fun_prop
  . simp_rw [ha, ite_false]
    change (∀ t, y' t = a * (y t) + b) ↔ (∀ t, y t = b / a * (Real.exp (a * t) - 1) + (y 0) * Real.exp (a * t))
    constructor
    . intro h s
      have step₁ : ∀ t, (y' t - a * y t) * (exp (-a * t)) = b * (exp (-a * t)) := by
        intro t
        congr
        rw [h]
        ring
      have step₂ : ∀ t, deriv (fun u ↦ y u * exp (-a * u)) t = b * (exp (-a * t)) := by
        intro t
        rw [deriv_fun_mul, deriv_exp, deriv_const_mul, deriv_id'', ← step₁]
        ring
        all_goals apply Differentiable.differentiableAt; fun_prop
      have step₃ : ∀ t, y t * exp (-a * t) - y 0 * exp (-a * 0) = b * ((exp (-a * t) - exp (-a * 0)) / -a) := by
        intro t
        have := funext step₂
        apply_fun (fun f : ℝ → ℝ ↦ ∫ u in 0..t, f u) at this
        rw [intervalIntegral.integral_deriv_eq_sub' (fun u ↦ y u * exp (-a * u)),
            intervalIntegral.integral_const_mul] at this
        rw [← integral_exp_mul (neg_ne_zero.2 ha)]
        exact this
        . rfl
        . intros; apply Differentiable.differentiableAt; fun_prop
        . fun_prop
      have : ∀ t, y t = b / a * (exp (a * t) - 1) + (y 0) * exp (a * t) := by
        intro t
        have := step₃ t
        simp at this
        rw [sub_eq_iff_eq_add] at this
        apply_fun (fun u ↦ u * exp (a * t)) at this
        rw [Real.exp_neg] at this
        convert this using 1
        . simp
        field_simp
        ring
      exact this s
    . intro h t
      have := funext h
      apply_fun (fun f ↦ deriv f t) at this
      rw [funext h]
      convert this using 1
      rw [deriv_fun_add, deriv_const_mul, deriv_sub_const,
          deriv_exp, deriv_const_mul, deriv_id'',
          deriv_const_mul, deriv_exp, deriv_const_mul, deriv_id'']
      field_simp [ha]
      ring
      all_goals fun_prop

theorem order_thm
  (a b : ℝ) :
  (∀ ε < a, ε < b) ↔ (∀ ε < a, ε ≤ b) := by
  constructor
  . intro h
    intro ε hε
    have := h ε hε
    have := le_of_lt this
    exact this
  . intro h ε hε
    let ε' := (ε + a) / 2
    have hε' : ε' < a := by unfold ε'; linarith
    have hε'₂ : ε < ε' := by unfold ε'; linarith
    have := h ε' hε'
    linarith

#check deriv_fun_inv''
theorem sencond_example
  (y : ℝ → ℝ) (h_smooth: ContDiff ℝ 1 y) (h_ne_zero : ∀ t, y t ≠ 0) :
  (∀ t, deriv y t = y t ^ 2)
  ↔
  (∀ t, y t = 1 / (1 / y 0 - t)) := by
  constructor
  . intro h
    have : ∀ t, deriv y t / y t ^ 2 = 1 := by
      intro t
      rw [h]
      field_simp [h_ne_zero]
    have : ∀ t, deriv (fun u ↦ -1 / y u) t = 1 := by
      intro t
      simp only [neg_div, one_div]
      rw [deriv.fun_neg, deriv_fun_inv'', neg_div, this]
      ring
      . exact h_smooth.differentiable_one.differentiableAt
      . exact h_ne_zero t
    have : ∀ t, (-1 / y t) - (-1 / y 0) = t - 0 := by
      intro t
      rw [← intervalIntegral.integral_deriv_eq_sub' (fun u ↦ -1 / y u) (funext this),
          intervalIntegral.integral_const, smul_eq_mul]
      ring
      . intro x hx
        have := h_smooth.differentiable_one.differentiableAt (x := x)
        have := this.fun_inv (h_ne_zero x)
        have := this.fun_neg
        convert this using 2
        rw [neg_div, one_div]
      . fun_prop
    have : ∀ t, y t = 1 / (1 / y 0 - t) := by
      intro t
      have := this t
      rw [sub_zero] at this
      nth_rw 2 [← this]
      ring_nf
      simp only [inv_inv]
    exact this
  . intro h t
    apply HasDerivAt.deriv
    rw [funext h]; dsimp
    have := ((hasDerivAt_id' t).const_sub (1 / y 0)).fun_inv ?_
    convert this
    . ext; simp
    . simp
    . have := h_ne_zero t
      rw [h] at this
      simpa using this
