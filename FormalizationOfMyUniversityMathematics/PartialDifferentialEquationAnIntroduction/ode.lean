import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- variable
--   (v : ℝ → ℝ → ℝ) (s : ℝ → Set ℝ) (K : NNReal) (t₀ : ℝ) (f g : ℝ → ℝ)

/-
ODE_solution_unique_univ.{u}
{E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
{v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f g : ℝ → E} {t₀ : ℝ}
(hv : ∀ (t : ℝ), LipschitzOnWith K (v t) (s t))
(hf : ∀ (t : ℝ), HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
(hg : ∀ (t : ℝ), HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
(heq : f t₀ = g t₀)
: f = g


f' = v(t, f(t))

f' = 0
=> v(t, x) = 0

f' = f
=> v(t, x) = x

f' = λ * f
=> v(t, x) = λ * x

f' = f * t
=> v(t, x) = x * t

u'' = -u
=> let u₁ = u, u₂ = u'
  u₁' = u₂
  u₂' = - u₁
  v(t, (x₁, x₂)) = (x₂, -x₁)

u'' = 0
=> let u₁ = u, u₂ = u'
  u₁' = u₂
  u₂' = 0
  v(t, (x₁, x₂)) = (x₂, 0)

-/

/-
ODE_solution_unique_univ.{u}
{E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
{v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f g : ℝ → E} {t₀ : ℝ}
(hv : ∀ (t : ℝ), LipschitzOnWith K (v t) (s t))
(hf : ∀ (t : ℝ), HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
(hg : ∀ (t : ℝ), HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
(heq : f t₀ = g t₀)
-/
#check LipschitzOnWith
#check Convex.lipschitzOnWith_of_nnnorm_deriv_le
#check lipschitzWith_of_nnnorm_deriv_le
#check HasDerivAt.deriv
#check LipschitzWith.lipschitzOnWith

-- f' = 0, f(0) = 1 => f = 1
example (f : ℝ → ℝ) (f_deriv : ∀ t, HasDerivAt f 0 t) (f_init : f 0 = 1)
  : f = 1 := by
  let v : ℝ → ℝ → ℝ := fun t x ↦ 0
  let g : ℝ → ℝ := fun t ↦ 1
  let s : ℝ → Set ℝ := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 0 (v t) (s t) := by
    simp [v, s]
    -- exact LipschitzWith.const' 0
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    exact fun t ↦ hasDerivAt_const t 1
  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

-- f' = 1, f(0) = 1 => f = t + 1
example (f : ℝ → ℝ) (f_deriv : ∀ t, HasDerivAt f 1 t) (f_init : f 0 = 1)
  : f = fun t ↦ t + 1 := by
  let v : ℝ → ℝ → ℝ := fun t x ↦ 1
  let g : ℝ → ℝ := fun t ↦ t + 1
  let s : ℝ → Set ℝ := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 0 (v t) (s t) := by
    simp [v, s]
    -- exact LipschitzWith.const' 1
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    exact fun t ↦ hasDerivAt_id' t
  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

-- f' = t => f = 1/2 * t ^ 2 + f(0)
example (f : ℝ → ℝ) (f_deriv : ∀ t, HasDerivAt f t t)
  : f = fun t ↦ 1/2 * t ^ 2 + f 0 := by
  let v : ℝ → ℝ → ℝ := fun t x ↦ t
  let g : ℝ → ℝ := fun t ↦ 1/2 * t ^ 2 + f 0
  let s : ℝ → Set ℝ := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 0 (v t) (s t) := by
    simp [v, s]
    -- exact fun t ↦ LipschitzWith.const' t
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    intro t
    convert HasDerivAt.const_mul (d' := 2 * t) _ _
    . ring
    convert hasDerivAt_pow _ _
    . ring
  have heq : f 0 = g 0 := by simp [g]
  apply ODE_solution_unique_univ; assumption'


#check Real.exp
#check Real.hasDerivAt_exp
#check hasDerivAt_exp
-- f' = f, f 0 = 1 => f = exp
example (f : ℝ → ℝ) (f_deriv : ∀ t, HasDerivAt f (f t) t) (f_init : f 0 = 1)
  : f = Real.exp := by
  let v : ℝ → ℝ → ℝ := fun t x ↦ x
  let g : ℝ → ℝ := Real.exp
  let s : ℝ → Set ℝ := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 1 (v t) (s t) := by
    simp [v, s]
    exact LipschitzWith.id
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    exact fun t ↦ Real.hasDerivAt_exp t
  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

-- f' = c * f, f 0 = 1 => f = fun t ↦ exp (c * t)
#check hasDerivWithinAt_comp_mul_left_smul_iff
#check HasDerivAt.comp_of_eq
#check HasDerivAt.comp
example (c : ℝ) (f : ℝ → ℝ)
  (f_deriv : ∀ t, HasDerivAt f (c * f t) t) (f_init : f 0 = 1)
  : f = fun t ↦ Real.exp (c * t) := by
  let v : ℝ → ℝ → ℝ := fun t x ↦ c * x
  let g : ℝ → ℝ := fun t ↦ Real.exp (c * t)
  let s : ℝ → Set ℝ := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith ‖c‖₊ (v t) (s t) := by
    simp [v, s]
    apply lipschitzWith_smul
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    intro t
    -- rw [mul_comm]
    -- apply HasDerivAt.comp (h := fun x ↦ c * x) (h₂ := Real.exp) _
    -- . exact Real.hasDerivAt_exp (c * t)
    -- . convert hasDerivAt_mul_const _ using 2; ring

    convert ((hasDerivAt_id t).mul_const c).exp using 1
    <;> simp <;> ring_nf

    -- convert (Real.hasDerivAt_exp _).comp t ((hasDerivAt_id t).mul_const c) using 1
    -- . ring_nf; simp; rfl
    -- . simp; ring_nf

  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

/-
f'' = 0, f' 0 = a, f 0 = b => f = a * x + b
=> let f₁ = f, f₂ = f'
  f₁' = f₂, f₁ 0 = b
  f₂' = 0, f₂ 0 = a
  v(t, (x₁, x₂)) = (x₂, 0)
=> f = (f₁, f₂), f 0 = (b, a)
  f' = (f₁', f₂') = (f₂, 0)
  v(t, p) = (p.2, 0)
  f = (a * t + b, a)
-/

-- #check HasDerivAt.prod
#check HasDerivAt.mul
#check HasDerivAt.fun_mul
#check hasDerivAt_mul_const
theorem f''_eq_zero_aux (a b : ℝ) (f : ℝ → ℝ × ℝ)
  (f_deriv : ∀ t, HasDerivAt f ((f t).2, 0) t) (f_init : f 0 = (b, a))
  : f = fun t ↦ (a * t + b, a) := by
  let v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p ↦ (p.2, 0)
  let g : ℝ → ℝ × ℝ := fun t ↦ (a * t + b, a)
  let s : ℝ → Set (ℝ × ℝ) := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 1 (v t) (s t) := by
    simp [v, s, lipschitzWith_iff_norm_sub_le]
    -- intro x y
    -- rw [Prod.mk_sub_mk, zero_sub_zero, Prod.norm_mk,
    --   norm_zero, max_eq_left (norm_nonneg _), NNReal.coe_one, one_mul,
    --   Prod.mk_sub_mk, Prod.norm_mk]
    -- exact le_max_right _ _
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    intro t
    apply HasDerivAt.prodMk
    . simp only [hasDerivAt_add_const_iff]
      convert hasDerivAt_mul_const _ using 2; ring
    . apply hasDerivAt_const
  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

example (a b : ℝ) (f f' : ℝ → ℝ)
  (f_deriv : ∀ t, HasDerivAt f (f' t) t) (f_init : f 0 = b)
  (f'_deriv : ∀ t, HasDerivAt f' 0 t) (f'_init : f' 0 = a)
  : f = fun t ↦ a * t + b := by
  let F : ℝ → ℝ × ℝ := fun t ↦ (f t, f' t)
  have F_deriv : ∀ t, HasDerivAt F ((F t).2, 0) t := by
    intro t
    apply HasDerivAt.prodMk
    <;> simp [F, f_deriv, f'_deriv]
  have F_init : F 0 = (b, a) := by simp [F, f_init, f'_init]
  have F_eq := f''_eq_zero_aux a b F F_deriv F_init
  ext t
  calc f t
    _ = (F t).1 := rfl
    _ = a * t + b := by rw [F_eq]


/-
f'' = -f => f = a * cos t + b * sin t
f 0 = a * 1 + b * 0 = a
f' 0 = (a * (-sin t) + b * cos t)[t := 0] = a * 0 + b * 1 = b
=> let f₁ = f, f₂ = f'
  f₁' = f₂,   f₁ 0 = a
  f₂' = - f₁, f₂ 0 = b
  v(t, (x₁, x₂)) = (x₂, -x₁)
=> f = (f₁, f₂), f 0 = (a, b)
  f' = (f₁', f₂') = (f₂, - f₁)
  v(t, p) = (p.2, -p.1)
  f = (a * cos t + b * sin t, a * (-sin t) + b * cos t)
-/
#check ContinuousLinearMap.norm_def
#check Real.hasDerivAt_cos
#check Real.hasDerivAt_sin
theorem f''_eq_neg_f_aux (a b : ℝ) (f : ℝ → ℝ × ℝ)
  (f_deriv : ∀ t, HasDerivAt f ((f t).2, - (f t).1) t)
  (f_init : f 0 = (a, b))
  : f = fun t ↦ (a * Real.cos t + b * Real.sin t, a * (-Real.sin t) + b * Real.cos t) := by
  let v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t p ↦ (p.2, -p.1)
  let g : ℝ → ℝ × ℝ := fun t ↦ (a * Real.cos t + b * Real.sin t, a * (-Real.sin t) + b * Real.cos t)
  let s : ℝ → Set (ℝ × ℝ) := fun t ↦ Set.univ
  have hv : ∀ t, LipschitzOnWith 1 (v t) (s t) := by
    simp [v, s, lipschitzWith_iff_norm_sub_le]
    intro a b a' b'
    left
    apply le_of_eq
    convert abs_neg _ using 1
    ring_nf
  have hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t := by
    simp [v, f_deriv, s]
  have hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t := by
    simp [v, g, s]
    intro t
    apply HasDerivAt.prodMk
    . apply HasDerivAt.add
      . convert HasDerivAt.mul_const (c := Real.cos) (c' := - Real.sin t) _ a using 1
        . ext; ring
        . ring
        exact Real.hasDerivAt_cos t
      . convert HasDerivAt.mul_const (c := Real.sin) (c' := Real.cos t) _ b using 1
        . ext; ring
        . ring
        exact Real.hasDerivAt_sin t
    . convert ((Real.hasDerivAt_sin t).const_mul a).fun_neg.fun_add ((Real.hasDerivAt_cos t).const_mul b) using 1
      ring
  have heq : f 0 = g 0 := by simp [f_init, g]
  apply ODE_solution_unique_univ; assumption'

/-
f'' = -f => f = a * cos t + b * sin t
f 0 = a * 1 + b * 0 = a
f' 0 = (a * (-sin t) + b * cos t)[t := 0] = a * 0 + b * 1 = b
=> let f₁ = f, f₂ = f'
  f₁' = f₂,   f₁ 0 = a
  f₂' = - f₁, f₂ 0 = b
  v(t, (x₁, x₂)) = (x₂, -x₁)
=> f = (f₁, f₂), f 0 = (a, b)
  f' = (f₁', f₂') = (f₂, - f₁)
  v(t, p) = (p.2, -p.1)
  f = (a * cos t + b * sin t, a * (-sin t) + b * cos t)
-/
theorem f''_eq_neg_f (a b : ℝ) (f f' : ℝ → ℝ)
  (f_deriv : ∀ t, HasDerivAt f (f' t) t) (f_init : f 0 = a)
  (f'_deriv : ∀ t, HasDerivAt f' (-f t) t) (f'_init : f' 0 = b)
  : f = fun t ↦ a * Real.cos t + b * Real.sin t := by
  let F : ℝ → ℝ × ℝ := fun t ↦ (f t, f' t)
  have F_deriv : ∀ t, HasDerivAt F ((F t).2, - (F t).1) t:= by
    intro t
    apply HasDerivAt.prodMk
    <;> simp [F, f_deriv, f'_deriv]
  have F_init : F 0 = (a, b) := by simp [F, f_init, f'_init]
  have F_eq := f''_eq_neg_f_aux a b F F_deriv F_init
  ext t
  calc f t
    _ = (F t).1 := rfl
    _ = a * Real.cos t + b * Real.sin t := by rw [F_eq]

#check ODE_solution_unique_univ
