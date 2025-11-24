import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace uxx_eq_zero

/-

Find all u(x, y) satisfying the equation uxx = 0. Well, we can integrate
once to get ux = constant. But that’s not really right since there’s another
variable y. What we really get is ux(x, y) = f(y), where f (y) is arbitrary.
Do it again to get u(x, y) = f(y)x + g(y). This is the solution formula.
Note that there are two arbitrary functions in the solution.

-/

-- what is deriv? fderiv? Differentiable?
section
variable (f : ℝ → ℝ) (L a : ℝ)
#check deriv f
#check HasDerivAt f L a
#check HasDerivAt
example (x₀ : ℝ) : deriv (fun x ↦ x * x) x₀ = 2 * x₀ := by
  simp only [differentiableAt_fun_id, deriv_fun_mul, deriv_id'', one_mul, mul_one]
  ring


#check fderiv ℝ f a
#check (ℝ →L[ℝ] ℝ)
#check ContinuousLinearMap
#check HasFDerivAt
#check HasFDerivWithinAt

example (x₀ : ℝ) (dx : ℝ): fderiv ℝ (fun x ↦ x * x) x₀ dx = 2 * x₀ * dx := by
  simp only [fderiv_eq_smul_deriv, differentiableAt_fun_id, deriv_fun_mul, deriv_id'', one_mul,
    mul_one, smul_eq_mul]
  ring


#check Differentiable ℝ f
#check DifferentiableAt ℝ f a

end

section
-- what is partial deriv
variable (u : ℝ × ℝ → ℝ) (x₀ y₀ L : ℝ)

-- uₓ(x₀, y₀)
#check deriv (fun x ↦ u (x, y₀)) x₀

-- uₓₓ(x₀, y₀)
#check deriv (fun x ↦ deriv (fun x' ↦ u (x', y₀)) x) x₀

example :
  let u := fun ((x, y) : ℝ × ℝ) ↦ (2 * x * y)
  ∀ (p : ℝ × ℝ), deriv (fun y' ↦ deriv (fun x' ↦ u (x', y')) p.1) p.2 = 2 := by
    intro u (x₀, y₀); dsimp [u]
    calc deriv (fun y' ↦ deriv (fun x' ↦ 2 * x' * y') x₀) y₀
      _ = deriv (fun y' ↦ deriv (fun x' ↦ 2 * x' * y') x₀) y₀ := rfl
      _ = deriv (fun y' ↦ deriv (fun x' ↦ (2 * y') * x') x₀) y₀ := by congr; ext; congr; ext; ring
      _ = deriv (fun y' ↦ 2 * y') y₀ := by congr; ext y'; rw [deriv_const_mul]; simp; fun_prop
      _ = 2 := by rw [deriv_const_mul]; simp; fun_prop
end

-- f_xy = f_yx?,
section
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Symmetric.html#second_derivative_symmetric
#check Convex.second_derivative_within_at_symmetric
#check second_derivative_symmetric
#check ContDiffAt.isSymmSndFDerivAt
#check minSmoothness
#check IsSymmSndFDerivAt
end


--wiki def of fderiv?
section
-- https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative
#check Module
#check NormedAddCommGroup
#check norm_smul
example [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) (a : ℝ)
  : ‖a • v‖ = ‖a‖ * ‖v‖ := by
  apply norm_smul
example [NormedAddCommGroup V] : MetricSpace V := by infer_instance
example [NormedAddCommGroup V] : TopologicalSpace V := by infer_instance
#check IsOpen
#check ContinuousLinearMap
set_option trace.Meta.synthInstance true in
example : ∀ u : ℝ × ℝ, Continuous (fun v : ℝ × ℝ  ↦ (u + v)) := by
  exact fun u ↦ continuous_add_left u
#check IsTopologicalRing
set_option trace.Meta.synthInstance true in
example : Continuous (fun ((a, v) : ℝ × (ℝ × ℝ)) ↦ a • v) := by
  exact continuous_smul
#check ContinuousSMul
set_option trace.Meta.synthInstance true in
example [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousSMul ℝ V := by infer_instance
example [NormedAddCommGroup V] [NormedSpace ℝ V] : ContinuousAdd V := by infer_instance
#check IsBoundedSMul

#check fderiv
example [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  : Norm 𝕜 := by infer_instance
example [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  : Norm E := sorry
#check HasFDerivWithinAt
/-
The derivative is defined in terms of the `IsLittleOTVS` relation to ensure the definition does not
ingrain a choice of norm, and is then quickly translated to the more convenient `IsLittleO` in the
subsequent theorems. It is also characterized in terms of the `Tendsto` relation.
-/
#check Asymptotics.IsLittleOTVS
#check Asymptotics.IsLittleO

example [NormedAddCommGroup V] [NormedSpace ℝ V]
  : ∀ c : V, fderiv ℝ (fun (x : V) ↦ c) 0 = 0 := by
  exact fun c ↦ fderiv_const_apply c

noncomputable example  [NormedAddCommGroup V] [NormedSpace ℝ V] : NontriviallyNormedField ℝ := by infer_instance
example  [NormedAddCommGroup V] [NormedSpace ℝ V] : AddCommGroup V := by infer_instance
example  [NormedAddCommGroup V] [NormedSpace ℝ V] : Module ℝ V := by infer_instance
example  [NormedAddCommGroup V] [NormedSpace ℝ V] : TopologicalSpace V := by infer_instance

example [NontriviallyNormedField 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  : ∀ c : V, fderiv 𝕜 (fun (x : V) ↦ c) 0 = 0 := by
  sorry

#check UniqueDiffOn
#check UniqueDiffWithinAt
#check IsOpen.uniqueDiffOn
#check UniqueDiffWithinAt.eq_deriv
#check UniqueDiffWithinAt.eq
#check UniqueDiffOn.eq

example [NormedAddCommGroup V] [NormedSpace ℝ V]
  : UniqueDiffOn ℝ (Set.univ : Set V) := by exact uniqueDiffOn_univ

example [NormedAddCommGroup V] [NormedSpace ℝ V] (U : Set V) (hU : IsOpen U)
  : UniqueDiffOn ℝ U := by exact IsOpen.uniqueDiffOn hU

#check Differentiable
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : HasDerivAt f (deriv f a) a := by
  exact DifferentiableAt.hasDerivAt (hf a)
end

section
variable
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : V → W) (A : V →L[ℝ] W) (x : V)

open scoped Topology -- for notation 𝓝

example : HasFDerivAt f A x ↔ HasFDerivAtFilter f A x (𝓝 x) := by rfl
example :
  HasFDerivAtFilter f A x (𝓝 x)
  ↔
  (fun x' => f x' - f x - A (x' - x)) =o[ℝ; 𝓝 x] (fun x' => x' - x) := by
    exact hasFDerivAtFilter_iff_isLittleOTVS f A x (𝓝 x)

#check Asymptotics.IsLittleOTVS
#check Asymptotics.isLittleOTVS_iff_isLittleO

example :
  (fun x' => f x' - f x - A (x' - x)) =o[ℝ; 𝓝 x] (fun x' => x' - x)
  ↔
  (fun x' => f x' - f x - A (x' - x)) =o[𝓝 x] (fun x' => x' - x) := by
    exact Asymptotics.isLittleOTVS_iff_isLittleO

#check Asymptotics.IsBigOWith_def
example :
  (fun x' => f x' - f x - A (x' - x)) =o[𝓝 x] (fun x' => x' - x)
  ↔
  ∀ c > 0, Asymptotics.IsBigOWith c (𝓝 x) (fun x' => f x' - f x - A (x' - x)) (fun x' => x' - x) := by
    exact Asymptotics.isLittleO_iff_forall_isBigOWith

example :
  (∀ c > 0, Asymptotics.IsBigOWith c (𝓝 x) (fun x' => f x' - f x - A (x' - x)) (fun x' => x' - x))
  ↔
  (∀ c > 0, ∀ᶠ x' in 𝓝 x, ‖f x' - f x - A (x' - x)‖ ≤ c * ‖x' - x‖) := by
    simp_rw [Asymptotics.isBigOWith_iff]

#check Asymptotics.isLittleO_iff_tendsto
example :
  (fun x' => f x' - f x - A (x' - x)) =o[𝓝 x] (fun x' => x' - x)
  ↔
  (fun x' => ‖f x' - f x - A (x' - x)‖) =o[𝓝 x] (fun x' => ‖x' - x‖) := by
    exact Iff.symm Asymptotics.isLittleO_norm_norm

example :
  (fun x' => ‖f x' - f x - A (x' - x)‖) =o[𝓝 x] (fun x' => ‖x' - x‖)
  ↔
  Filter.Tendsto (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (𝓝 x) (𝓝 0) := by
    rw [Asymptotics.isLittleO_iff_tendsto]
    intro x' hx'
    have : x' = x := by
      rw [norm_eq_zero] at hx'
      rw [sub_eq_zero.mp hx']
    simp [this]

#check Filter.tendsto_map'_iff
#check Homeomorph.subRight
#check map_add_right_nhds
example (g : ℝ → ℝ) :
  Filter.Tendsto g (𝓝 0) (𝓝 0)
  ↔
  Filter.Tendsto (fun x ↦ g (x - 1)) (𝓝 1) (𝓝 0) := by
    convert @Filter.tendsto_map'_iff _ _ _ g (fun x ↦ x - 1) _ _ using 2
    symm
    convert map_add_right_nhds _ _ using 1
    . ring
    . infer_instance


example :
  Filter.Tendsto (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (𝓝 x) (𝓝 0)
  ↔
  Filter.Tendsto (fun h ↦ ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  convert @Filter.tendsto_map'_iff _ _ _ (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (fun h ↦ x + h) _ _ using 2
  . rw [map_add_left_nhds, add_zero]
  . ext h
    dsimp
    congr <;> simp

theorem wiki_def_HasFDerivAt : HasFDerivAt f A x ↔
  Filter.Tendsto (fun h ↦ ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  calc HasFDerivAt f A x
    _ ↔ HasFDerivAtFilter f A x (𝓝 x) := by rfl
    _ ↔ (fun x' => f x' - f x - A (x' - x)) =o[ℝ; 𝓝 x] (fun x' => x' - x) := by
      exact hasFDerivAtFilter_iff_isLittleOTVS f A x (𝓝 x)
    _ ↔  (fun x' => f x' - f x - A (x' - x)) =o[𝓝 x] (fun x' => x' - x) := by
      exact Asymptotics.isLittleOTVS_iff_isLittleO
    _ ↔ (fun x' => ‖f x' - f x - A (x' - x)‖) =o[𝓝 x] (fun x' => ‖x' - x‖) := by
      exact Iff.symm Asymptotics.isLittleO_norm_norm
    _ ↔ Filter.Tendsto (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (𝓝 x) (𝓝 0) := by
      rw [Asymptotics.isLittleO_iff_tendsto]
      intro x' hx'
      have : x' = x := by
        rw [norm_eq_zero] at hx'
        rw [sub_eq_zero.mp hx']
      simp [this]
    _ ↔ Filter.Tendsto (fun h ↦ ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
      convert @Filter.tendsto_map'_iff _ _ _ (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (fun h ↦ x + h) _ _ using 2
      . rw [map_add_left_nhds, add_zero]
      . ext h
        dsimp
        congr <;> simp

end

section
variable
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {U : Set V} (hU : IsOpen U)
  (f : V → W) (A : V →L[ℝ] W) (x : V) (hxU : x ∈ U)

#check IsOpen.nhdsWithin_eq

example :
  HasFDerivAt f A x
  ↔
  HasFDerivWithinAt f A U x
  := by
  rw [HasFDerivAt, HasFDerivWithinAt]
  rw [IsOpen.nhdsWithin_eq]
  . exact hU
  . exact hxU

end

-- f' = 0 → f = c
section

#check is_const_of_deriv_eq_zero
#check IsOpen.is_const_of_deriv_eq_zero
#check IsOpen.exists_is_const_of_deriv_eq_zero

#check is_const_of_fderiv_eq_zero
#check IsOpen.is_const_of_fderiv_eq_zero
#check IsOpen.exists_is_const_of_fderiv_eq_zero

#check RCLike
#check IsRCLikeNormedField

#check IsLocallyConstant

def f : ℝ → ℝ := fun _ ↦ 1

#check Set.mem_preimage
#check isOpen_iff_forall_mem_open
example : IsLocallyConstant f := by
  unfold IsLocallyConstant
  intro s
  obtain h | h : 1 ∈ s ∨ 1 ∉ s := by exact Classical.em (1 ∈ s)
  . have preimage_is_univ : f ⁻¹' s = Set.univ := by
      ext x
      rw [Set.mem_preimage]
      unfold f
      simp
      exact h
    rw [preimage_is_univ]
    exact isOpen_univ
  . have preimage_is_empty : f ⁻¹' s = ∅ := by
      ext x
      rw [Set.mem_preimage]
      unfold f
      simp
      exact h
    rw [preimage_is_empty]
    exact isOpen_empty

example (f : ℝ → ℝ) (hdiff : Differentiable ℝ f) (hderiv : ∀ x : ℝ, deriv f x = 0)
  : ∃ c , ∀ x , f x = c := by
  use f 0
  intro x
  exact is_const_of_deriv_eq_zero hdiff hderiv x 0


#check eq_of_fderiv_eq
example (f : ℝ → ℝ) (hdiff : Differentiable ℝ f) (c : ℝ)
  (hderiv : ∀ x : ℝ, deriv f x = c)
  : ∃ d , ∀ x , f x = c * x + d := by
  let g (x : ℝ) := f x - c * x
  have hdiff' : Differentiable ℝ g := by fun_prop
  have hderiv' : ∀ x : ℝ, deriv g x = 0 := by
    intro x
    unfold g
    rw [deriv_fun_sub, deriv_const_mul]
    simp [hderiv]
    repeat fun_prop
  have g_const : ∃ d, ∀ x, g x = d := by
    use g 0; intros; apply is_const_of_deriv_eq_zero; assumption'

  have ⟨d, hg⟩ := g_const
  use d
  intro x
  calc f x
    _ = f x - c * x + c * x := by ring
    _ = g x + c * x := by unfold g; rfl
    _ = d + c * x := by rw [hg]
    _ = c * x + d := by ring

#check eq_of_fderiv_eq
example (f : ℝ → ℝ) (hdiff : Differentiable ℝ f) (c : ℝ)
  (hderiv : ∀ x : ℝ, deriv f x = c)
  : ∃ d , ∀ x , f x = c * x + d := by
  let g (x : ℝ) := c * x + f 0
  have hdiff' : Differentiable ℝ g := by fun_prop
  have hfderiv : ∀ x : ℝ, fderiv ℝ f x = c • .id ℝ ℝ := by
    intro x
    ext
    simp [hderiv]
  have hfg : ∀ x : ℝ, fderiv ℝ f x = fderiv ℝ g x := by
    intro x
    unfold g
    rw [fderiv_fun_add, fderiv_const_mul]
    simp [hfderiv]
    repeat fun_prop
  have hfg_at_zero : f 0 = g 0 := by simp [g]
  have f_eq_g := eq_of_fderiv_eq hdiff hdiff' hfg 0 hfg_at_zero
  use f 0
  intro x
  calc f x
    _ = g x := by rw [f_eq_g]
    _ = c * x + f 0 := by unfold g; rfl
end


-- main section
-- uxx = 0 → ux = f(y) → u = f(y)x + g(y)
section

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
    have hdiff : Differentiable ℝ (ux . y) := ux_diff_along_x y
    have hderiv : ∀ x, deriv (ux . y) x = 0 := by
      intro x
      simp_rw [← uxx_def, u_equation]
    use (ux . y) 0
    intro x
    apply is_const_of_deriv_eq_zero hdiff hderiv
  have step2 : ∃ f : ℝ → ℝ, ∀ x y, ux x y = f y := by
    have ⟨f, hf⟩ := Classical.axiomOfChoice step1
    use f
    intro x y
    exact hf y x
  have step3 : ∃ f : ℝ → ℝ, ∀ y, ∃ d, ∀ x, (u . y) x = f y * x + d := by
    have ⟨f, hf⟩ := step2
    use f
    intro y
    let g : ℝ → ℝ := fun x ↦ u x y - f y * x
    have hdiff : Differentiable ℝ g := by fun_prop
    have hderiv : ∀ x, deriv g x = 0 := by
      intro x
      unfold g
      rw [deriv_fun_sub, deriv_fun_mul]
      simp [← ux_def, hf]
      repeat fun_prop
    use g 0
    intro x
    calc u x y
      _ = u x y - f y * x + f y * x := by ring
      _ = g x + f y * x := rfl
      _ = g 0 + f y * x := by congr 1; apply is_const_of_deriv_eq_zero hdiff hderiv
      _ = f y * x + g 0 := by ring
  have step4 : ∃ f g: ℝ → ℝ, ∀ x y, u x y = f y * x + g y := by
    have ⟨f, hf⟩ := step3
    have ⟨g, hg⟩ := Classical.axiomOfChoice hf
    use f, g
    intro x y
    exact hg y x

  exact step4

end
