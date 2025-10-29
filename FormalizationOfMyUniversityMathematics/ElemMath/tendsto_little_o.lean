import Mathlib.Tactic

open Set Filter Topology
theorem Theorem_12_3 (a b : ℝ) (f : ℝ → ℝ) (x₀ : ℝ) (m : ℝ) :
  HasDerivWithinAt f m (Icc a b) x₀ ↔
  ∃ o : ℝ → ℝ,
    (∀ h ∈ Icc a b, f (x₀ + h) - f x₀ = m * h + o h) ∧
    (o 0 = 0) ∧
    (Tendsto (fun h => o h / h) (𝓝[≠] 0) (𝓝 0)) := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have slope_eq : slope f x₀ = fun x ↦ (f x - f x₀) / (x - x₀) := by
    ext x'
    rw [slope_def_field]
  constructor
  . intro hderiv
    let o h := f (x₀ + h) - f x₀ - m * h
    refine ⟨o, by simp [o], by simp [o], ?_⟩



    sorry
  . sorry
