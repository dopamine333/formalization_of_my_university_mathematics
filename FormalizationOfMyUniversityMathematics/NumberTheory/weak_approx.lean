import Mathlib.Analysis.AbsoluteValue.Equivalence

open Filter
open scoped Topology

theorem tendsto_one_div_one_add_pow_nhds_one {R : Type*} [Field R] {v : AbsoluteValue R ℝ}
  {a : R} (ha : v a < 1) :
    letI := v.toNormedField
    Filter.atTop.Tendsto (fun n ↦ 1 / (1 + a ^ n)) (𝓝 1) := by
  letI := v.toNormedField
  simpa using inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using ha)

theorem tendsto_one_div_one_add_pow_nhds_zero {R : Type*} [Field R] {v : AbsoluteValue R ℝ}
  {a : R} (ha : 1 < v a) :
    letI := v.toNormedField
    Filter.atTop.Tendsto (fun n ↦ 1 / (1 + a ^ n)) (𝓝 0) := by
  letI := v.toNormedField
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using AbsoluteValue.tendsto_div_one_add_pow_nhds_zero ha
/-
*Weak approximation for finite collection of non-trivial and pairwise inequivalent absolute values*
If v : ι → AbsoluteValue K ℝ is a finite collection of non-trivial and pairwise inequivalent absolute values,
then for any ε > 0 and any collection of elements a : ι → K,
there exists an element x in K such that for each i,
-/
theorem weak_approximation
  {K : Type u} [Field K]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  {v : ι → AbsoluteValue K ℝ}
  (h_IsNontrivial : ∀ (i : ι), (v i).IsNontrivial)
  (h_not_IsEquiv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
  (z : ι → K) (r : ℝ) (hr : 0 < r) :
  ∃ x : K, ∀ i : ι, v i (x - z i) < r := by
  choose a ha using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv h_IsNontrivial h_not_IsEquiv
  let y := fun n ↦ ∑ j, (1 / (1 + (a j)⁻¹ ^ n)) * z j
  have htendsto : ∀ i, letI := (v i).toNormedField; Tendsto y atTop (nhds (z i)) := by
    intro i
    letI := (v i).toNormedField
    simp_rw [← Fintype.sum_pi_single i z, y]
    refine tendsto_finset_sum _ fun j _ ↦ ?_
    by_cases hj : i = j
    · rw [← hj, Pi.single_apply i (z i), if_pos rfl]
      have : v i (a i)⁻¹ < 1 := by simpa [← inv_pow, inv_lt_one_iff₀] using .inr (ha i).1
      simpa using (tendsto_one_div_one_add_pow_nhds_one this).mul_const (z i)
    · simp only [Pi.single_apply j (z j), hj, if_false]
      have : 1 < v i (a j)⁻¹ := by
        have h1 := (ha j).2 i hj
        have h2 := (v i).pos_iff.2 ((v j).pos_iff.1 (one_pos.trans (ha j).1))
        have := one_lt_inv_iff₀.2 ⟨h2, h1⟩
        simpa using this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 <|
        (v i).tendsto_div_one_add_pow_nhds_zero this).mul_const ((WithAbs.equiv (v i)).symm _)
  have : ∀ i, letI := (v i).toNormedField; ∃ N, ∀ n ≥ N, v i (y n - z i) < r := by
    intro i
    letI := (v i).toNormedField
    exact Metric.tendsto_atTop.1 (htendsto i) r hr
  choose N hN using this
  let M := Finset.univ.sup N
  have hM : ∀ i, N i ≤ M := by intro i; exact Finset.le_sup (Finset.mem_univ _)
  exact ⟨y M, fun i ↦ hN i _ (hM i)⟩
