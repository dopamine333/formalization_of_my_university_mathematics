import Mathlib.Tactic

open Set Filter Topology Metric

#check EReal.tendsto_toReal_atTop
#check self_mem_nhdsWithin
#check mem_nhdsWithin_of_mem_nhds
#check EReal.tendsto_coe_atTop
#check EReal.tendsto_toReal_atTop
#check EReal.toReal_coe
#check EReal.coe_toReal
#check EReal.coe_ne_top
#check EReal.coe_ne_bot
#check preimage_range_inter

-- example {f : ℝ → EReal} {a : ℝ} :
--   Tendsto f (𝓝 a) (𝓝[≠] ⊤) ↔ Tendsto (fun x ↦ (f x).toReal) (𝓝 a) atTop := by
--   refine ⟨fun h ↦ EReal.tendsto_toReal_atTop.comp h, fun h ↦ ?_⟩
--   rw [EReal.nhdsWithin_top]
--   intro s hs
--   rw [mem_map] at hs
--   have := h hs
--   have heq : (fun x ↦ (f x).toReal) = EReal.toReal ∘ f := rfl
--   rw [heq, ← map_map, mem_map] at this
--   convert this

#check EReal.tendsto_coe_nhds_top_iff
example {f : ℝ → ℝ} {a : ℝ} :
  Tendsto (fun x ↦ (f x : EReal)) (𝓝 a) (𝓝 ⊥) ↔ Tendsto f (𝓝 a) atBot :=
  EReal.tendsto_coe_nhds_bot_iff


lemma tendsto_example_2'
  {f : ℝ → ℝ} {L : ℝ} {a : ℝ} (h : Tendsto f (𝓝[<] a) (𝓝 L)) :
  ∀ M > L, ∃ y < a, ∀ x ∈ Ioo y a, f x < M := by
  intro M hM
  have : Iio M ∈ 𝓝 L := Iio_mem_nhds hM
  have : f ⁻¹' Iio M ∈ 𝓝[<] a := h this
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at this
  exact this

lemma tendsto_example_2'_atBot
  {f : ℝ → ℝ} {a : ℝ} (h : Tendsto f (𝓝[<] a) atBot) :
  ∀ M, ∃ y < a, ∀ x ∈ Ioo y a, f x < M := by
  intro M
  have : Iio M ∈ atBot := Iio_mem_atBot M
  have : f ⁻¹' Iio M ∈ 𝓝[<] a := h this
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at this
  exact this

-- if a < b < c then `Ioo a c ∈ 𝓝 b`
#check Ioo_mem_nhds
-- then you can use `Tendsto f (𝓝 x) (𝓝 b)` to pull back `Ioo a c` (by definition of Tendsto)
-- and get `f ⁻¹' Ioo a c ∈ 𝓝 x`
-- in a metric space, `f ⁻¹' Ioo a c ∈ 𝓝 x` mean `∃ ε > 0, Metric.ball x ε ⊆ f ⁻¹' Ioo a c`
-- that is `∃ ε > 0, ∀ y ∈ Ioo (x - δ) (x + δ), a < f y < c`.
#check Metric.mem_nhds_iff
-- or you can try some lemma has name `...of_mem_nhds`
#loogle "of_mem_nhds"
lemma tendsto_example
  {f : ℝ → ℝ} {a L : ℝ} (h : Tendsto f (𝓝 a) (𝓝 L)) :
  ∀ M > L, ∃ δ > 0, ∀ x ∈ Metric.ball a δ, f x < M := by
  intro M hM
  have : Iio M ∈ 𝓝 L := Iio_mem_nhds hM
  have : f ⁻¹' Iio M ∈ 𝓝 a := h this
  rw [Metric.mem_nhds_iff] at this
  exact this

lemma tendsto_example'
  {f : ℝ → ℝ} {a L : ℝ} (h : Tendsto f (𝓝 a) (𝓝 L)) :
  ∀ M > L, ∃ δ > 0, ∀ x ∈ Metric.ball a δ, f x < M :=
  fun _ hM ↦ Metric.mem_nhds_iff.mp (h (Iio_mem_nhds hM))


lemma tendsto_example_2
  {f : ℝ → ℝ} {a L : ℝ} (h : Tendsto f (𝓝[<] a) (𝓝 L)) :
  ∀ M > L, ∃ y < a, ∀ x ∈ Ioo y a, f x < M := by
  intro M hM
  have : Iio M ∈ 𝓝 L := Iio_mem_nhds hM
  have : f ⁻¹' Iio M ∈ 𝓝[<] a := h this
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at this
  exact this

  -- ∃ δ > 0, ∀ x ∈ Ioo (a - δ) a, f x < M := by


  -- intro M hM
  -- have : Iio M ∈ 𝓝 L := Iio_mem_nhds hM
  -- have : f ⁻¹' Iio M ∈ 𝓝 a := h this
  -- rw [Metric.mem_nhds_iff] at this
  -- exact this


lemma tendsto_nhdsWithin_Ioi_atBot_iff
  {f : ℝ → ℝ} {c : ℝ} :
  Tendsto f (𝓝[>] c) atBot ↔
    ∀ A : ℝ, ∃ δ > 0, ∀ x ∈ Ioo c (c + δ), f x < A := by
  constructor
  . intro h A
    have hA : {y | y < A} ∈ atBot := Iio_mem_atBot A
    have hfA : {x | f x < A} ∈ nhdsWithin c (Ioi c) := h hA
    rw [mem_nhdsGT_iff_exists_Ioo_subset] at hfA
    obtain ⟨u, hu, hfu⟩ := hfA
    use u - c
    constructor
    . linarith [mem_Ioi.1 hu]
    . rw [add_sub_cancel]
      exact hfu
  . intro h S hS
    rw [mem_map]
    rw [mem_atBot_sets] at hS
    obtain ⟨A, hAS⟩ := hS
    obtain ⟨δ, hδpos, hδ⟩ := h A
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    use c + δ
    constructor
    . rw [mem_Ioi]
      linarith
    . intro x hx
      have := hδ x hx
      exact hAS _ this.le


#check EReal.mem_nhds_top_iff
#check EReal.coe_lt_coe_iff
#check EReal.tendsto_coe_atTop
example : ∀ s ∈ 𝓝 ⊤, (fun x : ℝ ↦ (x : EReal)) ⁻¹' s ∈ atTop := EReal.tendsto_coe_atTop
lemma tendsto_nhdsWithin_Ioi_atBot_iff_EReal
  {f : ℝ → ℝ} {a : ℝ} :
  Tendsto (Real.toEReal ∘ f) (𝓝 a) (𝓝 ⊤) ↔
    ∀ A : ℝ, ∃ ε > 0, ∀ x ∈ ball a ε, A < f x := by
  constructor
  . intro h A
    have : {y : EReal | ↑A < y} ∈ 𝓝 ⊤ := by
      rw [EReal.mem_nhds_top_iff]
      use A
      rfl
    have : {x : ℝ | ↑A < (f x : EReal)} ∈ 𝓝 a := h this
    have : {x : ℝ | A < f x} ∈ 𝓝 a := by
      simp_rw [EReal.coe_lt_coe_iff] at this
      exact this
    rw [Metric.mem_nhds_iff] at this
    exact this
  . intro h S hS
    have := EReal.tendsto_coe_atTop
    have := this hS
    rw [mem_map, mem_atTop_sets] at this
    obtain ⟨A, hAS⟩ := this
    obtain ⟨ε, hεpos, hε⟩ := h A
    rw [mem_map, Metric.mem_nhds_iff]
    refine ⟨ε, hεpos, ?_⟩
    intro x hx
    have := hε x hx
    have := hAS _ this.le
    exact this

#check λ x => x
#check λ x ↦ x
#check λ x ↦ x
