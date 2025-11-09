import Mathlib

open Filter Topology

#check tendsto_inv_nhdsGT_zero
#check tendsto_inv_atTop_nhdsGT_zero

example : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
  convert tendsto_inv_nhdsGT_zero (𝕜 := ℝ) using 2 with x
  exact one_div x

#check Archimedean
example : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
  rw [tendsto_iff_eventually]
  intro large hlarge
  rw [eventually_atTop] at hlarge
  replace hlarge : ∃ M > 0, ∀ x > M, large x := by
    obtain ⟨a, ha⟩ := hlarge
    let M := max 1 a
    have hM0 : M > 0 := lt_max_of_lt_left zero_lt_one
    have hMa : M ≥ a := le_max_right _ _
    exact ⟨M, hM0, fun x hx ↦ ha x (hMa.trans hx.le)⟩
  obtain ⟨M, hM0, hM⟩ := hlarge
  rw [eventually_nhdsWithin_iff]
  have : ∀ᶠ x in 𝓝 0, x < 1 / M := eventually_lt_nhds (one_div_pos.2 hM0)
  apply this.mono
  intro x hxM hx0
  apply hM
  exact (lt_one_div hM0 hx0).2 hxM

open Set in
example : Tendsto (fun x : ℝ => 1 / x) (𝓝[>] 0) atTop := by
  rw [Filter.tendsto_def]
  intro large hlarge
  rw [mem_atTop_sets] at hlarge
  replace hlarge : ∃ M > 0, ∀ x > M, x ∈ large := by
    obtain ⟨a, ha⟩ := hlarge
    let M := max 1 a
    have hM0 : M > 0 := lt_max_of_lt_left zero_lt_one
    have hMa : M ≥ a := le_max_right _ _
    exact ⟨M, hM0, fun x hx ↦ ha x (hMa.trans hx.le)⟩
  obtain ⟨M, hM0, hM⟩ := hlarge
  have h1 : Iio (1 / M) ∈ 𝓝 0 := Iio_mem_nhds (one_div_pos.2 hM0)
  have h2 : Ioi (0 : ℝ) ∈ 𝓝[>] 0 := self_mem_nhdsWithin
  have : Iio (1 / M) ∩ Ioi 0 ∈ 𝓝[>] 0 :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds h1) h2
  apply Filter.mem_of_superset this
  intro x ⟨hxM, hx0⟩
  apply hM
  exact (lt_one_div hM0 hx0).2 hxM
