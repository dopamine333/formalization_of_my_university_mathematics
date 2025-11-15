import Mathlib
import Mathlib.Analysis.AbsoluteValue.Equivalence

#check TopologicalSpace.ext
#check MetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
#check TopologicalSpace.ext_iff_nhds

-- #check NormedAddCommGroup.
#check AbsoluteValue.uniformSpace

#check AbsoluteValue
#check AbsoluteValue.nonneg
#check AbsoluteValue.eq_zero
#check AbsoluteValue.add_le
#check AbsoluteValue.map_mul

#check Valuation
#check Valuation.instIsPrimeSuppOfNontrivialOfNoZeroDivisors
#check Valuation.supp

#check Filter.HasBasis.tendsto_iff
#check Filter.HasBasis

#check nhdsWithin_hasBasis
#check TopologicalSpace.IsTopologicalBasis.nhds_hasBasis
#check Metric.nhds_basis_ball
#check Filter.HasBasis.mem_iff
#check Filter.atTop_basis

#check WithAbs
#check AbsoluteValue.toNormedRing
#check AbsoluteValue.trivial

#check NormedRing
#check NormedRing.dist_eq
#check PseudoMetricSpace

#check AbsoluteValue.nonneg
#check AbsoluteValue.eq_zero
#check AbsoluteValue.add_le
#check AbsoluteValue.map_mul

#check norm_mul_le
#check dist_self
#check dist_comm
#check dist_triangle
#check eq_of_dist_eq_zero

-- example (R : Type) [NormedRing R] : NormMulClass R := by infer_instance
example (R : Type) [NormedField R] : NormMulClass R := by infer_instance
#check norm_mul


#check WithAbs
#check AbsoluteValue.IsEquiv
-- #check AbsoluteValue.isEquiv_iff_lt_one_iff

#check AbsoluteValue.isEquiv_iff_isHomeomorph
#check AbsoluteValue.isEquiv_iff_exists_rpow_eq

#check IsHomeomorph
#check WithAbs.normedRing

noncomputable example {R : Type u} [Ring R] (v : AbsoluteValue R ℝ) :
  TopologicalSpace (WithAbs v) := inferInstance

noncomputable example {R : Type u} [Ring R] (v : AbsoluteValue R ℝ) :
  IsTopologicalRing (WithAbs v) := inferInstance

#check Topology.IsEmbedding
#check isHomeomorph_iff_isEmbedding_surjective
#check AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs

#check exists_ratio_hasDerivAt_eq_ratio_slope
-- obtain ⟨c, hc, h_eq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope  hff' hgg'

#check tendsto_pow_atTop_nhds_zero_iff_norm_lt_one

#check Valuation
#check AbsoluteValue.toNormedRing
#check NormMulClass.isAbsoluteValue_norm
#check IsAbsoluteValue.toAbsoluteValue

#check AbsoluteValue.isEquiv_of_lt_one_imp
#check AbsoluteValue.isEquiv_iff_lt_one_iff


#check one_mul
#check mul_inv_lt_iff₀
example
  {R : Type u} {S : Type v}
  [Field R] [Semifield S] [LinearOrder S]
  {v : AbsoluteValue R S}
  [IsStrictOrderedRing S] (x y : R) (hpos : v y > 0):
  v x < v y ↔ v (x * y⁻¹) < 1 := by
  rw [← one_mul (v y), ← mul_inv_lt_iff₀ hpos, ← map_inv₀, ← map_mul]


#check AbsoluteValue.isEquiv_of_lt_one_imp
#check AbsoluteValue.exists_lt_one_one_le_of_not_isEquiv
#check AbsoluteValue.exists_one_lt_lt_one_of_not_isEquiv


#check tendsto_pow_atTop_atTop_of_one_lt
#check tendsto_pow_atTop_nhds_zero_of_lt_one
#check AbsoluteValue.tendsto_div_one_add_pow_nhds_zero
#check AbsoluteValue.tendsto_div_one_add_pow_nhds_one

#check Real.iSup_pow
#check Finset.le_sup_dite_pos
#check Fintype.induction_subsingleton_or_nontrivial
#check Finset.induction

#check AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv




#check Metric.denseRange_iff
#check AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
#check WithAbs.equiv
#check tendsto_pi_nhds
#check Fintype.sum_pi_single
#check tendsto_finset_sum
-- WithAbs.tendsto_one_div_one_add_pow_nhds_one
#check tendsto_iff_norm_sub_tendsto_zero
#check tendsto_inv_iff₀
#check AbsoluteValue.tendsto_div_one_add_pow_nhds_one
#check tendsto_zero_iff_norm_tendsto_zero
#check AbsoluteValue.tendsto_div_one_add_pow_nhds_zero
#check Filter.Tendsto.mul_const
#check Metric.tendsto_atTop


#check AbsoluteValue.sum_le

#check WithAbs



#check Topology.IsEmbedding
#check isHomeomorph_iff_isEmbedding_surjective
#check AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs
#check map_pow
#check map_zpow

#check IsTopologicalGroup.isInducing_iff_nhds_one

open Topology Filter
theorem IsEquiv.equivWithAbs_image_mem_nhds_zero'
  {F : Type u_1} [Field F] {v w : AbsoluteValue F ℝ}
  (h : v.IsEquiv w) {U : Set (WithAbs v)}
    (hU : U ∈ 𝓝 0) : WithAbs.equivWithAbs v w '' U ∈ 𝓝 0 := by
  by_cases hv : v.IsNontrivial
  . have hw := h.isNontrivial_congr.1 hv
    rw [Metric.mem_nhds_iff] at hU ⊢
    obtain ⟨ε, hε, hU⟩ := hU
    obtain ⟨a, ha⟩ := hw.exists_abv_lt_one
    obtain ⟨n, hn⟩ : ∃ n, (v a) ^ n < ε := exists_pow_lt_of_lt_one hε (h.lt_one_iff.2 ha.2)
    refine ⟨w a ^ n, pow_pos (w.pos ha.1) _, fun x hx ↦ ?_⟩
    rw [← RingEquiv.apply_symm_apply (WithAbs.equivWithAbs v w) x]
    refine Set.mem_image_of_mem _ (hU ?_)
    rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_abv, ← map_pow,
        ← h.lt_iff_lt, map_pow] at hx
    have := hx.trans hn
    simpa [WithAbs.norm_eq_abv]
  . have hw := h.isNontrivial_congr.not.1 hv
    have : ({0} : Set (WithAbs w)) ∈ 𝓝 0 := by
      convert Metric.ball_mem_nhds (0 : WithAbs w) one_half_pos
      -- rw [AbsoluteValue.not_isNontrivial_apply]
      ext x
      refine ⟨fun hx ↦ by rw [hx]; simp, fun hx ↦ ?_⟩
      by_cases hx0 : x = 0
      · exact hx0
      rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_abv] at hx
      have := AbsoluteValue.not_isNontrivial_apply hw ((WithAbs.equiv w).map_ne_zero_iff.2 hx0)
      linarith
    filter_upwards [this] with x rfl
    rw [← RingEquiv.apply_symm_apply (WithAbs.equivWithAbs v w) 0]
    apply Set.mem_image_of_mem
    convert mem_of_mem_nhds hU

  -- rw [Metric.mem_nhds_iff] at hU ⊢
  -- obtain ⟨ε, hε, hU⟩ := hU
  -- obtain ⟨c, hc, hvw⟩ := isEquiv_iff_exists_rpow_eq.1 h
  -- refine ⟨ε ^ c, rpow_pos_of_pos hε _, fun x hx ↦ ?_⟩
  -- rw [← RingEquiv.apply_symm_apply (WithAbs.equivWithAbs v w) x]
  -- refine Set.mem_image_of_mem _ (hU ?_)
  -- rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_abv, ← funext_iff.1 hvw,
  --   rpow_lt_rpow_iff (v.nonneg _) hε.le hc] at hx
  -- simpa [WithAbs.norm_eq_abv]

noncomputable example {K : Type u} [Field K] (v : AbsoluteValue K ℝ) :
  TopologicalSpace (WithAbs v) := inferInstance

set_option trace.Meta.synthInstance true in
noncomputable example {K : Type u} [Field K] (v : AbsoluteValue K ℝ) :
  IsTopologicalDivisionRing (WithAbs v) := inferInstance

#check ValuativeRel
#check IsNonarchimedeanLocalField
#check IsNonarchimedeanLocalField.instIsTopologicalDivisionRing
#check IsValuativeTopology
#check Valued.isTopologicalDivisionRing

#check NormedDivisionRing.to_isTopologicalDivisionRing

#check tendsto_inv₀
#check tendsto_inv_iff₀
#check tendsto_inv_cobounded
#check eventually_cobounded_le_norm
#check tendsto_norm_cobounded_atTop
#check Bornology.eventually_ne_cobounded

#check Filter.Eventually.and
#check Filter.inter_mem
#check Filter.iInter_mem
#check Filter.eventually_all

#check WithAbs
