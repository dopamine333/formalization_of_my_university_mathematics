import Mathlib.Analysis.ODE.Gronwall
open Set Real
open scoped Topology NNReal

namespace ode_unique_done

theorem my_Icc_subset_of_forall_exists_gt
  {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a b : α} {s : Set α}
  (hs : IsClosed (s ∩ Icc a b))
  (ha : a ∈ s)
  (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty)
  : Icc a b ⊆ s := by
  intro y hy
  let t := s ∩ Icc a y
  have ht : IsClosed t := by
    unfold t
    have : Icc a y ⊆ Icc a b := Icc_subset_Icc_right hy.2
    rw [← inter_eq_self_of_subset_left this, inter_left_comm]
    apply isClosed_Icc.inter hs
  have hat : a ∈ t := ⟨ha, (left_mem_Icc.mpr hy.1)⟩
  have nonempty : t.Nonempty := ⟨a, hat⟩
  have hyt : y ∈ upperBounds t := by
    intro z ⟨hzs, hzy⟩
    exact hzy.2
  have bound : BddAbove t := ⟨y, hyt⟩
  let c := sSup t
  have hct : c ∈ t := ht.csSup_mem nonempty bound
  have hcy : c ≤ y := csSup_le nonempty hyt
  obtain hcy | hcy := eq_or_lt_of_le hcy
  . rw [hcy] at hct; exact hct.1
  exfalso
  have hac : a ≤ c := le_csSup bound hat
  have ⟨z, hzs, hcz, hzy⟩ := hgt c ⟨hct.1, hac, hcy.trans_le hy.2⟩ y hcy
  . have hzt : z ∈ t := ⟨hzs, (hac.trans_lt hcz).le, hzy⟩
    have hzc : z ≤ c := le_csSup bound hzt
    exact (hcz.trans_le hzc).false

theorem my_image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
  {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ} {f' : ℝ → E}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ}
  (ha : ‖f a‖ ≤ B a)
  (hB : ContinuousOn B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x)
  ⦃x : ℝ⦄
  : x ∈ Icc a b → ‖f x‖ ≤ B x := by
  intro hx
  let s := {x | ‖f x‖ ≤ B x}
  have hs : IsClosed (s ∩ Icc a b) := by
    rw [inter_comm]
    show IsClosed {x ∈ Icc a b | ‖f x‖ ≤ B x}
    apply isClosed_Icc.isClosed_le
    . exact hf.norm
    . exact hB
  have has : a ∈ s := ha
  have hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty := by
    intro x ⟨hxs, hax, hxb⟩ y hyx
    have : ‖f x‖ ≤ B x := hxs
    obtain h | h := eq_or_lt_of_le this
    . have ⟨r, hfr, hrB⟩ := exists_between (bound x ⟨hax, hxb⟩ h)
      have nhd₁ : ∀ᶠ z in 𝓝[>] x, ‖slope f x z‖ < r := by
        have := (hf' x ⟨hax, hxb⟩).Ioi_of_Ici
        rw [hasDerivWithinAt_iff_tendsto_slope' notMem_Ioi_self] at this
        have := this.norm
        apply this.eventually (p := (. < r))
        exact Iio_mem_nhds hfr
      have nhd₂ : ∀ᶠ z in 𝓝[>] x, slope (‖f .‖) x z < r := by
        apply nhd₁.mono
        intro z hz
        apply lt_of_le_of_lt _ hz
        apply le_trans (le_abs_self _) _
        simp [slope, norm_smul, abs_mul, abs_inv]
        gcongr
        apply abs_norm_sub_norm_le
      have nhd₃ :  ∀ᶠ z in 𝓝[>] x, r < slope B x z := by
        have := (hB' x ⟨hax, hxb⟩).Ioi_of_Ici
        rw [hasDerivWithinAt_iff_tendsto_slope' notMem_Ioi_self] at this
        apply this.eventually (p := (r < .))
        exact Ioi_mem_nhds hrB
      have nhd₄ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
      have ⟨z, z_slope, hxz, hzy⟩ := ((nhd₂.and nhd₃).and nhd₄).exists
      have hzs : ‖f z‖ ≤ B z := by
        have := (z_slope.1.trans z_slope.2).le
        rw [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right] at this
        linarith
        linarith
      exact ⟨z, hzs, hxz, hzy⟩
    . have nhd₁ : ∀ᶠ z in 𝓝[Icc a b] x, ‖f z‖ < B z := by
        apply Filter.Tendsto.eventually_lt _ _ h
        . exact hf.norm x ⟨hax, hxb.le⟩
        . exact hB x ⟨hax, hxb.le⟩
      have nhd₂ : ∀ᶠ z in 𝓝[>] x, ‖f z‖ < B z := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT hxb]
        apply nhd₁.filter_mono
        apply nhdsWithin_mono
        refine' (Ioo_subset_Ioo_left hax).trans (Ioo_subset_Icc_self)
      have nhd₃ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
      have ⟨z, fz_pos, hxz, hzy⟩ := (nhd₂.and nhd₃).exists
      exact ⟨z, fz_pos.le, hxz, hzy⟩
  exact my_Icc_subset_of_forall_exists_gt hs has hgt hx


theorem my_norm_le_gronwallBound_of_norm_deriv_right_le
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f f' : ℝ → E} {δ K ε a b : ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  (ha : ‖f a‖ ≤ δ)
  (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε)
  (x : ℝ)
  : x ∈ Icc a b → ‖f x‖ ≤ gronwallBound δ K ε (x - a) := by
  intro hx
  suffices ∀ r > 0, ‖f x‖ ≤ gronwallBound δ K (ε + r) (x - a) by
    convert ContinuousWithinAt.closure_le
      (f := fun r ↦ ‖f x‖) (g := fun r ↦ gronwallBound δ K (ε + r) (x - a))
      (x := 0) (s := Ioi 0) _ _ _ _ using 1
    . ring_nf
    . simp only [closure_Ioi, mem_Ici, le_refl]
    . exact continuousWithinAt_const
    . apply Continuous.continuousWithinAt
      apply (gronwallBound_continuous_ε _ _ _).comp (continuous_add_left ε)
    . exact this
  intro r rpos
  let g x := gronwallBound δ K (ε + r) (x - a)
  let g' x := K * g x + (ε + r)
  have hg : ContinuousOn g (Icc a b) := by
    apply HasDerivAt.continuousOn
    intros
    apply hasDerivAt_gronwallBound_shift
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ici x) x := by
    intros
    apply HasDerivAt.hasDerivWithinAt
    apply hasDerivAt_gronwallBound_shift
  have ha₂ : ‖f a‖ ≤ g a := by
    unfold g
    rwa [sub_self, gronwallBound_x0]
  have bound₂ : ∀ x ∈ Ico a b, ‖f x‖ = g x → ‖f' x‖ < g' x := by
    intro x hx heq
    calc ‖f' x‖
      _ ≤ K * ‖f x‖ + ε := bound x hx
      _ = K * g x + ε := by rw [heq]
      _ < K * g x + (ε + r) := by linarith
      _ = g' x := rfl
  apply my_image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
  assumption'

theorem my_dist_le_of_trajectories_ODE
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {a b δ : ℝ}
  (hv : ∀ (t : ℝ), LipschitzWith K (v t))
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
  (hg : ContinuousOn g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
  (ha : dist (f a) (g a) ≤ δ)
  (t : ℝ)
  : t ∈ Icc a b → dist (f t) (g t) ≤ δ * exp (K * (t - a)) := by
  let h := f - g
  let h' t := (v t (f t) - v t (g t))
  have hh : ContinuousOn h (Icc a b) := hf.sub hg
  have hh' : ∀ t ∈ Ico a b, HasDerivWithinAt h (h' t) (Ici t) t :=
    fun t ht ↦ (hf' t ht).sub (hg' t ht)
  have ha₂ : ‖h a‖ ≤ δ := by rw [dist_eq_norm] at ha; exact ha
  have bound : ∀ t ∈ Ico a b, ‖h' t‖ ≤ K * ‖h t‖ + 0 := by
    intro t ht
    calc ‖h' t‖
      _ = ‖v t (f t) - v t (g t)‖ := rfl
      _ ≤ K * ‖f t - g t‖ := by apply (hv t).norm_sub_le
      _ = K * ‖h t‖ := rfl
      _ = K * ‖h t‖ + 0 := by rw [add_zero]
  have norm_le := my_norm_le_gronwallBound_of_norm_deriv_right_le hh hh' ha₂ bound t
  simp_rw [gronwallBound_ε0] at norm_le
  convert norm_le using 2
  apply dist_eq_norm_sub

theorem my_ODE_solution_unique_univ_aux_1
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {a b : ℝ}
  (hv : ∀ (t : ℝ), LipschitzWith K (v t))
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
  (hg : ContinuousOn g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
  (ha : f a = g a)
  (t : ℝ)
  : t ∈ Icc a b → f t = g t := by
  intro ht
  replace ha := dist_le_zero.mpr ha
  have h := my_dist_le_of_trajectories_ODE hv hf hf' hg hg' ha t ht
  rw [zero_mul] at h
  exact dist_le_zero.mp h
