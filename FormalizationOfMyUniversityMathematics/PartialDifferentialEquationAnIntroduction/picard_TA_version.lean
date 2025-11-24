import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.ODE.PicardLindelof

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

theorem Real.mem_Icc_sub_add {x : ℝ} {r : ℝ} (h : 0 ≤ r) : x ∈ Icc (x-r) (x+r) := by
  rw [← closedBall_eq_Icc]
  exact mem_closedBall_self h

theorem NNReal.mem_Icc_sub_add {x : ℝ} {r : ℝ≥0} : x ∈ Icc (x-r) (x+r) := by
  exact Real.mem_Icc_sub_add r.2

theorem Real.sub_le_self_add {x : ℝ} {r : ℝ} (h : 0 ≤ r) : x - r ≤ x + r := by
  have := Real.mem_Icc_sub_add (x:=x) h
  exact this.1.trans this.2

theorem NNReal.sub_le_self_add  {x : ℝ} {r : ℝ≥0} : x - r ≤ x + r := by
  exact Real.sub_le_self_add r.2

#check IsPicardLindelof
structure MyIsPicardLindelof {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (a r M L b : ℝ≥0) : Prop where
  continuousOn : ContinuousOn (uncurry f) (Icc (t₀ - a) (t₀ + a) ×ˢ closedBall x₀ r)
  norm_le : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ x ∈ closedBall x₀ r, ‖f t x‖ ≤ M
  LipschitzOnWith : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith L (f t) (closedBall x₀ r)
  ineq : b ≤ a ∧ M * b ≤ r ∧ L * b < 1


namespace MyODE

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {s : Set ℝ} {u : Set E}

noncomputable def picard (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)


@[simp]
lemma picard_apply {x₀ : E} {t : ℝ} : picard f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

lemma picard_apply₀ {x₀ : E} : picard f t₀ x₀ α t₀ = x₀ := by simp

/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl
  rw [this]
  apply hf.comp (by fun_prop)
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

/-- Given a continuous time-dependent vector field `f` and a continuous curve `α`, the composition
`f t (α t)` is continuous in `t`. -/
lemma continuousOn_comp
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : MapsTo α s u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| (contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem)
end

#check ODE.FunSpace
@[ext]
structure FunSpace {E : Type u} [NormedAddCommGroup E]
  (t₀ : ℝ) (x₀ : E) (r b : ℝ≥0) where
  toFun : Icc (t₀ - b) (t₀ + b) → E
  continuous : Continuous toFun
  apply₀ : toFun ⟨t₀, NNReal.mem_Icc_sub_add⟩ = x₀
  mem_closedBall : ∀ {t : Icc (t₀ - b) (t₀ + b)}, toFun t ∈ closedBall x₀ r

namespace FunSpace

section
variable {E : Type u} [NormedAddCommGroup E] {t₀ : ℝ} {x₀ : E} {r b : ℝ≥0}

-- ContractingWith.fixedPoint need Nonempty (FunSpace t₀ x₀ r b)
#check ContractingWith.fixedPoint
instance : Inhabited (FunSpace t₀ x₀ r b) :=
  ⟨fun _ ↦ x₀, continuous_const, rfl, mem_closedBall_self r.2⟩

@[coe]
noncomputable def compProj (α : FunSpace t₀ x₀ r b) : ℝ → E :=
  fun t ↦ α.toFun (projIcc (t₀-b) (t₀+b) NNReal.sub_le_self_add t)

noncomputable instance : CoeFun (FunSpace t₀ x₀ r b) fun _ ↦ ℝ → E :=
  ⟨fun α ↦ compProj α⟩

lemma coe_apply {α : FunSpace t₀ x₀ r b} {t : ℝ} :
  α t = α.toFun (projIcc (t₀-b) (t₀+b) NNReal.sub_le_self_add t) := rfl

@[simp]
lemma coe_val {α : FunSpace t₀ x₀ r b} {t : Icc (t₀-b) (t₀+b)} :
  α t = α.toFun t := by rw [coe_apply, projIcc_val]

@[simp]
lemma coe_of_mem {α : FunSpace t₀ x₀ r b} {t : ℝ} (ht : t ∈ Icc (t₀-b) (t₀+b)) :
  α t = α.toFun ⟨t, ht⟩ := by rw [coe_apply, projIcc_of_mem _ ht]

@[continuity, fun_prop]
lemma coe_continuous (α : FunSpace t₀ x₀ r b) : Continuous α :=
  α.continuous.comp continuous_projIcc

lemma coe_apply₀ (α : FunSpace t₀ x₀ r b) : α t₀ = x₀ := by
  rw [coe_of_mem]
  exact α.apply₀

lemma coe_mem_closedBall (α : FunSpace t₀ x₀ r b) {t : ℝ} : α t ∈ closedBall x₀ r := by
  rw [coe_apply]
  exact α.mem_closedBall

def toContinuousMap : FunSpace t₀ x₀ r b ↪ C(Icc (t₀ - b) (t₀ + b), E) :=
  ⟨fun α ↦ ⟨α.toFun, α.continuous⟩, fun α β h ↦ by simp at h; exact FunSpace.ext h⟩

@[simp]
lemma toContinuousMap_apply_eq_apply (α : FunSpace t₀ x₀ r b) (t : Icc (t₀ - b) (t₀ + b)) :
    α.toContinuousMap t = α t := by rw [coe_val]; rfl

noncomputable instance : MetricSpace (FunSpace t₀ x₀ r b) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x₀ r b ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap :
    range (fun α : FunSpace t₀ x₀ r b ↦ α.toContinuousMap) =
      { α : C(Icc (t₀-b) (t₀+b), E) |
        α ⟨t₀, NNReal.mem_Icc_sub_add⟩ = x₀
        ∧ ∀ {t : Icc (t₀ - b) (t₀ + b)}, α t ∈ closedBall x₀ r} := by
  ext α
  constructor
  · rintro ⟨α, rfl⟩
    refine ⟨?_, ?_⟩
    . dsimp
      rw [toContinuousMap_apply_eq_apply, Subtype.coe_mk]
      exact α.coe_apply₀
    . exact α.mem_closedBall
  · rintro ⟨hα1, hα2⟩
    refine ⟨⟨α, ?_, ?_, ?_⟩, rfl⟩
    . exact α.2
    . exact hα1
    . exact hα2

instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x₀ r b) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply IsClosed.inter
  . apply isClosed_eq
    . fun_prop -- #check Continuous.eval
    . fun_prop
  rw [setOf_forall]
  refine isClosed_iInter (fun t ↦ ?_)
  simp_rw [mem_closedBall_iff_norm]
  exact isClosed_le (by fun_prop) continuous_const

theorem dist_eq_toContinuousMap_dist {α β : FunSpace t₀ x₀ r b} :
  dist α β = dist α.toContinuousMap β.toContinuousMap := by
    rw [← MetricSpace.isometry_induced FunSpace.toContinuousMap FunSpace.toContinuousMap.injective
    |>.dist_eq]

#check ContinuousMap.dist_le
theorem dist_le {α β : FunSpace t₀ x₀ r b} {C : ℝ} (C0 : 0 ≤ C) :
  dist α β ≤ C ↔ ∀ t : Icc (t₀-b) (t₀+b), dist (α t) (β t) ≤ C := by
  rw [dist_eq_toContinuousMap_dist]
  convert ContinuousMap.dist_le C0
  <;> rw [toContinuousMap_apply_eq_apply]

#check ContinuousMap.dist_apply_le_dist
theorem dist_apply_le_dist {α β : FunSpace t₀ x₀ r b} (t : Icc (t₀-b) (t₀+b)) :
  dist (α t) (β t) ≤ dist α β := by
  exact (dist_le (C := dist α β) dist_nonneg).1 (le_refl _) t

end



section
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {t₀ : ℝ} {x₀ x y : E} {a r L M b : ℝ≥0}

lemma continuousOn_comp_coe
  (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
  (α : FunSpace t₀ x₀ r b)
  : ContinuousOn (fun t' ↦ f t' (α t')) (Icc (t₀-b) (t₀+b)) := by
  apply continuousOn_comp (u := closedBall x₀ r)
  . apply hf.continuousOn.mono
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨?_, hx⟩
    have : (b : ℝ) ≤ a := hf.ineq.1
    refine Icc_subset_Icc ?_ ?_ ht
    . linarith
    . linarith
  . exact α.coe_continuous.continuousOn
  . intro _ _
    exact α.coe_mem_closedBall

/-- The integrand in `next` is integrable. -/
lemma intervalIntegrable_comp_coe
    (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
    (α : FunSpace t₀ x₀ r b) (t₁ t₂ : Icc (t₀-b) (t₀+b)) :
    IntervalIntegrable (fun t' ↦ f t' (α t')) volume t₁ t₂ := by
  apply ContinuousOn.intervalIntegrable
  apply α.continuousOn_comp_coe hf |>.mono
  refine uIcc_subset_Icc ?_ ?_
  . exact t₁.2
  . exact t₂.2

#check ContinuousOn.comp_continuous
#check intervalIntegral.continuousOn_primitive_interval'
#check intervalIntegral.continuousOn_primitive_interval
#check intervalIntegral.continuousOn_primitive_Icc
#check ODE.FunSpace.next
noncomputable def next
  (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
  (α : FunSpace t₀ x₀ r b) : FunSpace t₀ x₀ r b where
  toFun t := picard f t₀ x₀ α t
  continuous := by
    suffices ContinuousOn (picard f t₀ x₀ α) (Icc (t₀ - b) (t₀ + b)) by
      show Continuous (picard f t₀ x₀ α ∘ Subtype.val)
      apply this.comp_continuous continuous_subtype_val (fun t ↦ t.2)
    apply continuousOn_const.add
    convert intervalIntegral.continuousOn_primitive_interval' (b₁ := t₀ - b) (b₂ := t₀ + b) _ _ using 1
    . apply uIcc_of_le _ |>.symm
      exact NNReal.sub_le_self_add
    . exact Real.noAtoms_volume --?
    . let tmin : Icc (t₀-b) (t₀+b) := ⟨t₀-b, ⟨by rfl, NNReal.sub_le_self_add⟩⟩
      let tmax : Icc (t₀-b) (t₀+b) := ⟨t₀+b, ⟨NNReal.sub_le_self_add, by rfl⟩⟩
      exact α.intervalIntegrable_comp_coe hf tmin tmax
    . rw [uIcc_of_le NNReal.sub_le_self_add]
      exact NNReal.mem_Icc_sub_add
  apply₀ := picard_apply₀
  mem_closedBall {t} := by
    rw [mem_closedBall_iff_norm, picard_apply, add_sub_cancel_left]
    calc ‖∫ (τ : ℝ) in t₀..t, f τ (α τ)‖
      _ ≤ M * |t - t₀| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t' ht'
        apply hf.norm_le
        . refine mem_of_subset_of_mem ?_ ht'
          calc uIoc t₀ t
            _ ⊆ uIcc t₀ t := uIoc_subset_uIcc
            _ ⊆ Icc (t₀-b) (t₀+b) := uIcc_subset_Icc NNReal.mem_Icc_sub_add t.2
            _ ⊆ Icc (t₀-a) (t₀+a) := by
              have : (b : ℝ) ≤ a := hf.ineq.1
              apply Icc_subset_Icc <;> linarith
        . apply coe_mem_closedBall
      _ ≤ M * b := by gcongr; rw [abs_sub_comm, mem_Icc_iff_abs_le]; exact t.2
      _ ≤ r := hf.ineq.2.1


@[simp]
lemma next_apply (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
    (α : FunSpace t₀ x₀ r b) {t : Icc (t₀-b) (t₀+b)} :
    next hf α t = picard f t₀ x₀ α t := by rw [coe_val]; rfl

lemma next_apply₀ (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
    (α : FunSpace t₀ x₀ r b) : next hf α t₀ = x₀ := by
      rw [coe_of_mem NNReal.mem_Icc_sub_add]
      exact picard_apply₀

#check ODE.FunSpace.dist_iterate_next_iterate_next_le
theorem dist_next_next_le
  (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
  (α β : FunSpace t₀ x₀ r b)
  : dist (next hf α) (next hf β) ≤ L * b * dist α β := by
  rw [dist_le]
  . intro t
    rw [next_apply, next_apply, dist_eq_norm,
        picard, picard, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub]
    calc
      _ ≤ L * dist α β * |t - t₀| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t' ht'
        have ht' : t' ∈ Icc (t₀-b) (t₀+b) :=
          uIcc_subset_Icc NNReal.mem_Icc_sub_add t.2 (uIoc_subset_uIcc ht')
        trans L * ‖α t' - β t'‖
        . have : t' ∈ Icc (t₀-a) (t₀+a) := by
            have : (b : ℝ) ≤ a := hf.ineq.1
            refine (Icc_subset_Icc ?_ ?_ ht')
            <;> linarith
          apply (hf.LipschitzOnWith t' this).norm_sub_le
          <;> apply coe_mem_closedBall
        . gcongr
          rw [← dist_eq_norm, ← Subtype.coe_mk t' ht']
          apply dist_apply_le_dist ⟨t', ht'⟩
      _ ≤ L * dist α β * b := by gcongr; rw [abs_sub_comm, mem_Icc_iff_abs_le]; exact t.2
      _ = L * b * dist α β := by ring_nf
    . exact α.intervalIntegrable_comp_coe hf ⟨t₀, NNReal.mem_Icc_sub_add⟩ t
    . exact β.intervalIntegrable_comp_coe hf ⟨t₀, NNReal.mem_Icc_sub_add⟩ t
  . positivity

theorem contractingWith_next (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
  : ∃ C : ℝ≥0, ContractingWith C (next hf) :=
  ⟨L * b ,⟨hf.ineq.2.2, LipschitzWith.of_dist_le_mul (dist_next_next_le hf)⟩⟩

theorem exists_isFixedPt_next [CompleteSpace E]
  (hf : MyIsPicardLindelof f t₀ x₀ a r M L b)
  : ∃ α : FunSpace t₀ x₀ r b, IsFixedPt (next hf) α := by
  have ⟨C, hC⟩ := contractingWith_next hf
  exact ⟨_, hC.fixedPoint_isFixedPt⟩
end

end FunSpace


section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

#check ODE.hasDerivWithinAt_picard_Icc
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `picard f t₀ x₀ α`. -/
lemma hasDerivWithinAt_picard_Icc
    (ht₀ : t₀ ∈ Icc tmin tmax)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (picard f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_comp hf hα hmem |>.mono
  by_cases h : t < t₀
  · rw [uIcc_of_gt h]
    exact Icc_subset_Icc ht.1 ht₀.2
  · rw [uIcc_of_le (not_lt.mp h)]
    exact Icc_subset_Icc ht₀.1 ht.2

end

end MyODE

#check csSup_le
#check le_csSup
#check IsCompact.bddAbove
#check IsCompact.exists_bound_of_continuousOn
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
theorem picard_theorem
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {a r L : ℝ} (apos : a > 0) (rpos : r > 0) (Lpos : L > 0)
  {x₀ : E} {t₀ : ℝ} {f : ℝ → E → E}
  (continuousOn : ContinuousOn (uncurry f) (Icc (t₀ - a) (t₀ + a) ×ˢ closedBall x₀ r))
  (LipschitzOnWith : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith ⟨L, Lpos.le⟩ (f t) (closedBall x₀ r))
  : ∃ b > 0, ∃ α : ℝ → E, α t₀ = x₀
    ∧ ∀ t ∈ Icc (t₀ - b) (t₀ + b), HasDerivWithinAt α (f t (α t)) (Icc (t₀ - b) (t₀ + b)) t := by
    let K := Icc (t₀ - a) (t₀ + a) ×ˢ closedBall x₀ r
    have : IsCompact K := isCompact_Icc.prod (isCompact_closedBall x₀ r) -- need FiniteDimensional ℝ E
    have hfK : IsCompact ((‖uncurry f .‖) '' K) := IsCompact.image_of_continuousOn this continuousOn.norm
    let M := sSup ((‖uncurry f .‖) '' K)
    have M_nonneg : M ≥ 0 := by
      have : ‖f t₀ x₀‖ ∈ (‖uncurry f .‖) '' K :=
        ⟨⟨t₀,x₀⟩, ⟨Real.mem_Icc_sub_add apos.le, mem_closedBall_self rpos.le⟩, rfl⟩
      have := le_csSup hfK.bddAbove this
      exact (norm_nonneg _).trans this
    have hM :  ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ x ∈ closedBall x₀ r, ‖f t x‖ ≤ M := by
      intro t ht x hx
      apply le_csSup hfK.bddAbove
      exact ⟨⟨t,x⟩, ⟨ht,hx⟩, rfl⟩
    have ⟨b,bpos,ineq⟩ : ∃ b > 0, b ≤ a ∧ M * b ≤ r ∧ L * b < 1 := by
      have ineq1 : ∀ᶠ b in 𝓝[>] (0 : ℝ), b > 0 := self_mem_nhdsWithin
      have ineq2 : ∀ᶠ b in 𝓝[>] 0, b ≤ a := mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds apos)
      have ineq3 : ∀ᶠ b in 𝓝[>] 0, M * b ≤ r := by
        by_cases M0 : M = 0
        . simp only [M0, zero_mul, rpos.le, Filter.eventually_true]
        . apply Filter.Eventually.mono (p := (. ≤ r / M))
          . refine mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ?_)
            field_simp [lt_of_le_of_ne' M_nonneg M0]
            linarith
          . have M0 : M > 0 := lt_of_le_of_ne' M_nonneg M0
            intro x hx
            rwa [← le_div_iff₀' M0]
      have ineq4 : ∀ᶠ b in 𝓝[>] 0, L * b < 1 := by
        apply Filter.Eventually.mono (p := (. < 1 / L))
        . refine mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ?_)
          simp [Lpos]
        . intro x hx
          rwa [← lt_div_iff₀' Lpos]
      exact (ineq1.and <| ineq2.and <| ineq3.and ineq4).exists
    have hf : MyIsPicardLindelof f t₀ x₀ ⟨a,apos.le⟩ ⟨r,rpos.le⟩ ⟨M, M_nonneg⟩ ⟨L,Lpos.le⟩ ⟨b,bpos.le⟩ :=
      ⟨continuousOn, hM, fun {t} ↦ LipschitzOnWith t, ineq⟩

    have ⟨α, hα⟩ := MyODE.FunSpace.exists_isFixedPt_next hf
    refine ⟨b, bpos, α, ?_, fun t ht ↦ ?_⟩
    . exact α.coe_apply₀
    have : HasDerivWithinAt (MyODE.picard f t₀ x₀ α) (f t (α t)) (Icc (t₀-b) (t₀+b)) t := by
      apply MyODE.hasDerivWithinAt_picard_Icc (u := closedBall x₀ r)
      . apply Real.mem_Icc_sub_add bpos.le
      . apply hf.continuousOn.mono
        intro ⟨t, x⟩ ⟨ht, hx⟩
        refine ⟨?_, hx⟩
        apply mem_of_subset_of_mem _ ht
        have : b ≤ a := hf.ineq.1
        simp only [NNReal.coe_mk]
        apply Icc_subset_Icc <;> linarith
      . apply α.coe_continuous.continuousOn
      . intro t ht; apply α.coe_mem_closedBall
      . exact ht
    apply this.congr_of_mem _ ht
    intro t ht
    rw [← Subtype.coe_mk t ht, ← MyODE.FunSpace.next_apply hf, hα]
