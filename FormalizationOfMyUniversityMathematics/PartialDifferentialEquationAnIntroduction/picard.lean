import Mathlib.Analysis.ODE.PicardLindelof

open Metric Set ODE Filter
open scoped Nat NNReal Topology BoundedContinuousFunction
/-
euler method to prove exist of solution of ode
u~(t)- f(t,uh(t))l = lf(ti,xi)- f(t,uh(t))l
~ lf(ti,xi)- f(t,xi)l + lf(t,xi)- f(t,uh(t))l
~ It- tiiP + luh(t)- xiiK
~hP+hMK
=h(P+MK) =ch·


f'(t) = v(t, f(t))
tᵢ₊₁ = tᵢ + h
u(tᵢ₊₁) = u(tᵢ) + h * v(tᵢ, u(tᵢ))
for t ∈ [tᵢ, tᵢ₊₁)
  u(t) = u(tᵢ) + (t - tᵢ) * v(tᵢ, u(tᵢ))
  u'(t) = v(tᵢ, u(tᵢ)) (right deriv)

hv :
  v(t, .) is lip by K for all t
  v(., x) is lip by P for all x
  v is bound by M

use hv to show ‖u'(t) - v(t, u(t))‖ ≤ ε
for t ∈ [tᵢ, tᵢ₊₁)
  ‖u'(t) - v(t, u(t))‖
  = ‖v(tᵢ, u(tᵢ)) - v(t, u(t))‖
  ≤ ‖v(tᵢ, u(tᵢ)) - v(tᵢ, u(t))‖ + ‖v(tᵢ, u(t)) - v(t, u(t))‖
  ≤ K * ‖u(tᵢ) - u(t)‖ + P * ‖tᵢ - t‖
  = K * ‖u(tᵢ) - (u(tᵢ) + (t - tᵢ) * v(tᵢ, u(tᵢ)))‖ + P * ‖tᵢ - t‖
  = K * ‖(t - tᵢ) * v(tᵢ, u(tᵢ)))‖ + P * ‖tᵢ - t‖
  ≤ K * M * ‖t - tᵢ‖ + P * ‖tᵢ - t‖
  ≤ K * M * h + P * h
  ≤ (K * M + P) * h


for t ∈ [tᵢ, tᵢ₊₁)
  ‖u'(t) - v(t, u(t))‖
  = ‖v(tᵢ, u(tᵢ)) - v(t, u(t))‖
  ≤ ‖v(tᵢ, u(tᵢ)) - v(tᵢ, u(t))‖ + ‖v(tᵢ, u(t)) - v(t, u(t))‖
  ≤ K * ‖u(tᵢ) - u(t)‖ + P * ‖tᵢ - t‖
  = K * ‖u(tᵢ) - (u(tᵢ) + (t - tᵢ) * v(tᵢ, u(tᵢ)))‖ + P * ‖tᵢ - t‖
  = K * ‖(t - tᵢ) * v(tᵢ, u(tᵢ)))‖ + P * ‖tᵢ - t‖
  ≤ K * M * ‖t - tᵢ‖ + P * ‖tᵢ - t‖
  ≤ K * M * h + P * h
  ≤ (K * M + P) * h

-/

#check IsPicardLindelof

example : IsPicardLindelof
  (E := ℝ) (f := fun _ x ↦ x)
  (tmin := -1) (tmax := 1) (t₀ := ⟨0, by simp⟩)
  (x₀ := 0) (a := 1) (r := 0)
  (K := 1) (L := 1) where
  lipschitzOnWith:= by
    intro t hx
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    dsimp
    rw [one_mul]
  continuousOn := by
    intro x hx
    exact continuousOn_const
  norm_le := by
    intro t ht x hx
    dsimp at hx ⊢
    have : |x - 0| ≤ 1 := hx
    convert this
    ring
  mul_max_le := by
    dsimp
    ring_nf
    apply max_le <;> rfl

example : IsPicardLindelof
  (E := ℝ) (f := fun _ x ↦ x)
  (tmin := -1) (tmax := 1) (t₀ := ⟨0, by simp⟩)
  (x₀ := 0) (a := 1) (r := 0)
  (K := 1) (L := 1) where
  lipschitzOnWith t hx := by simp [LipschitzOnWith]
  continuousOn x hx := continuousOn_const
  norm_le t ht x hx := mem_closedBall_zero_iff.mp hx
  mul_max_le := by simp


#check ODE.contDiffOn_comp


#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#check IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
#check ContDiffAt.exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt
#check ODE.FunSpace.compProj

#check ODE.FunSpace

/-
lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
ODE.picard f t₀ x₀ α t = x₀ + ∫ (τ : ℝ) in t₀..t, f τ (α τ)

α is lip by L
f(t, .) is lip by K

β := x₀ + ∫ (τ : ℝ) in t₀..t, f τ (α τ)
is β lip? by?

‖β t - β t'‖
= ‖∫ (τ : ℝ) in t'..t, f τ (α τ)‖
≤ ∫ (τ : ℝ) in t'..t, ‖f τ (α τ)‖
if f is bound by L
≤ ∫ (τ : ℝ) in t'..t, L
= |t - t'| * L

it say
if f is bound by L then
∀ α, picard f t₀ x₀ α t ∈ FunSpace t₀ x₀ r L
-/

#check ODE.picard_apply

#check ODE.FunSpace.instInhabited
#check ODE.FunSpace.toContinuousMap

example
  [NormedAddCommGroup E] {x₀ : E} {t₀ : Icc tmin tmax}
  : FunSpace t₀ x₀ r L where
    toFun := fun _ ↦ x₀
    lipschitzWith := LipschitzWith.const' x₀
    mem_closedBall₀ := mem_closedBall_self r.2

example
  [NormedAddCommGroup E] {x₀ : E} {t₀ : Icc tmin tmax}
  : FunSpace t₀ x₀ r L where
    toFun := fun _ ↦ x₀
    lipschitzWith := by
      rw [lipschitzWith_iff_dist_le_mul, dist_self]
      intros
      exact mul_nonneg L.2 dist_nonneg
    mem_closedBall₀ := by
      rw [mem_closedBall, dist_self]
      exact r.2

#check zero_le
example (L : ℝ≥0) : 0 ≤ L := zero_le L
#synth CanonicallyOrderedAdd ℝ≥0

def my_toContinuousMap
  {E : Type u} [NormedAddCommGroup E] {tmin tmax : ℝ}
  {t₀ : ↑(Icc tmin tmax)} {x₀ : E} {r L : ℝ≥0}
  : FunSpace t₀ x₀ r L ↪ C(↑(Icc tmin tmax), E) where
    toFun := fun ⟨α,lip,_⟩ ↦ {
      toFun := α
      continuous_toFun := lip.continuous
    }
    inj' := by
      intro ⟨α,_,_⟩ ⟨β,_,_⟩ h
      simp only [ContinuousMap.mk.injEq] at h
      simp only [FunSpace.mk.injEq]
      exact h

#check FunSpace.instMetricSpace
#check MetricSpace.induced
#check ContinuousMap.instMetricSpace
#check BoundedContinuousFunction.instMetricSpace
#check BoundedContinuousFunction.dist_le
#check BoundedContinuousFunction.dist_lt_iff_of_nonempty_compact
#check ContinuousMap.dist_le
#check ContinuousMap.dist_lt_iff_of_nonempty
example
  (t₀ : Icc tmin tmax) (x₀ : ℝ)
  (f g : FunSpace t₀ x₀ r L)
  (hc : 0 ≤ C)
  : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  have h1 : dist f g = dist f.toContinuousMap g.toContinuousMap := rfl
  have h2 : ∀ x, dist (f x) (g x) = dist (f.toContinuousMap x) (g.toContinuousMap x) := fun _ ↦ rfl
  simp only [h1, h2]
  apply ContinuousMap.dist_le hc
example
  (t₀ : Icc tmin tmax) (x₀ : ℝ)
  (f g : FunSpace t₀ x₀ r L)
  : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  have h1 : dist f g = dist f.toContinuousMap g.toContinuousMap := rfl
  have h2 : ∀ x, dist (f x) (g x) = dist (f.toContinuousMap x) (g.toContinuousMap x) := fun _ ↦ rfl
  have h3 : Nonempty (Icc tmin tmax) := ⟨t₀.1, t₀.2⟩
  simp only [h1, h2]
  apply ContinuousMap.dist_le_iff_of_nonempty

#check FunSpace.isUniformInducing_toContinuousMap
#check FunSpace.range_toContinuousMap
#check FunSpace.instCompleteSpace
-- #check ContinuousMap.instCompleteSpace
#check BoundedContinuousFunction.instCompleteSpace
#check cauchySeq_iff
#check cauchySeq_tendsto_of_complete
#check CompleteSpace.complete


#check le_of_tendsto
theorem my_le_of_tendsto_of_LinearOrder
  {α : Type u} {β : Type v} [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α]
  {f : β → α} {a b : α} {x : Filter β} [x.NeBot]
  (lim : Tendsto f x (𝓝 a))
  (h : ∀ᶠ (c : β) in x, f c ≤ b)
  : a ≤ b := by
  -- have : (f . ≤ b) ∈ x := h
  -- have : (. ≤ b) ∈ x.map f := this
  -- have : x.map f ≤ 𝓝 a := lim
  by_contra!
  have : ∀ᶠ a' in 𝓝 a, b < a' := Ioi_mem_nhds this
  have : ∀ᶠ c in x, b < f c := lim this
  have ⟨c, hc1, hc2⟩:= (this.and h).exists
  exact lt_irrefl _ (hc1.trans_le hc2)

theorem my_le_of_tendsto
  {α : Type u} {β : Type v} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
  {f : β → α} {a b : α} {x : Filter β} [x.NeBot]
  (lim : Tendsto f x (𝓝 a))
  (h : ∀ᶠ (c : β) in x, f c ≤ b)
  : a ≤ b := by
  have : IsClosed (Iic b) := isClosed_Iic
  have : ∃ᶠ fc in 𝓝 a, fc ≤ b := by
    refine lim.frequently_map f ?_ h.frequently
    intros
    assumption'
  have ha : a ∈ closure (Iic b) := by
    apply mem_closure_iff_frequently.mpr this
  have : closure (Iic b) = Iic b := isClosed_Iic.closure_eq
  rw [this] at ha
  exact ha

#check BoundedContinuousFunction.instCompleteSpace
theorem my_BoundedContinuousFunction_instCompleteSpace
  {α : Type u} {β : Type v} [TopologicalSpace α] [PseudoMetricSpace β]
  [CompleteSpace β]
  : CompleteSpace (α →ᵇ β) :=
  complete_of_cauchySeq_tendsto fun (f : ℕ → α →ᵇ β) (hf : CauchySeq f) => by
    /- We have to show that `f n` converges to a bounded continuous function.
      For this, we prove pointwise convergence to define the limit, then check
      it is a continuous bounded function, and then check the norm convergence. -/
    have ⟨b, b0, b_bound, b_lim⟩ := cauchySeq_iff_le_tendsto_0.1 hf
    have f_bdd := fun x n m N hn hm => (BoundedContinuousFunction.dist_coe_le_dist x).trans (b_bound n m N hn hm)
    have fx_cau : ∀ x, CauchySeq fun n => f n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, f_bdd x, b_lim⟩
    choose F hF using fun x => cauchySeq_tendsto_of_complete (fx_cau x)
    /- `F : α → β`, `hF : ∀ (x : α), Tendsto (fun n ↦ ↑(f n) x) atTop (𝓝 (F x))`
      `F` is the desired limit function. Check that it is uniformly approximated by `f N`. -/
    have fF_bdd : ∀ x N, dist (f N x) (F x) ≤ b N := by
      intro x N
      have dist_lim : Tendsto (fun n ↦ dist (f N x) (f n x)) atTop (𝓝 (dist (f N x) (F x))) := by
        exact tendsto_const_nhds.dist (hF x)
      have dist_bdd : ∀ᶠ n in atTop, dist (f N x) (f n x) ≤ b N := by
        rw [eventually_atTop]
        exact ⟨N, fun n hn ↦ f_bdd x N n N (by rfl) hn ⟩
      exact le_of_tendsto dist_lim dist_bdd
    refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
    · -- Check that `F` is continuous, as a uniform limit of continuous functions
      have : TendstoUniformly (fun n x => f n x) F atTop := by
        rw [Metric.tendstoUniformly_iff]
        intro ε ε0
        have hbε : ∀ᶠ n in atTop, b n < ε := b_lim (Iio_mem_nhds ε0)
        apply hbε.mono
        intro n hn x
        rw [dist_comm]
        exact (fF_bdd x n).trans_lt hn
      exact this.continuous (Eventually.of_forall fun N => (f N).continuous)
    · -- Check that `F` is bounded
      rcases (f 0).bounded with ⟨C, hC⟩
      refine ⟨b 0 + C + b 0, fun x y => ?_⟩
      calc
        dist (F x) (F y)
        _ ≤ dist (F x) (f 0 x) + dist (f 0 x) (f 0 y) + dist (f 0 y) (F y) := dist_triangle4 _ _ _ _
        _ ≤ b 0 + C + b 0 := by
          gcongr
          . rw [dist_comm]
            apply fF_bdd
          . apply hC
          . apply fF_bdd
    · -- Check that `F` is close to `f N` in distance terms
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (g := b)
      . intro; exact dist_nonneg
      . intro n
        rw [BoundedContinuousFunction.dist_le (b0 n)]
        intro x
        exact fF_bdd x n
      . exact b_lim

#check  ODE.FunSpace.continuous_compProj

#check FunSpace.mem_closedBall
theorem my_mem_closedBall
  {E : Type u} [NormedAddCommGroup E] {tmin tmax : ℝ}
  {t₀ : Icc tmin tmax} {x₀ : E} {a r L : ℝ≥0} {α : FunSpace t₀ x₀ r L}
  (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r)
  {t : Icc tmin tmax} :
  α t ∈ closedBall x₀ a := by
  calc dist (α t) (x₀)
    _ ≤ dist (α t) (α t₀) + dist (α t₀) x₀ := dist_triangle _ _ _
    _ ≤ L * dist t t₀ + r := by
      gcongr
      . exact α.lipschitzWith.dist_le_mul t t₀
      . exact α.mem_closedBall₀
    _ ≤ L * max (tmax - t₀) (t₀ - tmin) + r := by
      gcongr
      apply abs_sub_le_max_sub t.2.1 t.2.2
    _ ≤ a - r + r := by gcongr
    _ = a := by ring

#check FunSpace.continuousOn_comp_compProj

#check FunSpace.next
/-
next (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (α : FunSpace t₀ x₀ r L) : FunSpace t₀ x₀ r L where
  toFun t := picard f t₀ x α.compProj t
  -/
#check picard_apply
#check intervalIntegral.norm_integral_le_of_norm_le_const
#check intervalIntegral.norm_integral_le_integral_norm
#check intervalIntegral.norm_integral_le_abs_integral_norm
noncomputable def my_next
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof f t₀ x₀ a r L K)
  (hx : x ∈ closedBall x₀ ↑r)
  (α : FunSpace t₀ x₀ r L)
  : FunSpace t₀ x₀ r L where
  toFun t := picard f t₀ x α.compProj t
  lipschitzWith := by
    simp_rw [lipschitzWith_iff_dist_le_mul, dist_eq_norm]
    intro t₁ t₂
    calc ‖picard f t₀ x α.compProj t₁ - picard f t₀ x α.compProj t₂‖
      _ = ‖(x + ∫ τ in t₀..t₁, f τ (α.compProj τ)) - (x + ∫ τ in t₀..t₂, f τ (α.compProj τ))‖ := by
        rw [picard_apply, picard_apply]
      _ = ‖(∫ τ in t₀..t₁, f τ (α.compProj τ)) - (∫ τ in t₀..t₂, f τ (α.compProj τ))‖ := by
        simp only [add_sub_add_left_eq_sub]
      _ = ‖∫ τ in t₂..t₁, f τ (α.compProj τ)‖ := by
        rw [intervalIntegral.integral_interval_sub_left]
        . apply α.intervalIntegrable_comp_compProj hf
        . apply α.intervalIntegrable_comp_compProj hf
      _ ≤ L * |(t₁ : ℝ) - t₂| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        apply hf.norm_le
        . have := uIcc_subset_Icc t₂.2 t₁.2
          exact this <| uIoc_subset_uIcc ht
        . apply α.mem_closedBall hf.mul_max_le
      _ = L * dist (t₁ : ℝ) t₂ := by
        simp only [dist_eq_norm, Real.norm_eq_abs]
  mem_closedBall₀ := by rwa [picard_apply₀]


#check ODE.FunSpace.dist_comp_iterate_next_le



/-

lemma dist_comp_iterate_next_le (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) (t : Icc tmin tmax)
    {α β : FunSpace t₀ x₀ r L}
    (h : dist ((next hf hx)^[n] α t) ((next hf hx)^[n] β t) ≤
      (K * |t - t₀.1|) ^ n / n ! * dist α β) :
    dist (f t ((next hf hx)^[n] α t)) (f t ((next hf hx)^[n] β t)) ≤
      K ^ (n + 1) * |t - t₀.1| ^ n / n ! * dist α β :=


for all t ∈ [tmin, tmax]
αₙ := next ^[n] α
d(αₙ(t), βₙ(t)) ≤ (K * |t - t₀|) ^ n / n! * d(α, β)
d(α₁(t), β₁(t)) ≤ K * |t - t₀| * d(α, β)

d(f(t, αₙ(t)), f(t, βₙ(t))) ≤ K ^ (n + 1) * |t - t₀| ^ n / n! * d(α, β)

d(αₙ(t), βₙ(t)) ≤ K'(t)
d(f(t, αₙ(t)), f(t, βₙ(t))) ≤ K * K'(t)

d(f(t, α(t)), f(t, β(t))) ≤ K * d(α(t), β(t))


d(α₁(t), β₁(t))
  ≤ d( ∫ τ in t₀..t, f(t, α(t)), ∫ τ in t₀..t, f(t, β(t)))
  = ‖ (∫ τ in t₀..t, f(t, α(t))) - (∫ τ in t₀..t, f(t, β(t)))‖
  = ‖∫ τ in t₀..t, (f(t, α(t)) - f(t, β(t)))‖
    since ‖(f(t, α(t)) - f(t, β(t)))‖ ≤ K * d(α(t), β(t)) ≤ K * d(α, β) is const
  ≤ |t - t₀| * K * d(α, β)

d(α₂(t), β₂(t))
  ≤ d( ∫ τ in t₀..t, f(t, α₁(t)), ∫ τ in t₀..t, f(t, β₁(t)))
  = ‖ (∫ τ in t₀..t, f(t, α₁(t))) - (∫ τ in t₀..t, f(t, β₁(t)))‖
  = ‖∫ τ in t₀..t, (f(t, α₁(t)) - f(t, β₁(t)))‖
    since ‖(f(t, α₁(t)) - f(t, β₁(t)))‖ ≤ K * d(α₁(t), β₁(t)) ≤ K * |t - t₀| * K * d(α, β)
  ≤ |∫ τ in t₀..t, K * |τ - t₀| * K * d(α, β)|
  ≤ K ^ 2 * d(α, β) * |∫ τ in t₀..t, |τ - t₀||
  = K ^ 2 * d(α, β) * ∫ τ in uIoc t₀ t, |τ - t₀|
  = K ^ 2 * d(α, β) * |t - t₀| ^ 2 / 2
  = (K * |t - t₀|) ^ 2 / 2 * d(α, β)

-/
#check integral_pow_abs_sub_uIoc

#check IsPicardLindelof.lipschitzOnWith
#check FunSpace.dist_iterate_next_apply_le
#check intervalIntegral.integral_mono
#check intervalIntegral.norm_integral_le_integral_norm
#check MeasureTheory.norm_integral_le_of_norm_le_const

#check (∀ᵐ _ ∂_, _)
#check intervalIntegral.norm_integral_le_of_norm_le
#check intervalIntegral.norm_integral_le_abs_integral_norm
#check intervalIntegral.norm_integral_le_abs_of_norm_le
#check intervalIntegral.norm_integral_le_of_norm_le_const
#check intervalIntegral.integral_mono
#check intervalIntegral.abs_integral_mono_interval
#check MeasureTheory.integral_mono_of_nonneg
#check MeasureTheory.norm_integral_le_of_norm_le
#check MeasureTheory.norm_integral_le_of_norm_le_const

#check mem_nhdsWithin_iff_eventually
example [TopologicalSpace α] {s t : Set α} {x : α}
  : (∀ᶠ y in 𝓝[t] x, y ∈ s) ↔ (∀ᶠ y in 𝓝 x, y ∈ t → y ∈ s) := by
  exact mem_nhdsWithin_iff_eventually



-- prove n=0,1,2 of dist_iterate_next_apply_le
#check FunSpace.dist_iterate_next_apply_le


theorem my_dist_iterate_next_apply_le_0
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof f t₀ x₀ a r L K)
  (hx : x ∈ closedBall x₀ ↑r)
  (α β : FunSpace t₀ x₀ r L)
  (n : ℕ) (t : ↑(Icc tmin tmax))
  (hn : n = 0):
  dist (((FunSpace.next hf hx)^[n] α).toFun t) (((FunSpace.next hf hx)^[n] β).toFun t) ≤
    (K * |(t : ℝ) - t₀|) ^ n / n ! * dist α β := by
  subst hn
  simp
  rw [← FunSpace.toContinuousMap_apply_eq_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply]
  exact ContinuousMap.dist_apply_le_dist t

theorem my_dist_iterate_next_apply_le_1
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof f t₀ x₀ a r L K)
  (hx : x ∈ closedBall x₀ ↑r)
  (α β : FunSpace t₀ x₀ r L)
  (n : ℕ) (t : ↑(Icc tmin tmax))
  (hn : n = 1):
  dist (((FunSpace.next hf hx)^[n] α).toFun t) (((FunSpace.next hf hx)^[n] β).toFun t) ≤
    (K * |(t : ℝ) - t₀|) ^ n / n ! * dist α β := by
  subst hn
  simp [-FunSpace.compProj_apply]
  calc
    _ = ‖(∫ τ in t₀..t, f τ (α.compProj τ)) - (∫ τ in t₀..t, f τ (β.compProj τ))‖ := by
      rw [dist_eq_norm]
    _ = ‖∫ τ in t₀..t, f τ (α.compProj τ) - f τ (β.compProj τ)‖ := by
      rw [intervalIntegral.integral_sub]
      . apply α.intervalIntegrable_comp_compProj hf
      . apply β.intervalIntegrable_comp_compProj hf
    _ ≤ (K * dist α β) * |(t : ℝ) - t₀| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      replace hs : s ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hs)
      calc
        _ ≤ K * ‖α.compProj s - β.compProj s‖ := by
          apply (hf.lipschitzOnWith s hs).norm_sub_le
          . apply α.mem_closedBall hf.mul_max_le
          . apply β.mem_closedBall hf.mul_max_le
        _ ≤ K * dist α β := by
          gcongr
          rw [← dist_eq_norm,
            α.compProj_of_mem hs, β.compProj_of_mem hs,
            ← α.toContinuousMap_apply_eq_apply,
            ← β.toContinuousMap_apply_eq_apply]
          apply ContinuousMap.dist_apply_le_dist
    _ = K * |(t : ℝ) - t₀| * dist α β := by ring_nf

#check MeasureTheory.ae
#check MeasureTheory.ae_restrict_eq
theorem my_dist_iterate_next_apply_le_2
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof f t₀ x₀ a r L K)
  (hx : x ∈ closedBall x₀ ↑r)
  (α β : FunSpace t₀ x₀ r L)
  (n : ℕ) (t : ↑(Icc tmin tmax))
  (hn : n = 2):
  dist (((FunSpace.next hf hx)^[n] α).toFun t) (((FunSpace.next hf hx)^[n] β).toFun t) ≤
    (K * |(t : ℝ) - t₀|) ^ n / n ! * dist α β := by
  subst hn
  simp [-FunSpace.compProj_apply]
  calc
    _ = ‖(∫ τ in t₀..t, f τ ((FunSpace.next hf hx α).compProj τ))
       - (∫ τ in t₀..t, f τ ((FunSpace.next hf hx β).compProj τ))‖ := by
      rw [dist_eq_norm]
    _ = ‖∫ τ in t₀..t, f τ ((FunSpace.next hf hx α).compProj τ)
                     - f τ ((FunSpace.next hf hx β).compProj τ)‖ := by
      rw [intervalIntegral.integral_sub]
      . apply FunSpace.intervalIntegrable_comp_compProj hf
      . apply FunSpace.intervalIntegrable_comp_compProj hf
    _ ≤ |∫ τ in t₀..t, K ^ 2 * dist α β * (|τ - t₀|)| := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      rw [MeasureTheory.ae_restrict_iff']
      apply Eventually.of_forall
      intro s hs
      replace hs : s ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 (uIoc_subset_uIcc hs)
      calc
        _ ≤ K * ‖(FunSpace.next hf hx α).compProj s
               - (FunSpace.next hf hx β).compProj s‖ := by
          apply (hf.lipschitzOnWith s hs).norm_sub_le
          . apply FunSpace.mem_closedBall hf.mul_max_le
          . apply FunSpace.mem_closedBall hf.mul_max_le
        _ ≤ K * (K * |s - t₀| * dist α β) := by
          gcongr
          have := my_dist_iterate_next_apply_le_1 hf hx α β 1 (⟨s, hs⟩ : Icc tmin tmax) (by rfl)
          simp only [Function.iterate_one,
            pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
          rwa [← dist_eq_norm,
            FunSpace.compProj_of_mem hs, FunSpace.compProj_of_mem hs]
        _ = K ^ 2 * dist α β * |s - t₀| := by ring
      . exact measurableSet_Ioc
      . apply ContinuousOn.intervalIntegrable
        fun_prop
    _ = K ^ 2 * dist α β * (|(t : ℝ) - t₀| ^ 2 / 2) := by
      rw [intervalIntegral.integral_const_mul, abs_mul]
      congr
      . simp [mul_nonneg]
      . conv => lhs; pattern (|_ - _|); rw [← pow_one (|x - t₀|)]
        rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc,
          integral_pow_abs_sub_uIoc]
        convert abs_eq_self.2 _
        . norm_num
        . infer_instance
        . positivity
    _ = (K * |(t : ℝ) - t₀|) ^ 2 / 2 * dist α β := by ring

#check exists_between
#synth DenselyOrdered ℝ

#check Function.IsFixedPt
/-
A : fun x ↦ α,
hA : ∀ x, Function.IsFixedPt (next hf hx) (A x)
∃ L, A is lip with L on Ball(x₀, r)

∀ α, d(x, y) = d(next(α, x), next(α, y))

d(A(x), A(y)) ≤ L d(x, y)

∀ᶠ n in atTop,
d(A(x), A(y))
≤ d(A(x), next^[n](α, x))
  + d(next^[n](α, x), α)
  + d(α, next^[n](α, y))
  + d(next^[n](α, y), A(y))
≤ ε
  + K' * d(next(α, x), α)
  + K' * d(next(α, y), α)
  ε
≤ 2 * ε + K' * (d(next(α, x), α) + d(next(α, y), α))
-- pick α = A(x)
≤ 2 * ε + K' * (d(next(A(x), x), A(x)) + d(next(A(x), y), A(x)))
≤ 2 * ε + K' * (0 + d(next(A(x), y), next(A(x), x)))
≤ 2 * ε + K' * d(x, y)

-/

#check FunSpace.dist_next_next
#check FunSpace.dist_iterate_next_le
#check FunSpace.dist_iterate_iterate_next_le_of_lipschitzWith
#check FunSpace.exists_forall_closedBall_funSpace_dist_le_mul
#check FunSpace.exists_isFixedPt_next
#check summable_pow_mul_geometric_of_norm_lt_one
theorem my_exists_forall_closedBall_funSpace_dist_le_mul
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ : E} {a r L K : ℝ≥0}
  [CompleteSpace E]
  (hf : IsPicardLindelof f t₀ x₀ a r L K)
  (K' : ℝ≥0)
  (fixedPt_iterate_next_bound : ∀ x (hx : x ∈ closedBall x₀ r) Ax α,
    Function.IsFixedPt (FunSpace.next hf hx) Ax
    → ∀ ε > 0, ∀ᶠ n in atTop, dist Ax ((FunSpace.next hf hx)^[n] α) ≤ ε)
  (iterate_next_self_bound : ∀ x (hx : x ∈ closedBall x₀ r), ∀ n, ∀ α,
      dist ((FunSpace.next hf hx)^[n] α) α ≤ K' * dist (FunSpace.next hf hx α) α )
  :
  ∃ L',
    ∀ (x y : E) (hx : x ∈ closedBall x₀ ↑r) (hy : y ∈ closedBall x₀ ↑r)
    (α β : FunSpace t₀ x₀ r L),
    Function.IsFixedPt (FunSpace.next hf hx) α →
    Function.IsFixedPt (FunSpace.next hf hy) β →
    dist α β ≤ ↑L' * dist x y := by
  use K'
  intro x y hx hy α β hα hβ
  suffices ∀ ε > 0, dist α β ≤ K' * dist x y + ε by
    apply le_of_forall_pos_le_add this
  intro ε hε
  have := half_pos hε
  have ⟨n, ineq1, ineq2⟩: ∃ n,
    dist α ((FunSpace.next hf hx)^[n] α) ≤ ε/2
    ∧ dist ((FunSpace.next hf hy)^[n] α) β ≤ ε/2 := by
    have h1 := fixedPt_iterate_next_bound x hx α α hα _ (half_pos hε)
    have h2 := fixedPt_iterate_next_bound y hy β α hβ _ (half_pos hε)
    simp_rw [dist_comm _ β]
    exact (h1.and h2).exists
  calc dist α β
    _ ≤ dist α ((FunSpace.next hf hx)^[n] α)
        + dist ((FunSpace.next hf hx)^[n] α) ((FunSpace.next hf hy)^[n] α)
        + dist ((FunSpace.next hf hy)^[n] α) β := dist_triangle4 _ _ _ _
    _ ≤ (ε/2) + dist ((FunSpace.next hf hx)^[n] α) ((FunSpace.next hf hy)^[n] α) + (ε/2) := by
      gcongr
    _ = ε + dist ((FunSpace.next hf hx)^[n] α) ((FunSpace.next hf hy)^[n] α) := by ring
    _ ≤ ε + (dist ((FunSpace.next hf hx)^[n] α) α
          + dist α ((FunSpace.next hf hy)^[n] α)) := by
      gcongr
      apply dist_triangle
    _ ≤ ε + (K' * dist (FunSpace.next hf hx α) α
          + K' * dist (FunSpace.next hf hy α) α) := by
      gcongr
      . apply iterate_next_self_bound
      . rw [dist_comm]; apply iterate_next_self_bound
    _ = ε + (K' * 0
        + K' * dist (FunSpace.next hf hy α) (FunSpace.next hf hx α)) := by
      have : dist (FunSpace.next hf hx α) α = 0 := by
        rw [dist_eq_zero]
        exact hα
      rw [this]
      conv => rhs; pattern (FunSpace.next _ hx α); rw [hα]
    _ = ε + K' * dist (FunSpace.next hf hy α) (FunSpace.next hf hx α) := by ring
    _ = ε + K' * dist x y := by
      rw [FunSpace.dist_next_next, dist_comm]
    _ = K' * dist x y + ε := by ring


#check hasDerivWithinAt_picard_Icc
#check intervalIntegral.FTCFilter


/-
class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) : Prop
    extends TendstoIxxClass Ioc outer inner where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]


pure a ≤ outer
f ⊆ pure a
s ∈ outer → s ∈ pure a
s ∈ outer → a ∈ s
(∀ᶠ x in outer, x ∈ s) → a ∈ s

inner ≤ 𝓝 a
𝓝 a ⊆ inner
s ∈ 𝓝 a → s ∈ inner
(∀ᶠ x in 𝓝 a, x ∈ s) → (∀ᶠ x in inter, x ∈ s)
-/

example [TopologicalSpace α] (a : α) : pure a ≤ 𝓝 a := by
  exact Specializes.pure_le_nhds fun ⦃U⦄ a ↦ a
example [TopologicalSpace α] (a : α) : pure a ≤ 𝓝 a := by
  show ∀ s ∈ 𝓝 a, a ∈ s
  intro s hs
  rw [_root_.mem_nhds_iff] at hs
  have ⟨t, hts, ht, hat⟩ := hs
  exact hts hat
example [MetricSpace α] (a b : α) : pure a ≤ 𝓝 b ↔ a = b := by
  show (∀ s ∈ 𝓝 b, a ∈ s) ↔ a = b
  constructor
  . intro h
    by_contra!
    have : dist a b > 0 := dist_pos.2 this
    have : ball b (dist a b) ∈ 𝓝 b := ball_mem_nhds b this
    have := h _ this
    have : dist a b < dist a b := this
    linarith
  . rintro rfl
    intro s hs
    rw [_root_.mem_nhds_iff] at hs
    have ⟨t, hts, ht, hat⟩ := hs
    exact hts hat
example [MetricSpace α] (a b : α) : pure a ≤ 𝓝 b ↔ a = b := by
  exact pure_le_nhds_iff
example [MetricSpace α] : T1Space α := inferInstance

example (a : ℝ) : 𝓝[<] a ≤ 𝓝[≤] a ∧ 𝓝[≤] a ≤ 𝓝 a := by
  constructor
  . refine nhdsWithin_mono a ?_
    exact Iio_subset_Iic_self
  . exact nhdsWithin_le_nhds

example (a : ℝ) (s : Set ℝ) : pure a ≤ 𝓝[s] a ↔ a ∈ s := by
  constructor
  . intro h
    apply h
    exact self_mem_nhdsWithin
  . intro h
    apply pure_le_nhdsWithin h
example : 𝓝[Ici 1] (0 : ℝ) = ⊥ := by
  rw [eq_bot_iff]
  show ∀ s, s ∈ univ → s ∈ 𝓝[Ici 1] 0
  rintro s -
  rw [mem_nhdsWithin_iff]
  refine ⟨1/2, one_half_pos, ?_⟩
  intro x ⟨h1, h2⟩
  have : |x| < 1/2 := by rwa [mem_ball_zero_iff] at h1
  have : x < 1/2 := (le_abs_self _).trans_lt this
  have : 1 ≤ x := h2
  linarith

example : (𝓝[Ioi 0] (0 : ℝ)).NeBot := by
  exact nhdsGT_neBot 0

#check ClusterPt
#check mem_closure_iff_clusterPt
#check mem_closure_iff_nhdsWithin_neBot


#check IsPicardLindelof.of_time_independent
lemma my_of_time_independent
  {E : Type u} [NormedAddCommGroup E]
  {f : E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ : E} {a r L K : ℝ≥0}
  (hb : ∀ x ∈ closedBall x₀ ↑a, ‖f x‖ ≤ ↑L)
  (hl : LipschitzOnWith K f (closedBall x₀ ↑a))
  (hm : ↑L * max (tmax - ↑t₀) (↑t₀ - tmin) ≤ ↑a - ↑r) :
  IsPicardLindelof (fun _ ↦ f) t₀ x₀ a r L K where
    lipschitzOnWith _ _ := hl
    continuousOn _ _ := continuousOn_const
    norm_le _ _ := hb
    mul_max_le := hm

#check IsPicardLindelof.of_contDiffAt_one
-- lemma of_contDiffAt_one [NormedSpace ℝ E]
--     {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
--     ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r), IsPicardLindelof (fun _ ↦ f)
--       (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
--   -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
--   obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
--   obtain ⟨a, ha : 0 < a, has⟩ := Metric.mem_nhds_iff.mp hs
--   set L := K * a + ‖f x₀‖ + 1 with hL
--   have hL0 : 0 < L := by positivity
--   have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
--     rw [hL]
--     calc
--       ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_le_norm_sub_add _ _
--       _ ≤ K * ‖x - x₀‖ + ‖f x₀‖ := by
--         gcongr
--         rw [← dist_eq_norm, ← dist_eq_norm]
--         apply hl.dist_le_mul x _ x₀ (mem_of_mem_nhds hs)
--         apply subset_trans _ has hx
--         exact closedBall_subset_ball <| half_lt_self ha -- this is where we need `a / 2`
--       _ ≤ K * a + ‖f x₀‖ := by
--         gcongr
--         rw [← mem_closedBall_iff_norm]
--         exact closedBall_subset_closedBall (half_le_self (le_of_lt ha)) hx
--       _ ≤ L := le_add_of_nonneg_right zero_le_one
--   let ε := a / L / 2 / 2
--   have hε0 : 0 < ε := by positivity
--   refine ⟨ε, hε0,
--     ⟨a / 2, le_of_lt <| half_pos ha⟩, ⟨a / 2, le_of_lt <| half_pos ha⟩ / 2,
--     ⟨L, le_of_lt hL0⟩, K, half_pos <| half_pos ha, ?_⟩
--   apply of_time_independent hb <|
--     hl.mono <| subset_trans (closedBall_subset_ball (half_lt_self ha)) has
--   rw [NNReal.coe_mk, add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_div,
--     NNReal.coe_two, NNReal.coe_mk, mul_comm, ← le_div_iff₀ hL0, sub_half, div_right_comm (a / 2),
--     div_right_comm a]

theorem my_of_contDiffAt_one
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {x₀ : E}
  (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ)
  : ∃ ε, ∃ (hε : 0 < ε), ∃ a r L K, ∃ (_ : 0 < r),
    IsPicardLindelof (fun _ ↦ f)
    (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, (by simp [le_of_lt hε])⟩ x₀ a r L K := by
  -- Obtain ball of radius `a` within the domain in which f is `K`-lipschitz
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith

  have ⟨L, hL⟩ := exists_gt ‖f x₀‖
  have hL0 : L > 0 := (norm_nonneg (f x₀)).trans_lt hL
  have := hf.continuousAt.norm.eventually (Iio_mem_nhds hL)
  obtain ⟨a, ha : 0 < a, has'⟩ := Metric.mem_nhds_iff.mp (this.and hs)
  have has : ball x₀ a ⊆ s := fun x hx ↦ (has' hx).2
  have hb (x : E) (hx : x ∈ closedBall x₀ (a / 2)) : ‖f x‖ ≤ L := by
    have : x ∈ ball x₀ a := lt_of_le_of_lt hx (half_lt_self ha)
    exact (has' this).1.le

  let ε := a / L / 2 / 2
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0,
    ⟨a / 2, le_of_lt <| half_pos ha⟩, ⟨a / 2, le_of_lt <| half_pos ha⟩ / 2,
    ⟨L, le_of_lt hL0⟩, K, half_pos <| half_pos ha, ?_⟩
  apply IsPicardLindelof.of_time_independent hb <|
    hl.mono <| subset_trans (closedBall_subset_ball (half_lt_self ha)) has
  rw [NNReal.coe_mk, add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_div,
    NNReal.coe_two, NNReal.coe_mk, mul_comm, ← le_div_iff₀ hL0, sub_half, div_right_comm (a / 2),
    div_right_comm a]


#check IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#check IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀


#check IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard
theorem my_exists_eq_forall_mem_Icc_eq_picard
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
  : ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax, α t = picard f t₀ x α t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx

  refine ⟨α.compProj, ?_, fun t ht ↦ ?_⟩
  . rw [← hα]; simp
  . nth_rw 1 [← hα, FunSpace.compProj_apply, FunSpace.next_apply, projIcc_of_mem _ ht];



/-

α'(t) = f(t, α(t)), α(t₀) = x₀
P(α)(t) = x₀ + ∫ τ in t₀..t, f(τ, α(τ))
‖P(α)(t) - P(β)(t)‖
= ‖∫ τ in t₀..t, f(τ, α(τ)) - f(τ, β(τ))‖
≤ ∫ τ in t₀..t, ‖f(τ, α(τ)) - f(τ, β(τ))‖
≤ ∫ τ in t₀..t, K * ‖α(τ) - β(τ)‖
≤ ∫ τ in t₀..t, K * ‖α - β‖
= (t - t₀) * K * ‖α - β‖
let t₁ - t₀ small the (t-t₀) * K ≤ (t₁-t₀) * K < 1

‖P^[n+1](α)(t) - P^[n+1](β)(t)‖
≤ ∫ τ in t₀..t, K * ‖P^[n](α)(τ) - P^[n](β)(τ)‖
≤ ∫ τ in t₀..t, K * B(n)(τ)
≤ B(n + 1)(t)

B(0)(t) = ‖α - β‖
B(n + 1)(t) = ∫ τ in t₀..t, K * B(n)(τ)
→ B(1)(t) = (t - t₀) * K * ‖α - β‖
→ B(2)(t) = K ^ 2 * ‖α - β‖ * (t - t₀)^2 / 2
→ B(3)(t) = K ^ 3 * ‖α - β‖ * (t - t₀)^3 / 3!
→ ...
→ B(n)(t) = K ^ n * ‖α - β‖ * (t - t₀)^n / n!

‖P^[n](α)(t) - P^[n](β)(t)‖
≤ K ^ n * ‖α - β‖ * (t - t₀)^n / n!
→ ‖P^[n](α) - P^[n](β)‖
≤ (K * (t₁ - t₀))^n / n! * ‖α - β‖ → 0 < 1
→ ∃ m, ‖P^[m](α) - P^[m](β)‖ < C * ‖α - β‖, where 0 ≤ C < 1




-/
#check abs_le_abs
#check intervalIntegral.abs_integral_eq_abs_integral_uIoc
#check intervalIntegral.abs_integral_le_integral_abs
#check intervalIntegral.norm_integral_le_abs_integral_norm
