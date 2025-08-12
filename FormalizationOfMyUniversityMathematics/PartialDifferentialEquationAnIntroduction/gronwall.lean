import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
-- import Mathlib.Analysis.Calculus.Deriv.MeanValue


open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

-- #check exists_deriv_eq_slope
#check image_le_of_deriv_right_lt_deriv_boundary'
#check image_le_of_deriv_right_lt_deriv_boundary
-- #check image_le_of_deriv_right_le_deriv_boundary'
#check image_le_of_deriv_right_le_deriv_boundary
#check image_norm_le_of_norm_deriv_right_lt_deriv_boundary
#check image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
#check image_norm_le_of_norm_deriv_right_le_deriv_boundary
#check image_norm_le_of_norm_deriv_right_le_deriv_boundary'



#check IsClosed.mem_of_ge_of_forall_exists_gt
#check IsClosed.Icc_subset_of_forall_exists_gt
/-
IsClosed.Icc_subset_of_forall_exists_gt.{u}
{α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
{a b : α} {s : Set α}
(hs : IsClosed (s ∩ Icc a b))
(ha : a ∈ s)
(hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty)
: Icc a b ⊆ s
-/
#check BddAbove
#check sSup_def
#check IsLUB.frequently_mem
#check exists_isLUB
#check csSup_le
#check le_csSup
#check IsClosed.csSup_mem
theorem my_Icc_subset_of_forall_exists_gt
  {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a b : α} {s : Set α}
  (hs : IsClosed (s ∩ Icc a b))
  (ha : a ∈ s)
  (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty)
  : Icc a b ⊆ s := by
  /-
  let y ∈ [a, b]
  let t = s ∩ [a, y]
  have ht : IsClosed t
    s ∩ [a, y] = s ∩ [a, b] ∩ [a, y]
    IsClosed s ∩ [a, b]
    IsClosed [a, y]
    IsClosed_inter
  have ha₂ : a ∈ t
    a ∈ s
    a ∈ [a, y]
  have bound : BddAbove t
    z ∈ t → z ∈ [a, y] → z ≤ y
  let c := sSup t
  have hct : c ∈ t := IsClosed.csSup_mem
  have c_le : c ≤ y := csSup_le
  case c = y
    y = c ∈ t ⊆ s
    y ∈ s
    done
  case c < y
    let z, (hz : z ∈ s, c < z ≤ y) := hgt c ⟨c ∈ s, c ∈ [a, b]⟩ y (y > c)
    z ∈ t
    z ≤ c := le_csSup
    contradition
  -/
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

#check ContinuousWithinAt.closure_le
#check hasDerivWithinAt_Ioi_iff_Ici
#check hasDerivWithinAt_iff_tendsto
#check hasDerivWithinAt_iff_tendsto_slope
#check hasDerivWithinAt_iff_tendsto_slope'
#check tendsto_iff_forall_eventually_mem
#check Filter.Eventually.of_forall
#check Filter.Eventually.eq_1
/-
  let ε > 0
  let g(x) := f(x) + ε * (x - a)
  then
    g(a) = f(a) ≥ 0
    g(b) = f(b) + ε * (b - a) < f(b) (have a < b else x ∈ [a, b] is false)
    g is conti on [a, b]
    g'(x) = f'(x) + ε > 0 (where g' is right deriv of f)
  to use Icc_subset_of_forall_exists_gt
  s := {x ∈ [a, b] | 0 ≤ g x}
  have IsClosed (s ∩ [a, b]) since
    s ∩ [a, b] = s
    preimage of closed [0, ⊤) under conti func g is closed
  have a ∈ s since a ∈ [a, b] and ∀ y, y ∈ [a, a] → y = a → g y = g a ≥ 0
  have ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty
    let x ∈ s, a ≤ x < b, x < y
    show ∃ z, z ∈ s and x < z ≤ y
    since x ∈ s => 0 ≤ g(x)
    x ∈ [a, b] => g'(x) > 0
    by def of g' > 0
    ∀ᶠ z ∈ 𝓝[>] x, g(z) > g(x) ≥ 0
    since (x, y) ∈ 𝓝[>] x
      ∃ z ∈ (x, y), g(z) ≥ 0
      → z ∈ s and x < z ≤ y
  by Icc_subset_of_forall_exists_gt
    ∀ x ∈ [a, b], x ∈ s
    i.e g x ≥ 0
  now notice
    0 ≤ g x = f(x) + ε (b - a) holds for all ε > 0
    => 0 ≤ f(x) by some lemma? (ContinuousWithinAt.closure_le)
  -/
theorem my_image_le_of_deriv_right_le_deriv_boundary_aux
  {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  (ha : 0 ≤ f a)
  (bound : ∀ x ∈ Ico a b, 0 ≤ f' x)
  ⦃x : ℝ⦄
  : x ∈ Icc a b → 0 ≤ f x := by
  intro hx
  suffices ∀ ε > 0, 0 ≤ f x + ε * (x - a) by
    convert ContinuousWithinAt.closure_le (f := 0) (g := fun ε ↦ f x + ε * (x - a)) (x := 0) (s := Ioi 0) _ _ _ _ using 1
    . ring
    . simp only [closure_Ioi, mem_Ici, le_refl]
    . exact continuousWithinAt_const
    . apply Continuous.continuousWithinAt
      fun_prop
    . exact this

  intro ε εpos
  let g x := f x + ε * (x - a)
  let g' x := f' x + ε
  have hg : ContinuousOn g (Icc a b) := by fun_prop
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ici x) x := by
    intro x hx
    unfold g g'
    convert (hf' x hx).add (((hasDerivWithinAt_id _ _).sub_const _).const_mul _) using 1
    . ring
  have ha₂ : 0 ≤ g a := by
    unfold g; linarith
  have bound₂ : ∀ x ∈ Ico a b, 0 < g' x := by
    unfold g'; intro x hx; linarith [bound x hx]

  let s := {x | 0 ≤ g x}
  have hs : IsClosed (s ∩ Icc a b) := by
    rw [inter_comm]
    apply hg.preimage_isClosed_of_isClosed
    . exact isClosed_Icc
    . exact isClosed_Ici
  have has : a ∈ s := ha₂

  have hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty := by
    intro x ⟨hxs, hxab⟩ y hyx
    have hg'x := hg' x hxab
    rw [← hasDerivWithinAt_Ioi_iff_Ici,
      hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi_self),
      tendsto_iff_forall_eventually_mem] at hg'x
    have mem_nhd : Ioi 0 ∈ 𝓝 (g' x) := by
      exact Ioi_mem_nhds (bound₂ x hxab)
    have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < slope g x z := hg'x _ mem_nhd
    have nhd₂ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
    have ⟨z, z_slope, hxz, hzy⟩ := (nhd₁.and nhd₂).exists
    have hzs : 0 ≤ g z := by
      rw [slope_def_field, div_pos_iff_of_pos_right] at z_slope
      . have : 0 ≤ g x := hxs
        linarith
      linarith
    exact ⟨z, hzs, hxz, hzy⟩

  exact my_Icc_subset_of_forall_exists_gt hs has hgt hx



#check image_le_of_deriv_right_le_deriv_boundary
/-
image_le_of_deriv_right_le_deriv_boundary
{f f' : ℝ → ℝ} {a b : ℝ}
(hf : ContinuousOn f (Icc a b))
(hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
{B B' : ℝ → ℝ} (ha : f a ≤ B a)
(hB : ContinuousOn B (Icc a b))
(hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
(bound : ∀ x ∈ Ico a b, f' x ≤ B' x)
⦃x : ℝ⦄ :
x ∈ Icc a b → f x ≤ B x
-/
theorem my_image_le_of_deriv_right_le_deriv_boundary
  {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ}
  (ha : f a ≤ B a)
  (hB : ContinuousOn B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, f' x ≤ B' x)
  ⦃x : ℝ⦄
  : x ∈ Icc a b → f x ≤ B x := by
  -- exact my_image_le_of_deriv_right_le_deriv_boundary_aux (f := B - f)
  intro hx
  rw [← sub_nonneg]
  apply my_image_le_of_deriv_right_le_deriv_boundary_aux (a := a) (b := b) (f := B - f) (f' := B' - f')
  . exact hB.sub hf
  . exact fun x hx ↦ (hB' x hx).sub (hf' x hx)
  . dsimp; linarith
  . dsimp; exact fun x hx ↦ by linarith [bound x hx]
  exact hx

#check image_le_of_deriv_right_lt_deriv_boundary'
/-
image_le_of_deriv_right_lt_deriv_boundary'
{f f' : ℝ → ℝ} {a b : ℝ} {B B' : ℝ → ℝ}
(hf : ContinuousOn f (Icc a b))
(hB : ContinuousOn B (Icc a b))
(hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
(hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
(ha : f a ≤ B a)
(bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x)
⦃x : ℝ⦄
: x ∈ Icc a b → f x ≤ B x

solution of ode : u'(t) = v(t, u(t))
lower fence : α'(t) ≤ v(t, α(t))
have α(t) = u(t) → α'(t) < u'(t)
since α(t) = u(t)
  → α'(t) ≤ v(t, α(t)) = v(t, u(t)) = u'(t)
  → α'(t) ≤ u'(t)

-/

theorem my_image_le_of_deriv_right_lt_deriv_boundary'_aux
  {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  (ha : 0 ≤ f a)
  (bound : ∀ x ∈ Ico a b, 0 = f x → 0 < f' x)
  ⦃x : ℝ⦄
  : x ∈ Icc a b → 0 ≤ f x := by
  intro hx

  let s := {x | 0 ≤ f x}
  have hs : IsClosed (s ∩ Icc a b) := by
    rw [inter_comm]
    apply hf.preimage_isClosed_of_isClosed
    . exact isClosed_Icc
    . exact isClosed_Ici
  have has : a ∈ s := ha

  have hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty := by
    intro x ⟨hxs, hxab⟩ y hyx
    have : 0 ≤ f x := hxs
    obtain h | h := eq_or_lt_of_le this
    . have hf'x := hf' x hxab
      -- rw [← hasDerivWithinAt_Ioi_iff_Ici,
      --   hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi_self),
      --   tendsto_iff_forall_eventually_mem] at hf'x
      -- have mem_nhd : Ioi 0 ∈ 𝓝 (f' x) := by
      --   exact Ioi_mem_nhds (bound x hxab h)
      -- have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < slope f x z := hf'x _ mem_nhd
      have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < slope f x z := by
        apply (hasDerivWithinAt_iff_tendsto_slope' notMem_Ioi_self).1 hf'x.Ioi_of_Ici
        exact (Ioi_mem_nhds (bound x hxab h))
      have nhd₂ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
      have ⟨z, z_slope, hxz, hzy⟩ := (nhd₁.and nhd₂).exists
      have hzs : 0 ≤ f z := by
        rw [slope_def_field, div_pos_iff_of_pos_right] at z_slope
        . have : 0 ≤ f x := hxs
          linarith
        linarith
      exact ⟨z, hzs, hxz, hzy⟩
    . -- have nhd₁ : ∀ᶠ fz in 𝓝 (f x), 0 < fz := Ioi_mem_nhds h
      -- have : ContinuousOn f (Icc a b) := hf
      -- have : Ico x b ⊆ Icc a b := by
      --   intro z ⟨hxz, hzb⟩
      --   exact ⟨hxab.1.trans hxz, hzb.le⟩
      -- have : ContinuousOn f (Ico x b) := hf.mono this
      -- have : ContinuousWithinAt f (Ico x b) x := this x ⟨by rfl, hxab.2⟩
      -- have nhd₂ : ∀ᶠ z in 𝓝[Ico x b] x, 0 < f z := this.eventually nhd₁
      -- have nhd₃ : ∀ᶠ z in 𝓝[Ici x] x, 0 < f z := by
      --   rwa [nhdsWithin_Ico_eq_nhdsGE] at nhd₂
      --   exact hxab.2
      -- have nhd₄ : ∀ᶠ z in 𝓝[>] x, 0 < f z := by
      --   apply nhd₃.filter_mono
      --   apply nhdsWithin_mono
      --   simp only [Ioi_subset_Ici_iff, le_refl]


      -- have subset : Ioo x b ⊆ Icc a b := fun z ⟨hxz, hzb⟩ ↦ ⟨hxab.1.trans hxz.le, hzb.le⟩
      -- have conti : ContinuousWithinAt f (Ioo x b) x := by
      --   apply ContinuousWithinAt.mono _ subset
      --   apply hf.continuousWithinAt (Ico_subset_Icc_self hxab)
      -- have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < f z := by
      --   rw [← nhdsWithin_Ioo_eq_nhdsGT hxab.2]
      --   apply conti.eventually_const_lt h
      -- have nhd₂ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
      -- have ⟨z, fz_pos, hxz, hzy⟩ := (nhd₁.and nhd₂).exists
      -- exact ⟨z, fz_pos.le, hxz, hzy⟩


      -- have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < f z := by
      --   rw [← nhdsWithin_Ioo_eq_nhdsGT hxab.2]
      --   apply Filter.Tendsto.eventually_const_lt h
      --   apply Filter.Tendsto.mono_left (x := 𝓝[Icc a b] x)
      --   . exact hf.continuousWithinAt (Ico_subset_Icc_self hxab)
      --   . apply nhdsWithin_mono
      --     exact fun z ⟨hxz, hzb⟩ ↦ ⟨hxab.1.trans hxz.le, hzb.le⟩
      have nhd₁ : ∀ᶠ z in 𝓝[>] x, 0 < f z := by
        have := (hf x (Ico_subset_Icc_self hxab)).eventually_const_lt h
        rw [← nhdsWithin_Ioo_eq_nhdsGT hxab.2]
        apply this.filter_mono _
        apply nhdsWithin_mono
        refine' (Ioo_subset_Ioo_left hxab.1).trans (Ioo_subset_Icc_self)
      have nhd₂ : ∀ᶠ z in 𝓝[>] x, x < z ∧ z ≤ y := Ioc_mem_nhdsGT hyx
      have ⟨z, fz_pos, hxz, hzy⟩ := (nhd₁.and nhd₂).exists
      exact ⟨z, fz_pos.le, hxz, hzy⟩

  exact my_Icc_subset_of_forall_exists_gt hs has hgt hx

#check image_le_of_deriv_right_lt_deriv_boundary'
theorem my_image_le_of_deriv_right_lt_deriv_boundary'
  {f f' : ℝ → ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  {B B' : ℝ → ℝ}
  (ha : f a ≤ B a)
  (hB : ContinuousOn B (Icc a b))
  (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x)
  ⦃x : ℝ⦄ :
  x ∈ Icc a b → f x ≤ B x := by
  intro hx
  rw [← sub_nonneg]
  apply my_image_le_of_deriv_right_lt_deriv_boundary'_aux (a := a) (b := b) (f := B - f) (f' := B' - f')
  . exact hB.sub hf
  . exact fun x hx ↦ (hB' x hx).sub (hf' x hx)
  . dsimp; linarith
  . dsimp; intro x hx heq; linarith [bound x hx (by linarith [heq])];
  exact hx

#check image_le_of_deriv_right_le_deriv_boundary
theorem my_image_le_of_deriv_right_le_deriv_boundary_prove_by_lt
  {f f' : ℝ → ℝ} {a b : ℝ} {B B' : ℝ → ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hB : ContinuousOn B (Icc a b))
  (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (ha : f a ≤ B a)
  (bound : ∀ x ∈ Ico a b, f' x ≤ B' x)
  ⦃x : ℝ⦄
  : x ∈ Icc a b → f x ≤ B x := by
  intro hx
  suffices ∀ ε > 0, f x ≤ B x + ε * (x - a) by
    convert ContinuousWithinAt.closure_le (f := fun ε ↦ f x) (g := fun ε ↦ B x + ε * (x - a)) (x := 0) (s := Ioi 0) _ _ _ _ using 1
    . ring
    . simp only [closure_Ioi, mem_Ici, le_refl]
    . exact continuousWithinAt_const
    . apply Continuous.continuousWithinAt
      fun_prop
    . exact this
  intro ε εpos
  let A x := B x + ε * (x - a)
  let A' x := B' x + ε
  have hA : ContinuousOn A (Icc a b) := by fun_prop
  have hA' : ∀ x ∈ Ico a b, HasDerivWithinAt A (A' x) (Ici x) x := by
    unfold A A'
    intro x hx
    convert (hB' x hx).add (((hasDerivWithinAt_id _ _).sub_const _).const_mul _) using 1
    . ring
  have ha₂ : f a ≤ A a := by unfold A; linarith
  have bound₂ : ∀ x ∈ Ico a b, f x = A x → f' x < A' x := by
    intro x hx heq
    unfold A at heq
    unfold A'
    linarith [bound x hx]
  exact my_image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha₂ hA hA' bound₂ hx

#check image_le_of_deriv_right_lt_deriv_boundary'
#check image_norm_le_of_norm_deriv_right_lt_deriv_boundary'
#check Tendsto.norm
#check hasFDerivWithinAt_iff_tendsto
#check hasDerivWithinAt_iff_tendsto_slope'
#check tendsto_norm_sub_self
#check hasDerivAt_iff_tendsto_slope
#check hasDerivAt_iff_tendsto_slope_zero
#check HasDerivWithinAt.liminf_right_slope_norm_le
/-
[NormedAddCommGroup E] [NormedSpace ℝ E]
{f : ℝ → E} {f' : E} {x r : ℝ}
(hf : HasDerivWithinAt f f' (Ici x) x) (hr : ‖f'‖ < r)
: ∃ᶠ (z : ℝ) in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r

f'(x) (right deriv) exist
Tendsto (fun z ↦ (f(z) - f(x)) / (z - x)) (𝓝[≥] x) (𝓝 f'(x))
Tendsto (fun z ↦ ‖(f(z) - f(x)) / (z - x) - f'(x)‖ ) (𝓝[≥] x) (𝓝 0)
Tendsto (fun z ↦ slope f x z) (𝓝[≥] x) (𝓝 f'(x))
∀ ε > 0, ∀ᶠ z in 𝓝[≥] x, ‖(f(z) - f(x)) / (z - x) - f'(x)‖ < ε

f conti at x
Tendsto f (𝓝 x) (𝓝 (f x))

‖.‖ conti at x
Tendsto ‖.‖ (𝓝 f'(x)) (𝓝 ‖f'(x)‖ )
Iio B'(x) = (. < B'(x)) ∈ 𝓝 ‖f'(x)‖   <---- generalizing it
→ (‖.‖ < B'(x)) ∈ 𝓝 f'(x)

Tendsto (fun z ↦ slope f x z) (𝓝[≥] x) (𝓝 f'(x))
(‖.‖ < B'(x)) ∈ 𝓝 f'(x)
→ (‖fun z ↦ slope f x z‖ < B'(x)) ∈ (𝓝[≥] x)
↔ ∀ᶠ z in 𝓝[≥] x, ‖slope f x z‖ < B'(x)

let r > ‖f'(x)‖
→ (. < r) ∈ 𝓝 ‖f'(x)‖
Tendsto ‖.‖ (𝓝 f'(x)) (𝓝 ‖f'(x)‖ )
→ (‖.‖ < r) ∈ 𝓝 f'(x)
Tendsto (fun z ↦ slope f x z) (𝓝[≥] x) (𝓝 f'(x))
→ (‖slope f x .‖ < r) ∈ 𝓝[≥] x
↔ ∀ᶠ z in 𝓝[≥] x, ‖slope f x z‖ < r
→ ∃ᶠ z in 𝓝[≥] x, ‖slope f x z‖ < r
slope ‖f.‖ x z ≤ ‖slope f x z‖
→ ∃ᶠ z in 𝓝[≥] x, slope ‖f.‖ x z < r
have ∀ r, ‖f'(x)‖ < r → ∀ᶠ z in 𝓝[≥] x, ‖slope f x z‖ < r

slope ‖f .‖  x z
= ‖f z‖ - ‖f x‖ / (z - x)
≤ ‖f z - f x‖ / (z - x)
= ‖slope f x z‖



‖f'(x)‖ < r
-/

#check HasDerivWithinAt.limsup_norm_slope_le

theorem my_limsup_norm_slope_le
{E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
{f : ℝ → E} {f' : E} {s : Set ℝ} {x r : ℝ}
(hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
: ∀ᶠ (z : ℝ) in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r := by
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖slope f x z‖ < r :=
     (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (Iio_mem_nhds hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖slope f x z‖ < r := by
    have step1 : {x} ∈ 𝓝[{x}] x :=
      self_mem_nhdsWithin
    have step1' :  ∀ᶠ z in 𝓝[{x}] x, z ∈ ({x} : Set ℝ) :=
      self_mem_nhdsWithin
    have step1'' : ∀ᶠ z in 𝓝[{x}] x, z = x :=
      self_mem_nhdsWithin
    have step2 : ∀ z, z = x → ‖slope f x z‖ < r := by
      intro z hz
      simp only [hz, slope_same, norm_zero]
      exact (norm_nonneg _).trans_lt hr
    have step3 : ∀ᶠ z in 𝓝[{x}] x, ‖slope f x z‖ < r :=
      step1''.mono step2
    exact step3
    -- refine Filter.Eventually.mono self_mem_nhdsWithin (fun z hz ↦ ?_)
    -- have : z = x := hz
    -- simp [this]
    -- exact (norm_nonneg _).trans_lt hr
  have C : ∀ᶠ z in 𝓝[s] x, ‖slope f x z‖ < r := by
    have step1 : ∀ᶠ z in 𝓝[s \ {x}] x ⊔ 𝓝[{x}] x, ‖slope f x z‖ < r :=
      Filter.mem_sup.1 ⟨A, B⟩
    have step2 : ∀ᶠ z in 𝓝[s \ {x} ∪ {x}] x, ‖slope f x z‖ < r := by
      rw [nhdsWithin_union]
      exact step1
    have step3 : ∀ᶠ z in 𝓝[s ∪ {x}] x, ‖slope f x z‖ < r := by
      rw [← diff_union_self]
      exact step2
    have step4 : ∀ᶠ z in 𝓝[s] x, ‖slope f x z‖ < r := by
      apply step3.filter_mono
      apply nhdsWithin_mono
      simp only [union_singleton, subset_insert]
    have step4' : ∀ᶠ z in 𝓝[s] x, ‖slope f x z‖ < r := by
      apply step2.filter_mono
      apply nhdsWithin_mono
      -- simp only [union_singleton, insert_diff_singleton, subset_insert]
      apply subset_diff_union
    exact step4

  apply C.mono
  intro z hz
  convert hz
  simp [slope_def_module, norm_smul]


#check HasDerivWithinAt.limsup_norm_slope_le
#check HasDerivWithinAt.limsup_slope_norm_le
#check HasDerivWithinAt.liminf_right_norm_slope_le
#check HasDerivWithinAt.liminf_right_slope_norm_le
theorem my_limsup_slope_norm_le
{E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
{f : ℝ → E} {f' : E} {s : Set ℝ} {x r : ℝ}
(hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r)
: ∀ᶠ z in 𝓝[s \ {x}] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  have step1 : Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') :=
    hasDerivWithinAt_iff_tendsto_slope.1 hf
  have step2 : Tendsto (‖slope f x .‖) (𝓝[s \ {x}] x) (𝓝 ‖f'‖) :=
    step1.norm
  have step2'_1 : Tendsto (‖.‖) (𝓝 f') (𝓝 ‖f'‖) :=
    continuous_norm.continuousAt
  have step2'_2 : Tendsto (‖slope f x .‖) (𝓝[s \ {x}] x) (𝓝 ‖f'‖) :=
    fun t ht ↦ step1 (step2'_1 ht)
  have step2'_2' : Tendsto (‖slope f x .‖) (𝓝[s \ {x}] x) (𝓝 ‖f'‖) :=
    step2'_1.comp step1
  have step2'' : Tendsto (‖slope f x .‖) (𝓝[s \ {x}] x) (𝓝 ‖f'‖) :=
    continuous_norm.continuousAt.tendsto.comp step1
  have step3 : Iio r ∈ 𝓝 ‖f'‖ := Iio_mem_nhds hr
  have step3' : ∀ᶠ z in 𝓝 ‖f'‖, z < r := Iio_mem_nhds hr
  have step3'' : ∀ᶠ z in 𝓝 ‖f'‖, z < r := eventually_lt_nhds hr
  have step4 : (‖slope f x .‖) ⁻¹' Iio r ∈ 𝓝[s \ {x}] x :=
    step2 step3
  have step4' : ∀ᶠ z in 𝓝[s \ {x}] x, ‖slope f x z‖ < r :=
    step2 step3
  have step4'' : ∀ᶠ z in 𝓝[s \ {x}] x, ‖slope f x z‖ < r :=
    step2.eventually step3
  have step5 : ∀ z, ‖f z‖ - ‖f x‖ ≤ ‖f z - f x‖ := by
    intro z
    apply norm_sub_norm_le
  have step5_2 : ∀ z, |‖f z‖ - ‖f x‖| ≤ ‖f z - f x‖ := by
    intro z
    exact abs_norm_sub_norm_le (f z) (f x)
  have step6 : ∀ z, |slope (‖f .‖)| x z ≤  ‖slope f x z‖ := by
    intro z
    simp [slope_def_module, norm_smul, abs_mul, abs_inv]
    gcongr
    exact step5_2 z
  have step6_1 : ∀ z, slope (‖f .‖) x z ≤ ‖slope f x z‖ :=
    fun z ↦ (le_abs_self _).trans (step6 z)
  have step7 : ∀ᶠ z in 𝓝[s \ {x}] x, slope (‖f .‖) x z < r := by
    refine step4'.mono ?_
    intro z hz
    exact (step6_1 z).trans_lt hz
  have step7' : ∀ᶠ z in 𝓝[s \ {x}] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r :=
    step7
  exact step7'

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


#check gronwallBound
#check hasDerivAt_gronwallBound
#check hasDerivAt_gronwallBound_shift
#check rexp
#check exp
#check Real.exp
#check le_gronwallBound_of_liminf_deriv_right_le
#check liminf
#check norm_le_gronwallBound_of_norm_deriv_right_le
#check dist_le_of_trajectories_ODE
#check ODE_solution_unique_univ
#check gronwallBound_ε0
#check gronwallBound_x0
#check image_le_of_deriv_right_lt_deriv_boundary'
/-
let r > 0
g x = gronwallBound δ K (ε + r) (x - a)
g' x = K * g x + (ε + r)
g a = δ
g conti on [a, b]
‖f a‖ ≤ g a
‖f x‖ = g x →  ‖f' x‖ ≤ K * ‖f x‖ + ε = K * g x + ε < K * g x + (ε + r) = g' x

-/
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
  /-
  let h = f - g
  then
    1. h conti on [a, b]
    2. h'(t) = v(t, f(t)) - v(t, g(t)) for t ∈ [a, b)
    3. ‖h(a)‖ ≤ δ
   (where h' is the right deriv of h)
  need to show
    bound : ‖h' t‖ ≤ K * ‖h t‖ + ε for t ∈ [a, b)
  look for t ∈ [a, c)
    ‖h'(t)‖
    = ‖v(t, f(t)) - v(t, g(t))‖ (use 2.)
    ≤ K * ‖f(t) - g(t)‖ (use hv : ∀ (t : ℝ), LipschitzWith K (v t))
    = K * ‖h(t)‖
    = K * ‖h(t)‖ + 0 (choose ε = 0)
  by norm_le_gronwallBound_of_norm_deriv_right_le
  we have :  ∀ t ∈ [a, b], ‖h(t)‖ ≤ gronwallBound δ K 0 (t - a)
  thus for t ∈ [a, b]
    dist (f t) (g t)
    = ‖h(t)‖
    ≤ gronwallBound δ K 0 (t - a)
    = δ * exp (K * (t - a))
  qed
  -/
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

#check dist_le_zero
-- #check
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
  /-
  have dist(f(a), g(a)) ≤ 0 since f a = g a (use dist_le_zero)
  by my_dist_le_of_trajectories_ODE (δ := 0)
  we have
  dist (f t) (g t) ≤ 0 * exp (K * (t - a)) = 0
  thus f t = g t (use dist_le_zero)
  -/
  intro ht
  replace ha := dist_le_zero.mpr ha
  have h := my_dist_le_of_trajectories_ODE hv hf hf' hg hg' ha t ht
  rw [zero_mul] at h
  exact dist_le_zero.mp h

#check HasDerivAt.continuousOn
#check HasDerivAt.hasDerivWithinAt
theorem my_ODE_solution_unique_univ_aux_2
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {t₀ : ℝ}
  (hv : ∀ (t : ℝ), LipschitzWith K (v t))
  (hf : ∀ (t : ℝ), HasDerivAt f (v t (f t)) t)
  (hg : ∀ (t : ℝ), HasDerivAt g (v t (g t)) t)
  (heq : f t₀ = g t₀)
  (t : ℝ)
  : t₀ ≤ t → f t = g t := by
  /-
  let t₀ ≤ t
  since f is diff on ℝ, f is conti on [t, t₀] (use HasDerivAt.continuousOn)
  since f' = v(t, f(t)) on ℝ
    => left deriv of f = v(t, f(t)) on ℝ (use HasDerivAt.hasDerivWithinAt)
    => left deriv of f = v(t, f(t)) on [a, b)
  same for g.
  by my_ODE_solution_unique_univ_aux_1 (a := t₀) (b := t)
  we have ∀ t' ∈ [t₀, t], f t' = g t'
  inpaticular t ∈ [t₀, t], so f t = g t
  -/
  intro ht
  have hf₂ : ContinuousOn f (Icc t₀ t) :=
    HasDerivAt.continuousOn (fun t' _ ↦ hf t')
  have hf'₂ : ∀ t' ∈ Ico t₀ t, HasDerivWithinAt f (v t' (f t')) (Ici t') t' :=
    fun t' _ ↦ (hf t').hasDerivWithinAt
  have hg₂ : ContinuousOn g (Icc t₀ t) :=
    HasDerivAt.continuousOn (fun t' _ ↦ hg t')
  have hg'₂ : ∀ t' ∈ Ico t₀ t, HasDerivWithinAt g (v t' (g t')) (Ici t') t' :=
    fun t' _ ↦ (hg t').hasDerivWithinAt
  have h := my_ODE_solution_unique_univ_aux_1 hv hf₂ hf'₂ hg₂ hg'₂ heq
  exact h t (⟨ht, by rfl⟩)

#check le_or_gt
#check norm_neg
#check HasDerivAt.scomp
#check HasDerivAt.comp
theorem my_ODE_solution_unique_univ
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {t₀ : ℝ}
  (hv : ∀ (t : ℝ), LipschitzWith K (v t))
  (hf : ∀ (t : ℝ), HasDerivAt f (v t (f t)) t)
  (hg : ∀ (t : ℝ), HasDerivAt g (v t (g t)) t)
  (heq : f t₀ = g t₀)
  : f = g := by
  /-
  let t ∈ ℝ
  by cases t₀ ≤ t or t₀ > t (use le_or_gt)
  case 1, t₀ ≤ t => exact my_ODE_solution_unique_univ_aux_2
  case 2, t₀ > t
  let
    F(t') = f(-t')
    G(t') = g(-t')
    V(t', x) = -v(-t', x)
  then for t' ∈ ℝ
    F'(t')
    = - f'(-t')
    = - v(-t', f'(-t'))
    = - v(-t', F'(t') )
    = V(t', F'(t'))
    same for g
  check ∀ (t : ℝ), LipschitzWith K (V t)
    let t ∈ ℝ
    ‖V(t,x) - V(t,y)‖
    = ‖-v(-t, -x) - (-v(-t, -y))‖
    = ‖v(-t, -y) - v(-t, -x)‖
    ≤ K * ‖-y - (-x)‖
    = K * ‖x - y‖
  by my_ODE_solution_unique_univ_aux_2 (f := F) (g := G) (v := V) (t₀ := - t₀)
  we have -t₀ ≤ t → F t = G t, indeed t < t₀ so -t₀ < -t
  that is f t = F -t = G -t = g t
  qed
  -/
  ext t
  obtain ht | ht := le_or_gt t₀ t
  . apply my_ODE_solution_unique_univ_aux_2
    assumption'

  let F t' := f (-t')
  let G t' := g (-t')
  let V t' x := -(v (-t') x)
  have hF : ∀ (t : ℝ), HasDerivAt F (V t (F t)) t := by
    intro t
    unfold V F
    convert (hf _).scomp t (hasDerivAt_neg' t) using 1
    simp
  have hG : ∀ (t : ℝ), HasDerivAt G (V t (G t)) t := by
    intro t
    unfold V G
    convert (hg _).scomp t (hasDerivAt_neg' t) using 1
    simp
  have hV : ∀ (t : ℝ), LipschitzWith K (V t) := by
    intro t x y
    unfold V
    simp
    apply hv
  have heq' : F (-t₀) = G (-t₀) := by simp [heq, F, G]
  have h := my_ODE_solution_unique_univ_aux_2 hV hF hG heq'
  calc f t
    _ = F (-t) := by simp [F]
    _ = G (-t) := by apply h; linarith [ht]
    _ = g t := by simp [G]


/-
f'(t) = -1 if f(t)>0 else 0
f(0) = 10

v(t, x) = -1 if x>0 else 0

f'(t) = -√f(t)
v(t, x) = -√x

¬ (∃ K : ℝ≥0, LipschitzOnWith K (fun x ↦ -√x) [0, ⊤))
∀ δ > 0, ∃ K : ℝ≥0, LipschitzOnWith K (fun x ↦ -√x) [δ, ⊤)

-/

/-


f(g(x))'
= f'(g(x)) * g'(x)


= (f'(g(x)) * g'(x))'
= [f'(g(x))]' * g'(x) + f'(g(x)) * g''(x)
= [f''(g(x)) * g'(x)] * g'(x) + f'(g(x)) * g''(x)
= f''(g(x)) * g'(x) ^ 2 + f'(g(x)) * g''(x)

-/

/-

x' = ax + b, x(0)=x₀
case a = 0
  x' = b => x = b * t + c
  x(0) = b * 0 + c = c = x₀
  => x = b * t + x₀
case a ≠ 0
  x' = ax + b
  let x = y * exp(a * t)
  x' = y' * exp(a * t) + y * a * exp(a * t)
    = a * y * exp(a * t) + b
  => y' * exp(a * t) = b
  => y' = b * exp(-a * t)
  => y = (-b/a) * exp(-a * t) + c
  x(0) = y(0) * 1 = y(0) = x₀
  y(0) = (-b/a) * 1 + c = x₀
  => c = x₀ + b/a
  y = (-b/a) * exp(-a * t) + x₀ + b/a
    = (b/a) * (1 - exp(-a * t)) + x₀
  x = y * exp(a * t)
    = (b/a) * (exp(a * t) - 1) + x₀ * exp(a * t)


-/


#check LT.lt.exists_disjoint_Iio_Ioi
theorem my_filter_tendsto_eventually_lt
  {α : Type u} {γ : Type w} [TopologicalSpace α] [LinearOrder α]
  [OrderClosedTopology α] {l : Filter γ} {f g : γ → α} {y z : α}
  (hf : Tendsto f l (𝓝 y)) (hg : Tendsto g l (𝓝 z))
  (hyz : y < z) : ∀ᶠ (x : γ) in l, f x < g x := by
  have ⟨a,hay,b,hbz,ineq⟩ := hyz.exists_disjoint_Iio_Ioi
  have h1 : ∀ᶠ x in l, f x < a := hf (Iio_mem_nhds hay)
  have h2 : ∀ᶠ x in l, b < g x := hg (Ioi_mem_nhds hbz)
  apply h2.mp
  apply h1.mp
  apply Eventually.of_forall
  intro x hfa hbg
  exact ineq _ hfa _ hbg
