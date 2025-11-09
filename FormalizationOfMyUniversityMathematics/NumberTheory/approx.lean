import Mathlib.Analysis.AbsoluteValue.Equivalence



open Filter
open scoped Topology
#check AbsoluteValue.isEquiv_iff_lt_one_iff
#check map_inv₀
#check inv_lt_one₀
#check inv_inv
#check Archimedean
#check exists_pow_lt_of_lt_one
/-
exists_pow_lt_of_lt_one.{u_4} {K : Type u_4}
[Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
{x y : K} [ExistsAddOfLE K] (hx : 0 < x) (hy : y < 1) : ∃ n, y ^ n < x

this seem very useful
-/
theorem isEquiv_of_lt_one_imp'
  {R : Type u} {S : Type v}
  [Field R] [Semifield S] [LinearOrder S]
  {v w : AbsoluteValue R S}
  [IsStrictOrderedRing S] [Archimedean S] [ExistsAddOfLE S]
  (hv : v.IsNontrivial)
  (h : ∀ (x : R), v x < 1 → w x < 1) : v.IsEquiv w := by
  -- goal : v.IsEquiv w
  -- by AbsoluteValue.isEquiv_iff_lt_one_iff and h
  -- suffiec to show
  -- `∀ (x : R), w x < 1 → v x < 1`
  -- let x : R, w x < 1
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
  refine fun x ↦ ⟨h x, fun hwx ↦ ?_⟩

  -- lemma, ∀ x, 1 < v x → 1 < w x
  -- by considering v (x⁻¹), w (x⁻¹)
  have h' : ∀ x, 1 < v x → 1 < w x := by
    intro x hvx
    have : x ≠ 0 := by rw [← AbsoluteValue.pos_iff v]; positivity
    have hvx_inv : v (x⁻¹) < 1 := by
      rwa [map_inv₀, inv_lt_one₀]
      apply AbsoluteValue.pos _ this
    have hwx_inv : w (x⁻¹) < 1 := h (x⁻¹) hvx_inv
    have hwx' : 1 < w x := by
      rwa [map_inv₀, inv_lt_one₀] at hwx_inv
      apply AbsoluteValue.pos _ this
    exact hwx'

  -- cases v x < 1, done
  obtain hvx | hvx | hvx := lt_trichotomy (v x) 1
  · exact hvx

  -- cases v x > 1, then by the lemma, w x > 1, contradiction, done
  swap
  · have hwx' := h' x hvx
    exact (hwx.trans hwx').false.elim

  -- cases v x = 1, → x ≠ 0
  . have hx0 : x ≠ 0 := by rw [← AbsoluteValue.pos_iff v, hvx]; positivity
  -- by nontrivial, there exists y ≠ 0, v y < 1 → w y < 1
    obtain ⟨y, hy0, hvy⟩ := hv.exists_abv_lt_one
    have hwy : w y < 1 := h y hvy
  -- since w x < 1, we must have w (x ^ n) < w y for some n
  -- (by Archimedean ?)
    obtain ⟨n, hn⟩ : ∃ n, w (x ^ n) < w y := by
      simp_rw [map_pow]
      exact exists_pow_lt_of_lt_one (w.pos hy0) hwx
  -- but now we get,
  -- → w (x ^ n / y) = (w x) ^ n / w y < 1
    have h1 := calc
      w (x ^ n / y)
      _ = (w (x ^ n)) / w y := by rw [map_div₀, map_pow]
      _ < 1 := by rwa [div_lt_one₀]; exact w.pos hy0
  -- v (x ^ n / y) = v (x ^ n) / v y = v x ^ n / v y = 1 / v y > 1
  -- → w (x ^ n / y) < 1, contradiction, done
    have := calc
      v (x ^ n / y)
      _ = v (x ^ n) / v y := by rw [map_div₀, map_pow]
      _ = v x ^ n / v y := by rw [map_pow]
      _ = (v y)⁻¹ := by rw [hvx, one_pow, inv_eq_one_div]
      _ > 1 := by rwa [gt_iff_lt, one_lt_inv₀]; exact v.pos hy0
    have h2 := h' _ this
    exact (h1.trans h2).false.elim


theorem exists_one_lt_lt_one_pi_of_eq_one'
  {K : Type u_1} [Field K]
  {ι : Type u_3} [Fintype ι] [DecidableEq ι]
  {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
  (ha : 1 < (v i) a) (haj : ∀ (j : ι), j ≠ i → (v j) a < 1) (haw : w a = 1)
  (hb : 1 < (v i) b) (hbw : w b < 1) :
  ∃ k, 1 < (v i) k ∧ (∀ (j : ι), j ≠ i → (v j) k < 1) ∧ w k < 1 := by
  let c : ℕ → K := fun n ↦ a ^ n * b
  have hcᵢ : Tendsto (fun n ↦ (v i) (c n)) atTop atTop := by
    have := tendsto_pow_atTop_atTop_of_one_lt ha
    have := this.atTop_mul_const (r := v i b) (by positivity)
    convert this with n
    rw [← map_pow, map_mul]
  replace hcᵢ : ∃ N, ∀ n ≥ N, 1 < (v i) (c n) := by
    have := hcᵢ (Ioi_mem_atTop 1)
    rw [mem_map, mem_atTop_sets] at this
    exact this
  have hcⱼ : ∀ (j : ι), j ≠ i → Tendsto (fun n ↦ (v j) (c n)) atTop (𝓝 0) := by
    intro j hij
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (haj j hij)
    have := this.mul_const (b := v j b)
    convert this with n
    . rw [← map_pow, map_mul]
    . rw [zero_mul]
  replace hcⱼ : ∀ (j : ι), j ≠ i → ∃ M, ∀ n ≥ M, (v j) (c n) < 1 := by
    intro j hij
    have := hcⱼ j hij (Iio_mem_nhds one_pos)
    rw [mem_map, mem_atTop_sets] at this
    exact this
  choose N hN using hcᵢ
  choose M hM using hcⱼ
  let L := Finset.univ.sup (fun j ↦ if hij : j = i then N else M j hij)
  have hNL : N ≤ L := by
    convert Finset.univ.le_sup_dite_pos (. = i) (Finset.mem_univ i) rfl
    rfl
  have hML : ∀ (j : ι) (hij : j ≠ i), M j hij ≤ L := by
    intro j hij
    exact Finset.univ.le_sup_dite_neg (. = i) (Finset.mem_univ j) hij
  refine ⟨c L, hN L hNL, fun j hij ↦ hM j hij L (hML j hij), ?_⟩
  rwa [map_mul, map_pow, haw, one_pow, one_mul]


#check AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
/-
AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv.{u_1, u_2, u_3}

{R : Type u_1} {S : Type u_2} [Field R] [Field S]
  [LinearOrder S] [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [OrderTopology S] {ι : Type u_3}
  [Fintype ι] [DecidableEq ι] {v : ι → AbsoluteValue R S} (h : ∀ (i : ι), (v i).IsNontrivial)
  (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (i : ι) : ∃ a, 1 < (v i) a ∧ ∀ (j : ι), j ≠ i → (v j) a < 1
If v : ι → AbsoluteValue R S is a finite collection of non-trivial and pairwise inequivalent absolute values,
then for any i there is some a : R such that 1 < v i a and v j a < 1 for all j ≠ i.
-/

/-
/--
*Weak approximation for infinite places*
The number field `K` is dense when embedded diagonally in the product
`(v : InfinitePlace K) → WithAbs v.1`, in which `WithAbs v.1` represents `K` equipped with the
topology coming from the infinite place `v`.
-/
theorem denseRange_algebraMap_pi [NumberField K] :
    DenseRange <| algebraMap K ((v : InfinitePlace K) → WithAbs v.1) := by
  -- We have to show that given `(zᵥ)ᵥ` with `zᵥ : WithAbs v.1`, there is a `y : K` that is
  -- arbitrarily close to each `zᵥ` in `v`'s topology.
  refine Metric.denseRange_iff.2 fun z r hr ↦ ?_
  -- Given `v`, by previous results we can select a `aᵥ : K` for each infinite place `v`
  -- such that `1 < v aᵥ` while `w aᵥ < 1` for all `w ≠ v`.
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv isNontrivial
    (fun _ _ hwv ↦ (eq_iff_isEquiv (K := K)).not.1 hwv)
  -- Define the sequence `yₙ = ∑ v, 1 / (1 + aᵥ ^ (-n)) * zᵥ` in `K`
  let y := fun n ↦ ∑ v, (1 / (1 + (a v)⁻¹ ^ n)) * WithAbs.equiv v.1 (z v)
  -- At each place `v` the limit of `y` with respect to `v`'s topology is `zᵥ`.
  have : atTop.Tendsto (fun n v ↦ (WithAbs.equiv v.1).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.2 fun v ↦ ?_
    simp_rw [← Fintype.sum_pi_single v z, y, map_sum, map_mul]
    refine tendsto_finset_sum _ fun w _ ↦ ?_
    by_cases hw : v = w
    · -- Because `1 / (1 + aᵥ ^ (-n)) → 1` in `WithAbs v.1`.
      rw [← hw, Pi.single_apply v (z v), if_pos rfl]
      have : v (a v)⁻¹ < 1 := by simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx v).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z v)
    · -- And `1 / (1 + aᵥ ^ (-n)) → 0` in `WithAbs w.1` when `w ≠ v`.
      simp only [Pi.single_apply w (z w), hw, if_false]
      have : 1 < v (a w)⁻¹ := by simpa [one_lt_inv_iff₀] using
        ⟨v.pos_iff.2 fun ha ↦ by linarith [map_zero w ▸ ha ▸ (hx w).1], (hx w).2 v hw⟩
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 <|
        v.1.tendsto_div_one_add_pow_nhds_zero this).mul_const ((WithAbs.equiv v.1).symm _)
  -- So taking a sufficiently large index of the sequence `yₙ` gives the desired term.
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 this r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩
-/

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
#check Fintype.sum_pi_single
#check Pi.single
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
