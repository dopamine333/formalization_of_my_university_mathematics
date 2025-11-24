import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

-- abstract version of Cauchy-Schwarz inequality
open scoped RealInnerProductSpace in
example {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x y : E) :
  ⟪x, y⟫ * ⟪x, y⟫ ≤ ⟪x, x⟫ * ⟪y, y⟫ :=
  real_inner_mul_inner_self_le x y

-- in ℝ³
#check Fin 3 → ℝ -- ℝ³
#synth Norm (Fin 3 → ℝ) -- equiped the sup norm
example (a : Fin 3 → ℝ) : ‖a‖ =  ‖a 0‖ ⊔ ‖a 1‖ ⊔ ‖a 2‖ := by
  calc ‖a‖
    _ = ↑(Finset.univ.sup fun i ↦ ‖a i‖₊) := rfl
    _ = ↑(({0, 1, 2} : Finset (Fin 3)).sup fun i ↦ ‖a i‖₊) := rfl
    _ = ↑(‖a 0‖₊ ⊔ ‖a 1‖₊ ⊔ ‖a 2‖₊) := by
      rw [Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton, max_assoc]
    _ = ‖a 0‖ ⊔ ‖a 1‖ ⊔ ‖a 2‖ := by push_cast; rfl
#check pi_norm_le_iff_of_nonneg' -- characterization of the sup norm
#check Pi.norm_def
-- but we want the Euclidean norm
#check PiLp
#check PiLp.norm_eq_ciSup
#check PiLp.norm_eq_sum
#check EuclideanSpace ℝ (Fin 3) -- equipped with the L2 norm
#check EuclideanSpace.norm_eq
example (a : EuclideanSpace ℝ (Fin 3)) : ‖a‖ =  √(a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) := by
  calc ‖a‖
    _ = √ (∑ i, ‖a i‖ ^ 2) := by rw [EuclideanSpace.norm_eq]
    _ = √ (∑ i, (a i) ^ 2) := by simp only [Real.norm_eq_abs, sq_abs]
    _ = √ (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) := by rw [Fin.sum_univ_three]

-- moreover, it is an inner product space
#synth Inner ℝ (EuclideanSpace ℝ (Fin 3))
#synth InnerProductSpace ℝ (EuclideanSpace ℝ (Fin 3))
#check PiLp.innerProductSpace
open scoped RealInnerProductSpace ComplexConjugate in
example (a b : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  calc ⟪a, b⟫
    _ = ∑ i, ⟪a i, b i⟫ := rfl
    _ = ∑ i, b i * conj (a i) := rfl
    _ = ∑ i, b i * a i := rfl
    _ = b 0 * a 0 + b 1 * a 1 + b 2 * a 2  := by rw [Fin.sum_univ_three]
    _ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by ring
open scoped RealInnerProductSpace ComplexConjugate in
-- notation: !₂[a₁, a₂, a₃] for (a₁, a₂, a₃) in ℝ³
example (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
  ⟪!₂[a₁, a₂, a₃], !₂[b₁, b₂, b₃]⟫ = a₁ * b₁ + a₂ * b₂ + a₃ * b₃ :=
    by simp [inner, Fin.sum_univ_three, mul_comm]

-- ℝ³ version of Cauchy-Schwarz inequality
open scoped RealInnerProductSpace in
example (x y : EuclideanSpace ℝ (Fin 3)) :
  ⟪x, y⟫ * ⟪x, y⟫ ≤ ⟪x, x⟫ * ⟪y, y⟫ :=
  real_inner_mul_inner_self_le x y

open scoped RealInnerProductSpace ComplexConjugate in
example (a b : EuclideanSpace ℝ (Fin 3)) :
  |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := by
  have H (a b : EuclideanSpace ℝ (Fin 3)) : ⟪a, b⟫ ≤ ‖a‖ * ‖b‖ := by
    -- if a = 0 or b = 0, then the inequality holds trivially
    by_cases ha : a = 0
    · rw [ha, inner_zero_left, norm_zero, zero_mul]
    by_cases hb : b = 0
    · rw [hb, inner_zero_right, norm_zero, mul_zero]
    -- if not, then we can normalize a and b to unit vectors, x and y
    let x := (1 / ‖a‖) • a
    let y := (1 / ‖b‖) • b
    have hx : ‖x‖ = 1 := by
      calc ‖x‖
        _ = |1 / ‖a‖| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = 1 / ‖a‖ * ‖a‖ := by rw [abs_of_nonneg]; positivity
        _ = 1 := by field_simp [ha]
    have hy : ‖y‖ = 1 := by
      calc ‖y‖
        _ = |1 / ‖b‖| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = 1 / ‖b‖ * ‖b‖ := by rw [abs_of_nonneg]; positivity
        _ = 1 := by field_simp [hb]
    -- then 0 ≤ ‖x - y‖² = ‖x‖² + ‖y‖² - 2⟪x, y⟫ = 2 - 2⟪x, y⟫
    have hxy : 0 ≤ 2 - 2 * ⟪x, y⟫ := by
      calc 0
        _ ≤ ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
        _ = ⟪x - y, x - y⟫ := by rw [real_inner_self_eq_norm_sq]
        _ = ⟪x, x⟫ - 2 * ⟪x, y⟫ + ⟪y, y⟫ := by
          rw [inner_sub_left, inner_sub_right, inner_sub_right]
          rw [real_inner_comm x y]
          ring
        _ = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := by
          simp [real_inner_self_eq_norm_sq]
        _ = 2 - 2 * ⟪x, y⟫ := by rw [hx, hy]; ring
    -- so ⟪x, y⟫ ≤ 1
    have hxy' : ⟪x, y⟫ ≤ 1 := by linarith
    -- thus ⟪a, b⟫ = ‖a‖ * ‖b‖ * ⟪x, y⟫ ≤ ‖a‖ * ‖b‖
    have hab : ⟪a, b⟫ ≤ ‖a‖ * ‖b‖ := by
      calc ⟪a, b⟫
        _ = ⟪‖a‖ • x, ‖b‖ • y⟫ := by rw [smul_smul, smul_smul]; field_simp; simp
        _ = ‖a‖ * ‖b‖ * ⟪x, y⟫ := by
          rw [inner_smul_left, inner_smul_right, mul_assoc, RCLike.conj_to_real]
        _ ≤ ‖a‖ * ‖b‖ * 1 := by gcongr
        _ = ‖a‖ * ‖b‖ := by ring
    exact hab
  -- by applying the same argument to a and -b, we get -⟪a, b⟫ ≤ ‖a‖ * ‖b‖
  -- thus |⟪a, b⟫| ≤ ‖a‖ * ‖b‖
  rw [abs_le']
  have := H a (-b)
  rw [inner_neg_right, norm_neg] at this
  exact ⟨H a b, this⟩


-- given a, b is linear independent, we can construct an orthonormal basis in ℝ²
-- let e₁ = a / ‖a‖, e₂ = (b - ⟪e₁, b⟫ * e₁) / ‖b - ⟪e₁, b⟫ * e₁‖
-- first let we see how lean handles orthonormal basis
#check OrthonormalBasis
#check OrthonormalBasis.repr_apply_apply
open scoped InnerProductSpace in
theorem my_repr_apply_apply
  {ι : Type u_1} {𝕜 : Type u_3} [RCLike 𝕜] {E : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
  (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫_𝕜 := by
  /-
  ⟪b i, v⟫
  = ⟪b.repr.symm (e i), v⟫
  = ⟪b.repr.symm (e i), b.repr.symm (b.repr v)⟫
  = ⟪e i, b.repr v⟫ -- since b.repr.symm is isometric
  = b.repr v
  -/
  -- check some lemma
  -- 1. v = b.repr.symm (b.repr v)
  -- #check b.repr.symm_apply_apply
  -- 2. isometric → inner product preserved
  -- #check b.repr.inner_map_map
  -- 3. inner of basis vector in ℝⁿ
  -- e i := EuclideanSpace.single i 1
  -- ⟪e i, v⟫ = v i
  -- #check EuclideanSpace.inner_single_left
  -- need classical since EuclideanSpace.single i 1 need decidableEq ι
  classical
  let e (i : ι) := EuclideanSpace.single i (1 : 𝕜)
  symm
  calc ⟪b i, v⟫_𝕜
    _ = ⟪b.repr.symm (e i), v⟫_𝕜 := rfl
    _ = ⟪b.repr.symm (e i), b.repr.symm (b.repr v)⟫_𝕜 := by
      rw [b.repr.symm_apply_apply]
    _ = ⟪e i, b.repr v⟫_𝕜 := by
      rw [b.repr.symm.inner_map_map]
    _ = b.repr v i := by
      rw [EuclideanSpace.inner_single_left]
      simp only [map_one, one_mul]


-- now we can construct the orthonormal basis in ℝ²
#check OrthonormalBasis.mk
#check orthonormal_iff_ite
#check Submodule.span
#check Submodule.top_le_span_range_iff_forall_exists_fun
#check LinearIndependent
#check linearIndependent_fin2
#check  basisOfLinearIndependentOfCardEqFinrank_repr_apply
-- a 1, a 2 are linearly independent
-- → ∃ e 1, e 2 are orthonormal basis
open scoped RealInnerProductSpace in
noncomputable example
  {a : Fin 2 → EuclideanSpace ℝ (Fin 2)} (ha : LinearIndependent ℝ a) :
  OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) := by
  -- 1. construct e₁, e₂
  let e₁ := (1 / ‖a 0‖) • a 0
  let e₂ := (1 / ‖a 1 - ⟪e₁, a 1⟫ • e₁‖) • (a 1 - ⟪e₁, a 1⟫ • e₁)
  let e := ![e₁, e₂]
  -- 2. show e is orthonormal
  have he : Orthonormal ℝ e := by
    have h11 : ⟪e₁, e₁⟫ = 1 := by
      have : a 0 ≠ 0 := ha.ne_zero 0
      rw [real_inner_self_eq_norm_sq e₁,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      field_simp
      positivity
    have h22 : ⟪e₂, e₂⟫ = 1 := by
      suffices a 1 - ⟪e₁, a 1⟫ • e₁ ≠ 0 by
        rw [real_inner_self_eq_norm_sq e₂,
          norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        field_simp
        positivity
      rw [Fintype.linearIndependent_iff] at ha
      intro h
      replace h : (- ⟪e₁, a 1⟫ * (1 / ‖a 0‖)) • a 0 + 1 • a 1 = 0 := by
        rw [← h, add_comm, sub_eq_add_neg, one_smul, smul_smul, ← neg_smul, neg_mul]
      set c := ![- ⟪e₁, a 1⟫ * (1 / ‖a 0‖), 1] with hc
      replace h : ∑ i, c i • a i = 0 := by
        simpa [hc] using h
      have := ha c h 1
      have : 1 = 0 := by simp [hc] at this
      contradiction
    have h12 : ⟪e₁, e₂⟫ = 0 := by
        rw [real_inner_smul_right]
        apply mul_eq_zero_of_right
        rw [inner_sub_right, real_inner_smul_right]
        simp [h11]
        sorry
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp
    · exact h11
    · exact h12
    · rw [real_inner_comm]; exact h12
    · exact h22
  -- 3. show e is basis
  have he' : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    rw [top_le_iff]
    apply LinearIndependent.span_eq_top_of_card_eq_finrank
    . apply he.linearIndependent
    . simp
  apply OrthonormalBasis.mk
  assumption'


-- look some LineDeriv i.e. directional derivative
#check HasLineDerivAt
#check HasFDerivAt.hasLineDerivAt
#check DifferentiableAt.lineDeriv_eq_fderiv
theorem my_lineDeriv_eq_fderiv.{u_1, u_2, u_3}
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {F : Type u_2}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : Type u_3}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → F} {x v : E}
  (hf : DifferentiableAt 𝕜 f x) :
  lineDeriv 𝕜 f x v = (fderiv 𝕜 f x) v := by
  change deriv (fun t ↦ f (x + t • v)) 0 = (fderiv 𝕜 f x) v
  change deriv (f ∘ (fun t ↦ x + t • v)) 0 = (fderiv 𝕜 f x) v
  rw [
    fderiv_comp_deriv,
    zero_smul, add_zero,
    deriv_const_add, deriv_smul_const, deriv_id'', one_smul
  ]
  . fun_prop
  . rw [zero_smul, add_zero]; exact hf
  . fun_prop


-- Cᵖ p-times diff conti
#check ContDiffWithinAt
#check HasFDerivAt
example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  {F : Type u_3} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  (f : E → F) (f' : E →L[𝕜] F) (x : E) : Prop := HasFDerivAt f f' x

-- example
--   {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
--   {E : Type u_2} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
--   {F : Type u_3} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] :
--   AddCommGroup (E →L[𝕜] F) := by infer_instance

-- example
--   {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
--   {E : Type u_2} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
--   {F : Type u_3} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] :
--   Module 𝕜 (E →L[𝕜] F) := by infer_instance

-- example
--   {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
--   {E : Type u_2} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
--   {F : Type u_3} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] :
--   TopologicalSpace (E →L[𝕜] F) := by infer_instance

example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E → F) (f' : E →L[𝕜] F) (x : E) : Prop := HasFDerivAt f f' x

example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  AddCommGroup (E →L[𝕜] F) := by infer_instance

example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  Module 𝕜 (E →L[𝕜] F) := by infer_instance

example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  TopologicalSpace (E →L[𝕜] F) := by infer_instance

set_option trace.Meta.synthInstance true in
noncomputable example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  NormedAddCommGroup (E →L[𝕜] F) := by infer_instance
#check ContinuousLinearMap.toNormedAddCommGroup

set_option trace.Meta.synthInstance true in
noncomputable example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  NormedSpace 𝕜 (E →L[𝕜] F) := by infer_instance
#check ContinuousLinearMap.toNormedSpace

#check iteratedFDeriv
#check ContinuousMultilinearMap


set_option trace.Meta.synthInstance true in
example {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  : AddCommMonoid (ι → M) :=  by infer_instance
#check Pi.addCommMonoid
set_option trace.Meta.synthInstance true in
example {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  : Module R (ι → M) :=  by infer_instance
#check Pi.addCommMonoid
set_option trace.Meta.synthInstance true in
example {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  : TopologicalSpace (ι → M) :=  by infer_instance
#check Pi.addCommMonoid

-- φ ∈ (i : I) → f i
-- ↔ ∀ i : I, φ i ∈ f i

-- f 1 × f 2 × ...

-- ((i ∈ I) → f(i)) = { φ : I → ∪_{i ∈ I}, f(i) | ∀ i ∈ I, φ(i) ∈ f(i)}
#check Classical.axiom_of_choice
#check Equiv.trans
#check LinearEquiv


set_option trace.Meta.synthInstance true in
noncomputable example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
  NormedSpace 𝕜 (E →L[𝕜] (E →L[𝕜] F)) := by infer_instance
#check ContinuousLinearMap.toNormedSpace
#check MultilinearMap


#check ContDiff
-- contdiff iff coord func are contidiff?
#check contDiff_pi
-- ok, but Φ : E → (i : ι) → F i
-- so Φ : (Fin n → ℝ) → (Fin n → ℝ) also work
example (n : WithTop ℕ∞) (N : ℕ) (Φ : (Fin N → ℝ) → (Fin N → ℝ)) :
  ContDiff ℝ n Φ ↔ ∀ i : Fin N, ContDiff ℝ n (Φ . i) := contDiff_pi
-- but (Fin n → ℝ) is equip sup norm
-- i want EuclideanSpace ℝ (Fin n) i.e L2 space
-- maybe ContDiff only depend on topo instead norm
#check EuclideanSpace
-- for f : E → F
#check ContinuousLinearEquiv.contDiff_comp_iff
-- if e : E' ≃L[𝕜] E, we have ContDiff 𝕜 n f ↔ ContDiff 𝕜 n (f ∘ e)
#check ContinuousLinearEquiv.comp_contDiff_iff
-- if e : F ≃L[𝕜] F', we have ContDiff 𝕜 n f ↔ ContDiff 𝕜 n (e ∘ f)
-- only need to find (EuclideanSpace ℝ (Fin n)) ≃L[𝕜] (Fin n → ℝ)
#check EuclideanSpace.equiv
-- yaa
example (n : WithTop ℕ∞) (N : ℕ) (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
  ContDiff ℝ n Φ ↔ ∀ i : Fin N, ContDiff ℝ n ((Φ . i) : EuclideanSpace ℝ (Fin N) → ℝ) := by
  let e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] Fin N → ℝ := EuclideanSpace.equiv _ _
  let proj := @ContinuousLinearMap.proj ℝ _ (Fin N) (fun _ : Fin N ↦ ℝ) _ _ _
  calc ContDiff ℝ n Φ
    _ ↔ ContDiff ℝ n (Φ ∘ e.symm) := (ContinuousLinearEquiv.contDiff_comp_iff _).symm
    _ ↔ ContDiff ℝ n (e ∘ Φ ∘ e.symm) := (ContinuousLinearEquiv.comp_contDiff_iff _).symm
    _ ↔ ∀ i : Fin N, ContDiff ℝ n ((e ∘ Φ ∘ e.symm) . i) := contDiff_pi
    _ ↔ ∀ i : Fin N, ContDiff ℝ n (Φ . i) := forall_congr' (fun i ↦ ?_)
  -- calc ContDiff ℝ n ((e ∘ Φ ∘ e.symm) . i)
  --   _ ↔ ContDiff ℝ n ((proj i) ∘ e ∘ Φ ∘ e.symm) := Iff.rfl
  --   _ ↔ ContDiff ℝ n ((proj i) ∘ Φ ∘ e.symm) := Iff.rfl
  --   _ ↔ ContDiff ℝ n (((proj i) ∘ Φ) ∘ e.symm) := Iff.rfl
  --   _ ↔ ContDiff ℝ n ((proj i) ∘ Φ) := by
  --     -- ContinuousLinearEquiv.contDiff_comp_iff _
  --     sorry
  --   _ ↔ ContDiff ℝ n (Φ . i) := sorry
  sorry

-- wow, we aleady have this lemma
#check contDiff_euclidean


example (n : WithTop ℕ∞) (N : ℕ) (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
  ContDiff ℝ n Φ ↔ ∀ i : Fin N, ContDiff ℝ n ((Φ . i) : EuclideanSpace ℝ (Fin N) → ℝ) :=
  contDiff_euclidean

example (n : WithTop ℕ∞) (N : ℕ) (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
  ContDiff ℝ n Φ ↔ ∀ i : Fin N, ContDiff ℝ n ((Φ . i) : EuclideanSpace ℝ (Fin N) → ℝ) := by
  let e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] Fin N → ℝ := EuclideanSpace.equiv _ _
  rw [← e.comp_contDiff_iff, contDiff_pi]
  rfl

example (n : WithTop ℕ∞) (N : ℕ) (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
  ContDiff ℝ n Φ ↔ ∀ i : Fin N, ContDiff ℝ n ((Φ . i) : EuclideanSpace ℝ (Fin N) → ℝ) := by
  let e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] Fin N → ℝ := EuclideanSpace.equiv _ _
  let proj := @ContinuousLinearMap.proj ℝ _ (Fin N) (fun _ : Fin N ↦ ℝ) _ _ _
  calc ContDiff ℝ n Φ
    _ ↔ ContDiff ℝ n (e ∘ Φ) := (ContinuousLinearEquiv.comp_contDiff_iff _).symm
    _ ↔ ∀ i : Fin N, ContDiff ℝ n ((e ∘ Φ) . i) := contDiff_pi
    _ ↔ ∀ i : Fin N, ContDiff ℝ n (Φ . i) := Iff.rfl

#check fderiv_inner_apply


#check fderiv
#check LinearMap.trace
noncomputable def div
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : E → E) (x : E) : 𝕜
  := LinearMap.trace 𝕜 E (fderiv 𝕜 f x)


theorem div_euclideanSpace
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n)) :
  div f x = ∑ i, (fderiv ℝ f x) (EuclideanSpace.single i 1) i := by
  let e (i : Fin n) := EuclideanSpace.single i (1 : ℝ)
  let E := EuclideanSpace ℝ (Fin n)
  let df := fderiv ℝ f x
  let tr := LinearMap.trace ℝ E
  let b' := EuclideanSpace.basisFun (Fin n) ℝ
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  calc tr df
    _ = (df.toMatrix b b).trace := LinearMap.trace_eq_matrix_trace ℝ b df
    _ = ∑ i, df.toMatrix b b i i := rfl
    _ = ∑ i, df (e i) i := Finset.sum_congr rfl (fun i _ ↦ ?_)
  calc df.toMatrix b b i i
    _ = b.repr (df (b i)) i := LinearMap.toMatrix_apply b b df i i
    _ = b'.repr (df (b i)) i := rfl
    _ = df (b i) i := EuclideanSpace.basisFun_repr _ _ _ _
    _ = df (b' i) i := rfl
    _ = df (e i) i := by rw [EuclideanSpace.basisFun_apply]


theorem div_euclideanSpace_fin2
  (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
  (x : EuclideanSpace ℝ (Fin 2)) :
  div f x = (fderiv ℝ f x) (EuclideanSpace.single 0 1) 0 + (fderiv ℝ f x) (EuclideanSpace.single 1 1) 1 := by
  rw [div_euclideanSpace, Fin.sum_univ_two]



set_option trace.Meta.synthInstance true in
noncomputable example
  {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
  NormedSpace 𝕜 (E × E) := by infer_instance
#check Prod.normedSpace

#check Prod.fst
-- ContinuousLinearMap.fst

noncomputable def curl
  (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
  (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  let df := fderiv ℝ f x
  -- df = jacobian matrix of f at x
  -- ∂fᵢ/∂xⱼ = df (e j) i
  let e (i : Fin 3) := EuclideanSpace.single i (1 : ℝ)
  sorry
  -- ![df (e 1) 0 - df (e 2) 1, df (e 0) 2 - df (e 1) 0, df (e 2) 1 - df (e 0) 2]
-- Theorem 1.2.3
-- theorem div_curl_eq_zero
--   (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
--   (hf : ContDiff ℝ 2 f) (x : EuclideanSpace ℝ (Fin 3)) :
--   div (curl f) x = (0 : ℝ) := by
--   -- We use the fact that div F = ∑ᵢ ∂Fᵢ/∂xᵢ
--   rw [div_euclideanSpace]
--   -- We expand the definition of curl
--   simp only [curl, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
--     Matrix.head_fin_const, Matrix.cons_val_two]
--   -- We need to compute the partial derivatives of the components of curl f
--   -- The derivative of (f i) is (fderiv ℝ (f i))
--   -- The derivative of a difference is the difference of derivatives
--   -- The derivative of a linear map is the map itself
--   let df := fderiv ℝ f x
--   let e (i : Fin 3) := EuclideanSpace.single i (1 : ℝ)


--   have h_fderiv_comp_f (i j) : fderiv ℝ (fun x ↦ fderiv ℝ (f i) x (e j)) = fun x ↦ (fderiv ℝ (fderiv ℝ (f i)) x) (e j) := by
--     funext x
--     exact fderiv_comp_fderiv_at (fun y ↦ f i y) (e j) (contDiff_euclidean.mp hf i)

--   -- ∂(curl f)₀/∂x₀
--   have h₀ : fderiv ℝ (fun x ↦ df₂ x e₁ - df₁ x e₂) x e₀ =
--       (fderiv ℝ df₂ x e₀) e₁ - (fderiv ℝ df₁ x e₀) e₂ := by
--     rw [fderiv_sub]
--     · simp only [fderiv_apply_const_right]
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 2) (by norm_num))
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 1) (by norm_num))

--   -- ∂(curl f)₁/∂x₁
--   have h₁ : fderiv ℝ (fun x ↦ df₀ x e₂ - df₂ x e₀) x e₁ =
--       (fderiv ℝ df₀ x e₁) e₂ - (fderiv ℝ df₂ x e₁) e₀ := by
--     rw [fderiv_sub]
--     · simp only [fderiv_apply_const_right]
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 0) (by norm_num))
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 2) (by norm_num))

--   -- ∂(curl f)₂/∂x₂
--   have h₂ : fderiv ℝ (fun x ↦ df₁ x e₀ - df₀ x e₁) x e₂ =
--       (fderiv ℝ df₁ x e₂) e₀ - (fderiv ℝ df₀ x e₂) e₁ := by
--     rw [fderiv_sub]
--     · simp only [fderiv_apply_const_right]
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 1) (by norm_num))
--     · exact Differentiable.fderiv (ContDiff.differentiable_fderiv (contDiff_euclidean.mp hf 0) (by norm_num))

--   -- The sum is zero due to Clairaut's theorem (symmetry of mixed partials)
--   -- fderiv (fderiv f) is the second derivative, which is a symmetric bilinear map for C² functions.
--   have h_symm (i) : (iteratedFDeriv ℝ 2 (f i) x).isSymm :=
--     (contDiff_iteratedFDeriv_iff.mpr (contDiff_euclidean.mp hf i)).2.2

--   rw [Fin.sum_univ_three]
--   simp_rw [h₀, h₁, h₂]
--   rw [show (fderiv ℝ df₂ x e₀) e₁ = (fderiv ℝ df₁ x e₂) e₀ from by sorry]
--   -- The above sorry needs to be filled. Let's expand the terms.
--   -- We have ∂²f₂/∂x₀∂x₁ - ∂²f₁/∂x₀∂x₂ + ∂²f₀/∂x₁∂x₂ - ∂²f₂/∂x₁∂x₀ + ∂²f₁/∂x₂∂x₀ - ∂²f₀/∂x₂∂x₁
--   -- Let D_i D_j f_k denote (fderiv (fderiv f_k) e_j) e_i
--   -- The sum is:
--   -- (D₀ D₁ f₂) - (D₀ D₂ f₁) + (D₁ D₂ f₀) - (D₁ D₀ f₂) + (D₂ D₀ f₁) - (D₂ D₁ f₀)
--   -- By symmetry D_i D_j f_k = D_j D_i f_k
--   -- (D₀ D₁ f₂) - (D₁ D₀ f₂) = 0
--   -- (D₂ D₀ f₁) - (D₀ D₂ f₁) = 0
--   -- (D₁ D₂ f₀) - (D₂ D₁ f₀) = 0
--   -- So the sum is zero.

--   let ddf (i) := iteratedFDeriv ℝ 2 (f i) x
--   have h_symm_ddf (i j k) : ddf i (e j) (e k) = ddf i (e k) (e j) := by
--     apply (h_symm i).eq

--   calc fderiv ℝ (curl f) x e₀ 0 + fderiv ℝ (curl f) x e₁ 1 + fderiv ℝ (curl f) x e₂ 2
--     _ = (ddf 2 e₀ e₁ - ddf 1 e₀ e₂) + (ddf 0 e₁ e₂ - ddf 2 e₁ e₀) + (ddf 1 e₂ e₀ - ddf 0 e₂ e₁) := by
--         simp only [fderiv_comp_fderiv_at, (contDiff_euclidean.mp hf _), curl, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_fin_const, Matrix.cons_val_two, fderiv_sub, fderiv_apply_const_right, Differentiable.fderiv, ContDiff.differentiable_fderiv, Nat.zero_le, WithTop.coe_le_coe, Nat.cast_one, fderiv_pi]
--         congr
--     _ = (ddf 2 e₀ e₁ - ddf 2 e₁ e₀) + (ddf 1 e₂ e₀ - ddf 1 e₀ e₂) + (ddf 0 e₁ e₂ - ddf 0 e₂ e₁) := by ring
--     _ = 0 := by
--         rw [h_symm_ddf 2 0 1, h_symm_ddf 1 2 0, h_symm_ddf 0 1 2]
--         ring
