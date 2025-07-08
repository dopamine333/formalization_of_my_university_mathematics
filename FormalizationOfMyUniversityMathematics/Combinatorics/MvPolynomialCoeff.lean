import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.MvPolynomial.Equiv

open MvPolynomial
noncomputable section

section I
#check (C 1 : MvPolynomial (Fin 2) ℕ)
#check (X ⟨0, by norm_num⟩ : MvPolynomial (Fin 2) ℕ)
#check (X ⟨1, by norm_num⟩ : MvPolynomial (Fin 2) ℕ)
#check (X 0 : MvPolynomial ℕ ℕ)
#check (X 1 : MvPolynomial ℕ ℕ)
#check (X (-1) : MvPolynomial ℤ ℕ)

#check add_pow
example (n : ℕ) : (X 0 + X 1) ^ n
  = ∑ k ∈ Finset.range (n + 1), (X 0) ^ k * (X 1) ^ (n - k) * (n.choose k : MvPolynomial ℕ ℕ) := by
  exact add_pow (X 0) (X 1) n


#check coeff
#check Finsupp
#check (fun _ ↦ 1 : Fin 10 → ℕ)
#check Finsupp.mk (Finset.univ) (fun _ ↦ 1 : Fin 10 → ℕ) (by simp)
#check Finsupp.indicator (Finset.univ : Finset (Fin 10)) (fun _ _ ↦ 1)
-- set_option trace.Meta.synthInstance true in
#check Finsupp.ofSupportFinite (fun _ ↦ 1 : Fin 10 → ℕ) (Set.toFinite _)
-- set_option trace.Meta.synthInstance true in
#check Finsupp.ofSupportFinite (fun _ ↦ 1 : Fin 10 → ℕ) _
#check Finsupp.equivFunOnFinite.symm (fun _ ↦ 1 : Fin 10 → ℕ)
#check Multiset.toFinsupp (Finset.univ.1 : Multiset (Fin 10))
example : Finsupp.equivFunOnFinite.symm (fun _ ↦ 1 : Fin 10 → ℕ) = Multiset.toFinsupp (Finset.univ.1 : Multiset (Fin 10)) := by
  ext x
  rw [Finsupp.equivFunOnFinite_symm_apply_toFun, Multiset.toFinsupp_apply,
    Multiset.count_univ]
end I

section II
#check MvPolynomial.sumAlgEquiv
#check MvPolynomial.finSuccEquiv
#check finSumFinEquiv
#check renameEquiv
#check Polynomial ℕ
#synth (Algebra ℕ (Polynomial ℕ))
example (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
example (m n : ℕ) : MvPolynomial (Fin m ⊕ Fin n) ℕ ≃ₐ[ℕ] MvPolynomial (Fin (m + n)) ℕ := renameEquiv _ finSumFinEquiv
example (m n : ℕ) : MvPolynomial (Fin m ⊕ Fin n) ℕ ≃ₐ[ℕ] MvPolynomial (Fin m) (MvPolynomial (Fin n) ℕ) := sumAlgEquiv _ _ _
example (m n : ℕ) : MvPolynomial (Fin (m + n)) ℕ ≃ₐ[ℕ] MvPolynomial (Fin m) (MvPolynomial (Fin n) ℕ) := by
  exact (renameEquiv _ finSumFinEquiv.symm).trans (sumAlgEquiv _ _ _)
example (m n : ℕ) : MvPolynomial (Fin (m + n)) ℕ ≃ₐ[ℕ] MvPolynomial (Fin n) (MvPolynomial (Fin m) ℕ) := by
  exact ((renameEquiv _ finSumFinEquiv.symm).trans (sumAlgEquiv _ _ _)).trans (commAlgEquiv _ _ _)

#check MvPolynomial.optionEquivLeft_coeff_coeff
#check MvPolynomial.finSuccEquiv_apply
#check finSuccEquiv_coeff_coeff
#synth Add ((Fin 10) →₀ ℕ)
#synth AddMonoid ((Fin 10) →₀ ℕ)
#synth AddMonoid ((Fin 10) → ℕ)
#check Finsupp.support_add_eq
#check Finsupp.addEquivFunOnFinite
#check Finsupp.split
#check Finsupp.sigmaFinsuppEquivPiFinsupp
#check Finsupp.sigmaFinsuppAddEquivPiFinsupp
#check Sigma.curry
#check Equiv.piCurry
#check Prod.toSigma
def indexd_two_type (A B : Type) : Fin 2 → Type := fun | 0 => A | 1 => B
@[simp]
lemma indexd_two_type_apply_0 {A B : Type} : indexd_two_type A B 0 = A := by simp [indexd_two_type]
@[simp]
lemma indexd_two_type_apply_1 {A B : Type} : indexd_two_type A B 1 = B := by simp [indexd_two_type]
example (A B : Type) : Sigma (fun | 0 => A | 1 => B : Fin 2 → Type) ≃ A ⊕ B where
  toFun
    | ⟨0, b⟩ => Sum.inl b
    | ⟨1, b⟩ => Sum.inr b
  invFun
    | Sum.inl b => ⟨0, b⟩
    | Sum.inr b => ⟨1, b⟩
  left_inv := fun
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  right_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl


#check finSuccEquiv_coeff_coeff
#check optionEquivLeft_coeff_coeff
#check MvPolynomial.induction_on
#check sumAlgEquiv
#check Finsupp.sumFinsuppAddEquivProdFinsupp

@[simp] lemma Finsupp.sumElim_zero_iff {S₁ S₂ : Type} {s₁ : S₁ →₀ ℕ} {s₂ : S₂ →₀ ℕ} :
  s₁.sumElim s₂ = 0 ↔ s₁ = 0 ∧ s₂ = 0 := by
  constructor
  . intro hs
    constructor
    . ext i
      calc s₁ i
        _ = (s₁.sumElim s₂) (Sum.inl i) := rfl
        _ = 0 := by rw [hs]; rfl
    . ext i
      calc s₂ i
        _ = (s₁.sumElim s₂) (Sum.inr i) := rfl
        _ = 0 := by rw [hs]; rfl
  . rintro ⟨hs₁, hs₂⟩
    rw [hs₁, hs₂]
    exact card_support_eq_zero.mp rfl
@[simp] lemma Finsupp.zero_sumElim_zero {S₁ S₂ : Type} : Finsupp.sumElim 0 0 = (0 : S₁ ⊕ S₂ →₀ ℕ) := card_support_eq_zero.mp rfl

@[simp] theorem MvPolynomial.sumAlgEquiv_coeff_coeff {R : Type} [CommSemiring R]
  {S₁ S₂ : Type} [DecidableEq S₁] [DecidableEq S₂]
  (s₁ : S₁ →₀ ℕ) (s₂ : S₂ →₀ ℕ) (f : MvPolynomial (S₁ ⊕ S₂) R) :
  coeff s₂ (coeff s₁ ((sumAlgEquiv R S₁ S₂) f)) = coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩) f := by
  induction f using MvPolynomial.induction_on generalizing s₁ s₂ with
  | C a =>
    simp
    obtain hs | hs := eq_or_ne (s₁.sumElim s₂) 0
    . simp [Finsupp.sumElim_zero_iff.mp hs]
    . have := Finsupp.sumElim_zero_iff.not.mp hs
      by_cases hs₁ : s₁ ≠ 0
      . simp [hs.symm, hs₁.symm]
      . have hs₂ : s₂ ≠ 0 := by tauto
        simp [hs.symm, (not_not.mp hs₁).symm, hs₂.symm]
  | add p q hp hq =>
    simp at ⊢ hp hq
    rw [hp, hq]
  | mul_X p i hp =>
    simp at hp ⊢
    match i with
    | Sum.inl i =>
      simp
      rw [coeff_mul_X']
      rw [coeff_mul_X']
      simp
      by_cases hs₁ : s₁ i = 0
      . simp [hs₁]
      . simp [hs₁]
        convert hp _ _
        ext j
        match j with
        | Sum.inl j =>
          obtain rfl | hij := eq_or_ne i j
          . simp
          . simp [hij]
        | Sum.inr j => simp
    | Sum.inr i =>
      simp
      rw [mul_comm, coeff_C_mul]
      rw [coeff_X_mul']
      rw [coeff_mul_X']
      simp
      by_cases hs₂ : s₂ i = 0
      . simp [hs₂]
      . simp [hs₂]
        convert hp _ _
        ext j
        match j with
        | Sum.inl j => simp
        | Sum.inr j =>
          obtain rfl | hij := eq_or_ne i j
          . simp
          . simp [hij]


@[simp] theorem MvPolynomial.sumAlgEquiv_coeff_coeff' {R : Type} [CommSemiring R]
  {S₁ S₂ : Type} [DecidableEq S₁] [DecidableEq S₂]
  (s : S₁ ⊕ S₂ →₀ ℕ) (f : MvPolynomial (S₁ ⊕ S₂) R) :
  coeff (Finsupp.sumFinsuppAddEquivProdFinsupp s).2 (coeff (Finsupp.sumFinsuppAddEquivProdFinsupp s).1 ((sumAlgEquiv R S₁ S₂) f)) = coeff s f := by
  set s₁ := (Finsupp.sumFinsuppAddEquivProdFinsupp s).1
  set s₂ := (Finsupp.sumFinsuppAddEquivProdFinsupp s).2
  have s_eq : s = Finsupp.sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩ := by
    calc s
      _ =  Finsupp.sumFinsuppAddEquivProdFinsupp.symm (Finsupp.sumFinsuppAddEquivProdFinsupp s) := by symm; apply Equiv.symm_apply_apply
      _ = Finsupp.sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩ := by congr
  rw [s_eq]
  apply sumAlgEquiv_coeff_coeff

/-
(f : σ → τ) (hf : Function.Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
  coeff (Finsupp.mapDomain f d) ((rename f) φ) = coeff d φ
  -/
@[simp] theorem coeff_renameEquiv_domCongr
  {R : Type} [CommSemiring R] {σ τ : Type}
  (f : σ ≃ τ) (p : MvPolynomial σ R) (s : σ →₀ ℕ)
  : coeff (Finsupp.domCongr f s) (renameEquiv _ f p) = coeff s p := by
  simp
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  rw [coeff_rename_mapDomain]
  exact Equiv.injective f

end II


section III

#check Finsupp.sumFinsuppAddEquivProdFinsupp
#check Equiv.sumArrowEquivProdArrow
#check Finsupp.domCongr
def split_finsupp {m n : ℕ} : (Fin (m + n) →₀ ℕ) ≃+ (Fin m →₀ ℕ) × (Fin n →₀ ℕ) :=
  (Finsupp.domCongr finSumFinEquiv.symm).trans Finsupp.sumFinsuppAddEquivProdFinsupp
def nested_polynomial {m n : ℕ} : MvPolynomial (Fin (m + n)) ℕ ≃ₐ[ℕ] MvPolynomial (Fin m) (MvPolynomial (Fin n) ℕ) :=
  (renameEquiv _ finSumFinEquiv.symm).trans (sumAlgEquiv _ _ _)

#check Fin.castAdd
#check Fin.natAdd
example : Fin.castAdd 1 (20 : Fin 300) = (20 : Fin 301) := rfl
example : Fin.natAdd 1 (20 : Fin 300) = (21 : Fin 301) := rfl
example : finSumFinEquiv (Sum.inl (1 : Fin 30) : (Fin 30 ⊕ Fin 40)) = (1 : Fin 70) := rfl
example : finSumFinEquiv (Sum.inr (1 : Fin 40) : (Fin 30 ⊕ Fin 40)) = (31 : Fin 70) := rfl
@[simp] lemma split_finsupp_apply_left {m n : ℕ} (s : Fin (m + n) →₀ ℕ) :
  (split_finsupp s).1 = s ∘ Fin.castAdd n := rfl
@[simp] lemma split_finsupp_apply_right {m n : ℕ} (s : Fin (m + n) →₀ ℕ) :
  (split_finsupp s).2 = s ∘ Fin.natAdd m := rfl
lemma split_finsupp_apply_left_at {m n : ℕ} (s : Fin (m + n) →₀ ℕ) (x : Fin m):
  (split_finsupp s).1 x = s (⟨x, by linarith [x.2]⟩ : Fin (m + n)) := rfl
lemma split_finsupp_apply_right_at {m n : ℕ} (s : Fin (m + n) →₀ ℕ) (x : Fin n):
  (split_finsupp s).2 x = s (⟨m + x, by linarith [x.2]⟩ : Fin (m + n)) := rfl

#check renameEquiv
#check renameEquiv_apply
#check rename_monomial
#check rename_C
#check rename_X
#check sumAlgEquiv
#check sumAlgEquiv_apply
#check sumAlgEquiv_symm_apply
#check sumToIter_C
#check sumToIter_Xl
#check sumToIter_Xr
#check iterToSum_C_C
#check iterToSum_C_X
#check iterToSum_X
@[simp] lemma nested_polynomial_C {m n : ℕ} (a : ℕ) :
  nested_polynomial (C a : MvPolynomial (Fin (m + n)) ℕ) = C (C a) := by
  simp only [eq_natCast, map_natCast]
@[simp] lemma nested_polynomial_X_left {m n : ℕ} (i : Fin m) :
  nested_polynomial (X (Fin.castAdd n i)) = X i := by simp [nested_polynomial]
@[simp] lemma nested_polynomial_X_right {m n : ℕ} (i : Fin n) :
  nested_polynomial (X (Fin.natAdd m i)) = C (X i) := by simp [nested_polynomial]


#check MvPolynomial.induction_on'
#check Finsupp.induction
#synth DecidableEq (Fin 10)
#check coeff_map
#check coeff_rename_embDomain
#check coeff_rename_mapDomain
#check Finsupp.equivMapDomain
#check Finsupp.domCongr
#check Finsupp.equivMapDomain_eq_mapDomain

lemma coeff_nested_polynomial_split_finsupp_step1 (m n : ℕ) (p : MvPolynomial (Fin m ⊕ Fin n) ℕ) (s : (Fin m ⊕ Fin n) →₀ ℕ)
  : coeff s p = coeff ((Finsupp.sumFinsuppAddEquivProdFinsupp s).2) (coeff (Finsupp.sumFinsuppAddEquivProdFinsupp s).1 (sumAlgEquiv _ _ _ p)) := by
  symm
  apply sumAlgEquiv_coeff_coeff'

lemma coeff_nested_polynomial_split_finsupp_step2 (m n : ℕ) (p : MvPolynomial (Fin (m + n)) ℕ) (s : Fin (m + n) →₀ ℕ)
  : coeff s p = coeff (Finsupp.domCongr finSumFinEquiv.symm s) (renameEquiv _ finSumFinEquiv.symm p) := by
  simp
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  rw [coeff_rename_mapDomain]
  exact Equiv.injective finSumFinEquiv.symm

theorem coeff_nested_polynomial_split_finsupp (m n : ℕ) (p : MvPolynomial (Fin (m + n)) ℕ) (s : Fin (m + n) →₀ ℕ)
  : coeff s p = coeff ((split_finsupp s).2) (coeff (split_finsupp s).1 (nested_polynomial p)) := by
  simp [nested_polynomial, split_finsupp,
        coeff_nested_polynomial_split_finsupp_step2,
        coeff_nested_polynomial_split_finsupp_step1]

end III


section IV
-- set_option trace.Meta.synthInstance true in
def exactly_once (σ : Type u_1) [Finite σ] : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ ↦ 1
def perm_coeff (n : ℕ) : ℕ := ((∑ k : Fin n, X k) ^ n).coeff (Finsupp.equivFunOnFinite.symm fun _ ↦ 1)

@[simp] lemma perm_coeff_eq_exactly_once (n : ℕ) : perm_coeff n = ((∑ k : Fin n, X k) ^ n).coeff (exactly_once (Fin n)) := rfl
@[simp] lemma split_finsupp_exactly_once (m n : ℕ) : split_finsupp (exactly_once (Fin (m + n))) = ⟨exactly_once (Fin m), exactly_once (Fin n)⟩ := by
  ext i <;> simp [exactly_once]
@[simp] lemma split_finsupp_exactly_once_left (m n : ℕ) : (split_finsupp (exactly_once (Fin (m + n)))).1 = exactly_once (Fin m) := by simp
@[simp] lemma split_finsupp_exactly_once_right (m n : ℕ) : (split_finsupp (exactly_once (Fin (m + n)))).2 = exactly_once (Fin n) := by simp
@[simp] lemma exactly_once_eq_single {σ : Type} [Unique σ] : exactly_once σ = Finsupp.single (default) 1 := by ext; simp [exactly_once]
#check sumAlgEquiv_coeff_coeff'
#check split_finsupp
#check nested_polynomial
#check coeff_nested_polynomial_split_finsupp
#check Nat.choose_one_right
#check Fin.sum_univ_castSucc X
#check finAddFlip
#check add_pow
#check MvPolynomial.C_eq_coe_nat
#check MvPolynomial.coeff_C_mul
#check MvPolynomial.coeff_X

example : (2 : Fin 3).castAdd 1 = (2 : Fin 4) := rfl
example (n : ℕ) : Fin (n + 1) ≃ Fin (1 + n) := by exact finAddFlip

-- set_option profiler true
theorem perm_coeff_succ (n : ℕ) : perm_coeff (n + 1) = (n + 1) * perm_coeff n := by
  calc perm_coeff (n + 1)
    _ = coeff (exactly_once (Fin (n + 1))) ((∑ k : Fin (n + 1), X k) ^ (n + 1)) := rfl
    _ = coeff (exactly_once (Fin (n + 1))) (((∑ k : Fin n, X (k.castAdd 1)) + X (Fin.natAdd n 1) ) ^ (n + 1)) := by
      congr
      exact Fin.sum_univ_castSucc X
    _ = coeff (exactly_once (Fin (1 + n))) (((∑ k : Fin n, X (k.natAdd 1)) + X (Fin.castAdd n 0) ) ^ (n + 1)) := by
      convert coeff_renameEquiv_domCongr (finAddFlip : Fin (1 + n) ≃ Fin (n + 1)) _ _ using 2
      . ext i; simp [exactly_once]
      . simp
    _ = coeff (exactly_once (Fin n)) (coeff (exactly_once (Fin 1)) ((C (∑ k : Fin n, X k) + (X (0 : Fin 1))) ^ (n + 1))) := by
      simp [coeff_nested_polynomial_split_finsupp]
    _ = coeff (exactly_once (Fin n)) (coeff (exactly_once (Fin 1)) (
        ∑ m ∈ Finset.range ((n + 1) + 1), (C (∑ k : Fin n, X k)) ^ m * (X (0 : Fin 1)) ^ ((n + 1) - m) * ↑((n + 1).choose m)
      )) := by rw [add_pow]
    _ = coeff (exactly_once (Fin n)) (
        coeff (exactly_once (Fin 1)) ( (C (∑ k : Fin n, X k)) ^ n * (X (0 : Fin 1)) ^ ((n + 1) - n) * ↑((n + 1).choose n))
      ) := by
      congr 1
      rw [coeff_sum]
      apply Finset.sum_eq_single
      . intro m hm hmn
        calc coeff (exactly_once (Fin 1)) (C (∑ k : Fin n, X k) ^ m * X 0 ^ (n + 1 - m) * ((n + 1).choose m : MvPolynomial (Fin 1) (MvPolynomial (Fin n) ℕ)))
          _ = coeff (exactly_once (Fin 1)) (C ((∑ k : Fin n, X k) ^ m * ((n + 1).choose m : MvPolynomial (Fin n) ℕ)) * X 0 ^ (n + 1 - m))  := by
            rw [← C_eq_coe_nat, mul_right_comm, ← C_pow, ← C_mul]
          _ = (∑ k : Fin n, X k) ^ m * ((n + 1).choose m : MvPolynomial (Fin n) ℕ) * coeff (exactly_once (Fin 1)) (X 0 ^ (n + 1 - m)) := by
            rw [coeff_C_mul]
          _ = 0 := by
            convert mul_zero _
            rw [coeff_X_pow]
            rw [exactly_once_eq_single]
            have : n + 1 - m ≠ 1 := by
              have : m ≤ n + 1 := by linarith [Finset.mem_range.mp hm]
              intro h
              apply hmn
              apply Nat.succ_inj.mp
              calc m.succ
                _ = 1 + m := by rw [add_comm]
                _ = n + 1 - m + m := by rw [h]
                _ = n + 1 := by rw [Nat.sub_add_cancel this]
            rw [ite_eq_right_iff]
            intro h
            have : n + 1 - m = 1 := Finsupp.single_injective _ h
            contradiction
      . intro hn
        linarith [Finset.mem_range.not.mp hn]
    _ = coeff (exactly_once (Fin n)) (
        coeff (exactly_once (Fin 1)) ( (C (∑ k : Fin n, X k)) ^ n * (X (0 : Fin 1)) * ↑(n + 1))
      ) := by simp
    _ = coeff (exactly_once (Fin n)) (
        coeff (exactly_once (Fin 1)) ( ↑(n + 1) * ((C (∑ k : Fin n, X k)) ^ n * (X (0 : Fin 1)) ))
      ) := by ring
    _ = (n + 1)
      * coeff (exactly_once (Fin n)) ( ((∑ k : Fin n, X k) ^ n)
      * coeff (exactly_once (Fin 1)) (X (0 : Fin 1))
      ) := by
        rw [← C_eq_coe_nat, coeff_C_mul,
            ← C_eq_coe_nat, coeff_C_mul,
            ← C_pow, coeff_C_mul]
        rfl
    _ = (n + 1)
      * coeff (exactly_once (Fin n)) ( ((∑ k : Fin n, X k) ^ n)
      * 1
      ) := by simp
    _ = (n + 1)
      * coeff (exactly_once (Fin n)) ( ((∑ k : Fin n, X k) ^ n)) := by simp
    _ = (n + 1) * perm_coeff n := by rfl

#check MvPolynomial.eq_C_of_isEmpty
-- #synth IsEmpty (Fin 0 → ℕ)
#synth Unique (Fin 0 → ℕ)
#synth Unique (Fin 0 →₀ ℕ)
theorem perm_coeff_zero : perm_coeff 0 = 1 := by
  rw [perm_coeff, pow_zero, coeff_one]
  simp
  symm
  apply Unique.uniq

theorem perm_coeff_eq_factorial (n : ℕ) : perm_coeff n = Nat.factorial n := by
  induction n with
  | zero => rw [perm_coeff_zero]; rfl
  | succ n hn => rw [perm_coeff_succ, hn]; rfl

/-
(x1 + ... + xn + x(n+1)) ^ (n+1)
sum k=0^n+1 ncr(n+1,k) (x1 + ... + xn) ^ k (x(n+1)) ^ (n+1-k)
ncr(n+1,n) (x1 + ... + xn) ^ n (x(n+1)) ^ (n+1-n)
-/
end IV
