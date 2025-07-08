import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Nat.Choose.Sum

open MvPolynomial Finsupp
noncomputable section

-- # How multivariate polynomials are defined
section I

#check MvPolynomial
#check MvPolynomial.X
#check MvPolynomial.C
#check MvPolynomial.coeff

example (σ : Type) (R : Type) [CommSemiring R] :
  MvPolynomial σ R = ((σ →₀ ℕ) →₀ R) := rfl

#check Finsupp
#check equivFunOnFinite
#check single

#check single_eq_monomial
#check monomial_eq
example : (3 * X 0 * X 1 ^ 2 : MvPolynomial (Fin 2) ℕ) =
  single (equivFunOnFinite.symm fun | 0 => 1 | 1 => 2) 3 := by
  sorry

end I

-- # Some Isomorphisms between MvPolynomials
section II

#check AlgEquiv
#check RingEquiv
#check LinearEquiv

#check renameEquiv
#check finSumFinEquiv
#check sumAlgEquiv
example (m n : ℕ) : MvPolynomial (Fin (m + n)) ℕ ≃ₐ[ℕ] MvPolynomial (Fin m) (MvPolynomial (Fin n) ℕ) := by
  sorry

#check finSuccEquiv
#check finSuccEquiv_coeff_coeff
#check optionEquivLeft
#check optionEquivLeft_coeff_coeff
#check sumAlgEquiv
#check sumFinsuppAddEquivProdFinsupp
-- `I want this !!!`
-- #check sumAlgEquiv_coeff_coeff
#check renameEquiv
#check Finsupp.domCongr
-- `And this !!!`
-- #check coeff_renameEquiv_domCongr

#check sumAlgEquiv
#check sumFinsuppAddEquivProdFinsupp
#check finSuccEquiv_coeff_coeff -- Hint : You can see how this lemma is proved`.
#check MvPolynomial.induction_on
#check MvPolynomial.induction_on'
theorem MvPolynomial.sumAlgEquiv_coeff_coeff {R : Type} [CommSemiring R]
  {S₁ S₂ : Type} [DecidableEq S₁] [DecidableEq S₂] -- you can try delete [DecidableEq S₁] [DecidableEq S₂]
  (s₁ : S₁ →₀ ℕ) (s₂ : S₂ →₀ ℕ) (f : MvPolynomial (S₁ ⊕ S₂) R) :
  coeff s₂ (coeff s₁ ((sumAlgEquiv R S₁ S₂) f)) = coeff (sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩) f := by
  sorry

theorem MvPolynomial.sumAlgEquiv_coeff_coeff' {R : Type} [CommSemiring R]
  {S₁ S₂ : Type} [DecidableEq S₁] [DecidableEq S₂]
  (s : S₁ ⊕ S₂ →₀ ℕ) (f : MvPolynomial (S₁ ⊕ S₂) R) :
  coeff (sumFinsuppAddEquivProdFinsupp s).2 (coeff (sumFinsuppAddEquivProdFinsupp s).1 ((sumAlgEquiv R S₁ S₂) f)) = coeff s f := by
  set s₁ := (sumFinsuppAddEquivProdFinsupp s).1
  set s₂ := (sumFinsuppAddEquivProdFinsupp s).2
  have s_eq : s = sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩ := by
    calc s
      _ =  sumFinsuppAddEquivProdFinsupp.symm (sumFinsuppAddEquivProdFinsupp s) := by symm; apply Equiv.symm_apply_apply
      _ = sumFinsuppAddEquivProdFinsupp.symm ⟨s₁, s₂⟩ := by congr
  rw [s_eq]
  apply sumAlgEquiv_coeff_coeff

#check coeff_rename_mapDomain
#check equivMapDomain_eq_mapDomain
theorem coeff_renameEquiv_domCongr
  {R : Type} [CommSemiring R] {σ τ : Type}
  (f : σ ≃ τ) (p : MvPolynomial σ R) (s : σ →₀ ℕ)
  : coeff (Finsupp.domCongr f s) (renameEquiv _ f p) = coeff s p := by
  sorry

end II

-- # The number of permutations is equal to n!
section III

def perm_coeff (n : ℕ) : ℕ := ((∑ k : Fin n, X k) ^ n).coeff (Finsupp.equivFunOnFinite.symm fun _ ↦ 1)

#check Fin.sum_univ_castSucc
#check add_pow
#check Nat.choose_succ_self_right
theorem perm_coeff_succ (n : ℕ) : perm_coeff (n + 1) = (n + 1) * perm_coeff n := by
  sorry

#check MvPolynomial.eq_C_of_isEmpty
#check Unique.uniq
#synth Unique (Fin 0 →₀ ℕ)
theorem perm_coeff_zero : perm_coeff 0 = 1 := by
  sorry

theorem perm_coeff_eq_factorial (n : ℕ) : perm_coeff n = Nat.factorial n := by
  induction n with
  | zero => rw [perm_coeff_zero]; rfl
  | succ n hn => rw [perm_coeff_succ, hn]; rfl
-- `yaaaaa`

end III
