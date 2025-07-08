import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff

open scoped Polynomial.Bivariate
-- open scoped LaurentPolynomial
open Nat Polynomial Finset
noncomputable section

#check X
#check C
#check Y
#check (X : ℕ[X])
#check (X : ℕ[X][Y])
#check (Y : ℕ[X][Y])
#check Y
#check CC
#check ℕ[X]
#check ℕ[X][Y]
#check (C : ℕ → ℕ[X])
#check (C : ℕ[X] → ℕ[X][Y])
#check (CC : ℕ → ℕ[X][Y])

#check coeff ((C X + Y) : ℕ[X][Y]) 1
example : ((C X + Y) : ℕ[X][Y]).coeff 1 = (1 : ℕ[X]) := by
  rw [coeff_add]
  rw [coeff_X_one, coeff_C]
  norm_num

example : ((C X + Y) ^ 2).coeff 1 = (2 * X : ℕ[X]) := by
  calc ((C X + Y) ^ 2).coeff 1
    _ = ((C X) ^ 2 + 2 * C X * Y + Y ^ 2).coeff 1 := by ring_nf
    _ = (2 * X : ℕ[X]) := by
      simp
      calc (C X ^ 2).coeff 1 + 2 * X
        _ = (C X * C X).coeff 1 + 2 * X  := by ring_nf
        _ = 0 + 2 * X  := by simp
        _ = 2 * X := by simp

#check choose
#check X
#check C
#check coeff

#check add_pow
-- Goal
-- theorem bivariate_binomial_thm (n k : ℕ) :
--   ((C X + Y) ^ n).coeff k = (n.choose k) * (X : ℕ[X]) ^ (n - k) := by step7 n k

/-
[X^k] (1 + X)^n = nCr(n,k)
(1 + X)^n = sum_k=0^n nCr(n,k) X^k
(1 + (Y/X))^n = sum_k=0^n nCr(n,k) (Y/X)^k
X^n * (1 + (Y/X))^n = X^n * sum_k=0^n nCr(n,k) (Y/X)^k
(X + X * (Y/X))^n = sum_k=0^n nCr(n,k) X^n * (Y/X)^k
(X + Y)^n = sum_k=0^n nCr(n,k) X ^ (n-k) Y ^ k
[Y^k] (X + Y)^n = sum_k=0^n nCr(n,k) X ^ (n-k)
-/

open LaurentPolynomial
open scoped LaurentPolynomial

#check C
#check ℕ[T;T⁻¹]
#check (C : ℕ → ℕ[X])
#check (toLaurent : ℕ[X] → ℕ[T;T⁻¹])
#check (C : ℕ → ℕ[T;T⁻¹])
#check coeff_one_add_X_pow

def a : ℕ[X] := X
-- [X^k] (1 + X)^n = nCr(n,k)
theorem step1 (n k : ℕ) : ((1 + a) ^ n).coeff k = n.choose k := by apply coeff_one_add_X_pow

-- (1 + X)^n = sum_k=0^n nCr(n,k) X^k
theorem step2 (n : ℕ) : (1 + a) ^ n = ∑ k ∈ range (n + 1), (n.choose k) * a ^ k := by
  rw [← Polynomial.sum_C_mul_X_pow_eq ((1 + a) ^ n)]
  rw [sum]
  simp_rw [step1]
  simp
  congr
  ext j
  rw [Polynomial.mem_support_iff]
  rw [step1 n j]
  simp [Nat.choose_eq_zero_iff]
  exact Iff.symm Nat.lt_add_one_iff

example : (X : ℕ[X]).toLaurent = (T 1 : ℕ[T;T⁻¹]) := by simp only [toLaurent_X]
example : (X^2 : ℕ[X]).eval 2 = 4 := by simp
example : (X^2 : ℕ[X]).eval (2:ℕ) = (4:ℕ) := by simp
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℤ : ℕ →+* ℤ) (-2:ℤ) = (4:ℤ) := by simp
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℕ[X] : ℕ →+* ℕ[X]) (X^3 : ℕ[X]) = X^6 := by
  simp only [eval₂_X_pow]
  ring
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℕ[X][Y] : ℕ →+* ℕ[X][Y]) (Polynomial.C X * Y : ℕ[X][Y]) = Polynomial.C X ^ 2 * Y ^ 2 := by
  simp only [eval₂_X_pow]
  ring
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℕ[T;T⁻¹]) (T (-1)) = T (-2) := by
  simp only [Int.reduceNeg, eval₂_X_pow, T_pow, cast_ofNat, mul_neg, mul_one]
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℕ[T;T⁻¹][X]) (C (T (-1))) = (C (T (-2)) : ℕ[T;T⁻¹][X]) := by
  simp
  rw [← C_pow]
  simp
example : (X^2 : ℕ[X]).eval₂ (castRingHom ℕ[T;T⁻¹][X]) ((C (T (-1)): ℕ[T;T⁻¹][X]) * X) = ((C (T (-2)) : ℕ[T;T⁻¹][X]) * X ^ 2) := by
  simp
  rw [mul_pow (C (T (-1)): ℕ[T;T⁻¹][X])]
  rw [← C_pow]
  simp

def b : ℕ[T;T⁻¹][X] := X
def c : ℕ[T;T⁻¹][X] := C (T 1)
def c_inv : ℕ[T;T⁻¹][X] := C (T (-1))
def i₁ : ℕ →+* ℕ[T;T⁻¹][X] := castRingHom ℕ[T;T⁻¹][X]
@[simp]
lemma eval_a_at_b_mul_c_inv : a.eval₂ i₁ (b * c_inv) = b * c_inv := by simp [a, b, c_inv, i₁]
-- (1 + (Y/X))^n = sum_k=0^n nCr(n,k) (Y/X)^k
theorem step3 (n : ℕ) : (1 + b * c_inv) ^ n
  = ∑ k ∈ range (n + 1), n.choose k * (b * c_inv) ^ k := by
  calc (1 + b * c_inv) ^ n
   _ = ((1 + a) ^ n).eval₂ (i₁) (b * c_inv) := by
    rw [eval₂_pow i₁ (b * c_inv)]
    simp
   _ = (∑ k ∈ range (n + 1), (n.choose k) * a ^ k).eval₂ (i₁) (b * c_inv) := by
    simp_rw [step2 n]
   _ = ∑ k ∈ range (n + 1), (n.choose k) * (a ^ k).eval₂ (i₁) (b * c_inv) := by
    simp_rw [eval₂_finset_sum, eval₂_mul i₁ (b * c_inv), eval₂_natCast]
   _ = ∑ k ∈ range (n + 1), (n.choose k) * ((b * c_inv) ^ k) := by
    simp_rw [eval₂_pow i₁ (b * c_inv)]
    simp
-- X^n * (1 + (Y/X))^n = X^n * sum_k=0^n nCr(n,k) (Y/X)^k
theorem step4 (n : ℕ) : c ^ n * (1 + b * c_inv) ^ n
  = c ^ n * ∑ k ∈ range (n + 1), n.choose k * (b * c_inv) ^ k := by
  simp [step3 n]
-- (X + X * (Y/X))^n = sum_k=0^n nCr(n,k) X^n * (Y/X)^k
theorem step5 (n : ℕ) :  (c + c * b * c_inv) ^ n
  = ∑ k ∈ range (n + 1), n.choose k * c ^ n * (b * c_inv) ^ k := by
  convert step4 n
  . calc (c + c * b * c_inv) ^ n
    _ = (c * (1 + b * c_inv)) ^ n := by ring
    _ = c ^ n * (1 + b * c_inv) ^ n := by rw [mul_pow c]
  . rw [mul_sum]
    congr
    ext
    ring_nf

@[simp]
lemma c_mul_c_inv : c * c_inv = 1 := by
  unfold c c_inv
  refine map_mul_eq_one Polynomial.C ?_
  rw [← LaurentPolynomial.T_add]
  simp

-- @[simp]
-- lemma c_inv_is_c_inv : c_inv = c⁻¹ := by
-- (X + Y)^n = sum_k=0^n nCr(n,k) X ^ (n-k) Y ^ k
theorem step6 (n : ℕ) :  (c + b) ^ n
  = ∑ k ∈ range (n + 1), n.choose k * c ^ (n - k) * b ^ k := by
  convert step5 n using 2 with k hk
  . congr
    symm
    calc c * b * c_inv
      _ = b * (c * c_inv) := by ring
      _ = b * 1 := by simp
      _ = b := by simp
  . replace hk : k ≤ n := by linarith [mem_range.1 hk]
    rw [mul_assoc, mul_assoc]
    congr 1
    symm
    calc c ^ n * (b * c_inv) ^ k
      _ = (c ^ n * c_inv ^ k) * b ^ k := by ring
      _ = c ^ (n - k) * b ^ k := by
        congr
        unfold c c_inv
        rw [← map_pow, ← map_pow, ← map_mul, ← map_pow]
        congr
        rw [T_pow, T_pow, T_pow]
        ring_nf
        rw [Int.natCast_sub hk, T_sub]


def e : ℕ[X][Y] := C X
def f : ℕ[X][Y] := Y
def i₂ : ℕ[X][Y] →+* ℕ[T;T⁻¹][X] := Polynomial.mapRingHom (toLaurent : ℕ[X] →+* ℕ[T;T⁻¹])
@[simp]
lemma i₂_of_e_eq_c : i₂ e = c := by simp [i₂, e, c]
@[simp]
lemma i₂_of_f_eq_b : i₂ f = b := by simp [i₂, b, f]
@[simp]
lemma i₂_injective : Function.Injective i₂ := by
  simp [i₂]
  exact Polynomial.map_injective (toLaurent : ℕ[X] →+* ℕ[T;T⁻¹]) toLaurent_injective

#check (Polynomial.map)
#check (Polynomial.mapAlgHom)
#check (Polynomial.mapRingHom)
#check (Polynomial.map)
#check Polynomial.eval₂RingHom
#check toLaurent_inj
#check toLaurent
#check toLaurent
example : c = (C (T 1) : ℕ[T;T⁻¹][X]) := rfl
example : e = (C X : ℕ[X][Y]) := rfl
example : e.map (toLaurent : ℕ[X] →+* ℕ[T;T⁻¹]) = c := by simp [e, c]
example : f.map (toLaurent : ℕ[X] →+* ℕ[T;T⁻¹]) = b := by simp [f, b]
example : (e + f).map toLaurent = c + b := by simp [c, b, e, f]
example : (e + f).map toLaurent = c + b := by simp [c, b, e, f]

example (F G: ℕ[X][Y]) (h : (F.map toLaurent : ℕ[T;T⁻¹][X]) = G.map toLaurent) : F = G := by
  have h1 := Polynomial.map_injective (toLaurent : ℕ[X] →+* ℕ[T;T⁻¹]) toLaurent_injective
  have h2 := h1 h
  exact h2

-- (X + Y)^n = sum_k=0^n nCr(n,k) X ^ (n-k) Y ^ k
theorem step6' (n : ℕ) : (e + f) ^ n
  = ∑ k ∈ range (n + 1), n.choose k * e ^ (n - k) * f ^ k := by
  apply i₂_injective
  calc i₂ ((e + f) ^ n)
    _ = (c + b) ^ n := by simp
    _ = ∑ k ∈ range (n + 1), n.choose k * c ^ (n - k) * b ^ k := step6 n
    _ = i₂ (∑ k ∈ range (n + 1), n.choose k * e ^ (n - k) * f ^ k) := by simp

-- [Y^k] (X + Y)^n = sum_k=0^n nCr(n,k) X ^ (n-k)
theorem step7 (n k : ℕ) : (((C X : ℕ[X][Y]) + Y) ^ n).coeff k = n.choose k * X ^ (n - k) := by
  calc (((C X : ℕ[X][Y]) + Y) ^ n).coeff k
    _ = ((e + f) ^ n).coeff k := rfl
    _ = (∑ k ∈ range (n + 1), n.choose k * e ^ (n - k) * f ^ k).coeff k := by congr; exact (step6' n)
    _ = (n.choose k : ℕ[X]) * X ^ (n - k) := by
      unfold e f
      rw [finset_sum_coeff, sum_eq_single k]
      . convert coeff_monomial_same _ _
        convert C_mul_X_pow_eq_monomial
        simp
      . intro j hj₁ hj₂
        convert coeff_monomial_of_ne ((n.choose j : ℕ[X]) * X ^ (n - j)) hj₂
        convert C_mul_X_pow_eq_monomial
        simp
      . intro hk
        replace hk : n < k := by linarith [mem_range.not.1 hk]
        rw [choose_eq_zero_of_lt hk]
        simp
