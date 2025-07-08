import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff

open Nat Polynomial

#check choose
#check X
#check C
#check coeff

-- Gaol :
-- theorem binomial_thm (n k: ℕ) : ((1 + X) ^ n).coeff k = choose n k := sorry

#check choose_eq_factorial_div_factorial

#check choose.eq_1
#check choose.eq_2
#check choose.eq_3

theorem choose_is_defined_by_pascal's_formula {f : ℕ → ℕ → ℕ}
  (eq_1 : ∀ n, f n 0 = 1)
  (eq_2 : ∀ k, f 0 (k + 1) = 0)
  (eq_3 : ∀ n k, f (n + 1) (k + 1) = f n k + f n (k + 1))
  : ∀ n k, f n k = choose n k := by
  intro n
  induction' n with n hn
  . intro k
    cases' k with k
    . rw [eq_1]
      rfl
    . rw [eq_2]
      rfl
  . intro k
    cases' k with k
    . rw [eq_1]
      rfl
    . rw [eq_3]
      rw [hn k, hn (k + 1)]
      rfl

noncomputable def binomial_coeff (n k : ℕ) : ℕ := ((1 + X) ^ n).coeff k

#check binomial_coeff.eq_1

theorem binomial_coeff_eq_1 (n : ℕ) : binomial_coeff n 0 = 1 := by
  unfold binomial_coeff
  induction' n with n hn
  . rw [pow_zero]
    rw [coeff_one_zero]
  . rw [pow_succ]
    rw [mul_coeff_zero, hn]
    rw [coeff_add]
    rw [coeff_one_zero, coeff_X_zero]
    norm_num
theorem binomial_coeff_eq_1' (n : ℕ) : binomial_coeff n 0 = 1 := by
  unfold binomial_coeff
  induction' n with n hn
  . simp
  . rw [pow_succ]
    simp [hn]
theorem binomial_coeff_eq_2 (k : ℕ) : binomial_coeff 0 (k + 1) = 0 := by
  unfold binomial_coeff
  rw [pow_zero]
  rw [Polynomial.coeff_one]
  norm_num
#check coeff_X_mul
theorem binomial_coeff_eq_3 (n k : ℕ) : binomial_coeff (n+1) (k+1) = binomial_coeff n k + binomial_coeff n (k+1) := by
  unfold binomial_coeff
  calc ((1 + X) ^ (n + 1)).coeff (k + 1)
   _ = ((1 + X) ^ n * (1 + X)).coeff (k + 1)  := by congr
   _ = ((1 + X) ^ n + X * (1 + X) ^ n).coeff (k + 1) := by congr; ring
   _ = ((1 + X) ^ n).coeff (k + 1) + (X * (1 + X) ^ n).coeff (k + 1) := by rw [coeff_add]
   _ = ((1 + X) ^ n).coeff (k + 1) + ((1 + X) ^ n).coeff k := by rw [coeff_X_mul]
   _ = ((1 + X) ^ n).coeff k + ((1 + X) ^ n).coeff (k + 1) := by ring

theorem test_ext (f g : ℕ → ℕ → ℕ) : (f = g) → (∀ n k, f n k = g n k) := by
  exact fun a n k ↦ congrFun (congrFun a n) k

theorem binomial_thm (n k : ℕ) : ((1 + X) ^ n).coeff k = choose n k := by
  refine @choose_is_defined_by_pascal's_formula (fun n k ↦ ((1 + X) ^ n).coeff k) ?_ ?_ ?_ n k
  . exact binomial_coeff_eq_1
  . exact binomial_coeff_eq_2
  . exact binomial_coeff_eq_3
