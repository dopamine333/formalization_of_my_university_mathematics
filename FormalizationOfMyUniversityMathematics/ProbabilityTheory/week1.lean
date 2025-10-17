import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Data.Nat.Factorial.BigOperators


/-
1.
in class, we see the cauchy functional equation i.e.
f(x + y) = f(x) + f(y)
if f : ℚ → ℚ satisfies this, then f is linear.

2.
fix k : ℕ, λ : ℝ
show lim n → ∞, (n.choose k) * (λ / n) ^ k * (1 - λ / n) ^ (n - k)
= exp (-λ) λ^k / k!
-/


#check Rat.num_div_den
#check Rat.forall

theorem cauchy_functional_equation_on_ℚ
  (f : ℚ → ℚ)
  (hf : ∀ x y, f (x + y) = f x + f y) :
  ∃ c, ∀ x, f x = c * x := by

  have key₁ : f 0 = 0 := by
    have := calc
      f 0 = f (0 + 0) := by rw [add_zero]
      _ = f 0 + f 0 := by rw [hf]
    exact add_eq_right.mp this.symm

  have key₂ : ∀ x, f (-x) = - (f x) := by
    intro x
    have := calc
      0 = f (x + (-x)) := by rw [add_neg_cancel, key₁]
      _ = f x + f (-x) := by rw [hf]
    rw [Eq.comm, add_comm, add_eq_zero_iff_eq_neg] at this
    exact this

  have key₃ : ∀ (n : ℕ) (x : ℚ), f (n • x) = n • (f x) := by
    intro n
    induction n with
    | zero => intro x; simp [key₁]
    | succ n ih => intro x; rw [succ_nsmul, hf, ih, succ_nsmul]

  have key₄ : ∀ (k : ℤ) (x : ℚ), f (k • x) = k • (f x) := by
    intro k x
    by_cases hk : k ≥ 0
    · rw [Int.eq_natAbs_of_nonneg hk]
      change f (k.natAbs • x) = k.natAbs • f x
      exact key₃ _ _
    · have : k ≤ 0 := by linarith
      rw [Int.eq_neg_natAbs_of_nonpos this,
          neg_zsmul, key₂, neg_zsmul]
      change -f (k.natAbs • x) = -(k.natAbs • f x)
      rw [key₃]

  use f 1
  rw [Rat.forall]
  intro a b
  by_cases hb : b = 0
  . rw [hb]; simp [key₁]
  have := calc
    f (a • 1) = f (b * (a / b)) := by field_simp
    _ = f (b • (a / b)) := by simp only [zsmul_eq_mul]
  rw [key₄, key₄, zsmul_eq_mul, zsmul_eq_mul] at this
  field_simp
  simpa [mul_comm] using this.symm

#check Nat.descFactorial_eq_prod_range
#check Nat.choose_eq_asc_factorial_div_factorial
#check tendsto_finset_prod
#check Filter.tendsto_congr'
open Filter Real in
open scoped Topology in
theorem binomial_limit (k : ℕ) (c : ℝ) :
  Tendsto
    (fun n ↦ (n.choose k) * (c / n) ^ k * (1 - c / n) ^ (n - k))
    atTop (𝓝 (exp (-c) * c ^ k / k.factorial)) := by
  have : ∀ᶠ n in atTop,
    (n.choose k) * (c / n) ^ k * (1 - c / n) ^ (n - k)
    = (c ^ k / k.factorial) * (1 - c / n) ^ n
    * ((n - k + 1).ascFactorial k) / n ^ k * ((1 - c / n) ^ k)⁻¹ := by
    have hn₁ : ∀ᶠ (n : ℕ) in atTop, c / n < 1 :=
      tendsto_const_div_atTop_nhds_zero_nat c (Iio_mem_nhds zero_lt_one)
    have hn₂ : ∀ᶠ (n : ℕ) in atTop, k ≤ n :=
      eventually_ge_atTop k
    filter_upwards [hn₁, hn₂] with n hn₁ hn₂
    -- the line "filter_upwards ..." is equivalent to
    -- refine (hn₁.and hn₂).mono fun n ⟨hn₁, hn₂⟩ ↦ ?_
    let m := n - k
    have hm : n = m + k := by rw [Nat.sub_add_cancel hn₂]
    replace hn₁ : 1 - c / n ≠ 0 := by linarith
    rw [hm] at hn₁
    rw [hm, Nat.choose_eq_asc_factorial_div_factorial, div_pow]
    conv => rhs; rw [Nat.add_sub_cancel]
    sorry
    -- rw [pow_sub₀ hn₁]
