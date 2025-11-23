import Mathlib

#check Even
#check Odd
#check Nat.even_iff
#check Nat.odd_iff
#check Odd.add_even
#check if_pos
#check if_neg
-- # suggest use Odd n in definition of phi
/-- Characteristic function of odd numbers -/
def phi (n : ℕ) : ℕ :=
  if n % 2 = 1 then 1 else 0

def phi' (n : ℕ) : ℕ :=
  if Odd n then 1 else 0
example {n : ℕ} (h : Odd n) : 2 * ∑ _ ∈ Finset.range 5, phi' n = 10 := by
  rw [phi', if_pos h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

#check Nat.div_two_mul_two_of_even
#check Nat.two_mul_div_two_of_even
#check Nat.div_two_mul_two_add_one_of_odd
#check Nat.two_mul_div_two_add_one_of_odd
-- # division in ℕ is floor division i.e. n / d = ⌊ n / d ⌋, be careful when using it
/-- The h_k map: h_k(n) = (n + 3^k * phi(n)) / 2 -/
def h (k n : ℕ) : ℕ :=
  (n + 3^k * phi n) / 2

def h' (k n : ℕ) : ℕ :=
  (n + 3 ^ k * phi' n) / 2

lemma two_mul_h' (k n : ℕ) :
  2 * h' k n = n + 3 ^ k * phi' n := by
  -- need to show the numerator is even for all n k
  have : Even (n + 3 ^ k * phi' n) := by
    by_cases hn : Odd n
    . rw [phi', if_pos hn]
      have : Odd 3 := by norm_num
      exact hn.add_odd (this.pow.mul odd_one)
    . rw [phi', if_neg hn, mul_zero, add_zero]
      rwa [Nat.not_odd_iff_even] at hn
  rw [h', Nat.two_mul_div_two_of_even this]

#check Nat.iterate
#check Function.iterate_zero
#check Function.iterate_succ
#check Function.iterate_succ'
#check Function.iterate_add
#check Function.iterate_mul
-- # suggest use h^[j] in definition of h_iter
/-- Iterate h_k j times -/
def h_iter (k n : ℕ) : ℕ → ℕ
  | 0     => n
  | j+1   => h k (h_iter k n j)

def h'_iter (k n j : ℕ) : ℕ := (h' k)^[j] n

lemma h'_iter_zero (k n : ℕ) : h'_iter k n 0 = n := by
  simp [h'_iter, Function.iterate_zero]
lemma h'_iter_succ  (k n j: ℕ) : h'_iter k n (j + 1) = h'_iter k (h' k n) j := by
  simp [h'_iter]
lemma h'_iter_succ' (k n j: ℕ) : h'_iter k n (j + 1) = (h' k) (h'_iter k n j) := by
  simp only [h'_iter, Function.iterate_succ']
  rfl

#check Finset.sum_range_zero
#check Finset.sum_range_succ
#check Finset.sum_mul
#check Finset.sum_le_sum
-- # suggest use ∑ i ∈ range j, ... in lemma h_iter_explicit
-- # notice range 5 = {0, 1, 2, 3, 4}, it count start from 0
lemma h_iter_explicit (k n j : ℕ) :
  h_iter k n j =
    (n + 3^k * ((List.range j).map (fun i => phi (h_iter k n i) * 2^i)).sum) / 2^j := by
  induction j with
  | zero =>
      simp [h_iter]
  | succ j ih =>
      have sum_eq :
        ((List.range (j+1)).map (fun i => phi (h_iter k n i) * 2^i)).sum =
        ((List.range j).map (fun i => phi (h_iter k n i) * 2^i)).sum
          + phi (h_iter k n j) * 2^j := by
        simp [List.range_succ, List.map_append]
      simp [h_iter, sum_eq, ih]
      have hpow : 2 ^ (j+1) = 2^j * 2 := by
        simp [pow_succ]
      sorry

#check Nat.add_div
#check add_div -- add_div only work for DivisionSemiring
-- by ℕ is not a DivisionSemiring, uncommented the following line to see that
-- #synth DivisionSemiring ℕ

open Finset in
lemma h'_iter_explicit (k n j : ℕ) :
  -- use 2 ^ j * a = b rather then a = b / 2 ^ j is less less cumbersome when working over ℕ
  2 ^ j * h'_iter k n j =
    n + 3 ^ k * ∑ i ∈ range j, phi' (h'_iter k n i) * 2 ^ i := by
  induction j with
  | zero => rw [h'_iter_zero, sum_range_zero]; norm_num
  | succ j ih =>
    calc 2 ^ (j + 1) * h'_iter k n (j + 1)
      _ = 2 ^ j * (2 * h' k (h'_iter k n j)) := by
        rw [h'_iter_succ']; ring
      _ = 2 ^ j * h'_iter k n j + 3 ^ k * phi' (h'_iter k n j) * 2 ^ j := by
        rw [two_mul_h']; ring
      _ = n + 3 ^ k * ∑ i ∈ range j, phi' (h'_iter k n i) * 2 ^ i
          + 3 ^ k * phi' (h'_iter k n j) * 2 ^ j  := by
        rw [ih]
      _ = n + 3 ^ k * ∑ i ∈ range (j + 1), phi' (h'_iter k n i) * 2 ^ i := by
        rw [sum_range_succ]
        ring


-- use Nat.find to implement the ceil funciton (only make sense for x ≥ 0)
theorem exist_my_ceil (x : ℝ) : ∃ n : ℕ, x ≤ n := by exact exists_nat_ge x

noncomputable def my_ceil (x : ℝ) : ℕ := Nat.find (exist_my_ceil x)

noncomputable def my_ceil' (x : ℝ) : ℕ := Nat.find (by exact exists_nat_ge x)

theorem le_my_ceil (x : ℝ) : x ≤ my_ceil x := Nat.find_spec (exist_my_ceil x)

theorem my_ceil_lt_add_one (x : ℝ) (h : x ≥ 0) : my_ceil x < x + 1 := by
  by_contra!
  have h : 1 ≤ my_ceil x := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
    linarith
  have : x ≤ ↑(my_ceil x - 1) := by
    calc x
      _ = (x + 1) - 1 := by ring
      _ ≤ ↑(my_ceil x) - 1 := by gcongr
      _ = ↑(my_ceil x - 1) := by
        rw [Nat.cast_sub h, Nat.cast_one]
  have : my_ceil x ≤ my_ceil x - 1 := Nat.find_min' (exist_my_ceil x) this
  have : my_ceil x - 1 < my_ceil x := by
    apply Nat.sub_one_lt
    linarith
  linarith



-- 假設 g : ℕ → ℕ → ℕ 並且對第二個參數單調
variable (g : ℕ → ℕ → ℕ)
variable (g_monotone : ∀ x, Monotone (g x))


-- Predicate：2^((g x)^[k] 0) > x
def k0_pred (x k : ℕ) : Prop := 2 ^ (g x k) > x

lemma pow_two_gt_self : ∀ x : ℕ, 2^(x+1) > x := by
  -- intro x
  -- induction x with
  -- | zero => simp
  -- | succ n ih =>
  --   calc
  --     2^(n+2) = 2*2^(n+1) := by exact Nat.pow_succ'
  --     _ > 2*(n+1)        := by sorry --sorry --mul_lt_mul_of_pos_left ih (by norm_num)
  --     _ ≥ n+2            := by linarith
    sorry

lemma exists_k0 (x : ℕ) : ∃ k, k0_pred g x k := by
  -- use x+1
  -- have h_iter : (g x (x+1)) ≥ x+1 := by
  --   -- 利用嚴格單調性或 monotone lemma
  --   sorry -- 這裡可以用 g 的單調性歸納或 monotone lemma 完成
  -- have h_pow : 2^(g x (x+1)) ≥ 2^(x+1) := by
  --   apply? --exact Nat.pow_le_pow_left (by norm_num) h_iter
  -- exact lt_of_lt_of_le (pow_two_gt_self x) h_pow
  sorry

noncomputable def k₀ (x : ℕ) : ℕ := Classical.choose (exists_k0 g x)

-- lemma S_odd_of_odd {n : ℕ} : Odd n → Odd (S n) :=
--   fun _ => (Classical.choose_spec (exists_pow_mul_odd_of_odd n)).2

--new--
-- lemma g_strictMono' (x : ℕ) [hx : Fact (Odd x)] :
--   StrictMono (g x) := by
--   -- 只需證明 ∀ k, g x k < g x (k+1)
--   have hstep : ∀ k, g x k < g x (k+1) := by
--     intro k
--     -- 展開定義
--     simp [g]
--     have hodd : Odd (S^[k] x) := S_iter_odd x k
--     have hβpos : 0 < β (S^[k] x) := β_pos_of_odd _ hodd
--     exact hβpos

--   -- 逐步累加到任意 k₁ < k₂
--   intros k₁ k₂ hlt
--   induction k₂ with
--   | zero =>
--       -- impossible: k₁ < 0
--       exact (Nat.not_lt_zero _ hlt).elim
--   | succ k₂ ih =>
--       by_cases h : k₁ = k₂
--       · subst h
--         exact hstep k₁
--       · have hlt' : k₁ < k₂ := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) h
--         exact lt_trans (ih hlt') (hstep k₂)
