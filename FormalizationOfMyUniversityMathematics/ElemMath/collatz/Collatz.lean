import Mathlib
import Mathlib.Tactic.Basic
import LeanCopilot
import Mathlib.Data.Nat.Factorization.Basic
open Nat


def odd_nat (n : ℕ) : Prop := n % 2 = 1

instance (n : ℕ) : Decidable (odd_nat n) := by
  unfold odd_nat
  infer_instance


lemma exists_pow_mul_odd_of_odd (n : ℕ) :
  ∃ p : ℕ × ℕ,
    (3 * n + 1) = 2 ^ p.1 * p.2 ∧ Odd p.2 := by
  have h_nonzero : 3 * n + 1 ≠ 0 := by simp
  rcases exists_eq_two_pow_mul_odd h_nonzero with ⟨k, m, hm⟩
  refine ⟨(k, m), ?_, ?_⟩
  · exact hm.2        -- the equality (3*n+1) = 2^k * m
  · exact hm.1        -- Odd m



noncomputable def β (n : ℕ) : ℕ :=
  (Classical.choose (exists_pow_mul_odd_of_odd n)).1

noncomputable def S (n : ℕ) : ℕ :=
  (Classical.choose (exists_pow_mul_odd_of_odd n)).2


lemma β_pos_of_odd (n : ℕ) (hn : Odd n) : β n > 0 := by
  rcases hn with ⟨k, rfl⟩
  have h_even : Even (3*(2*k+1)+1) := by norm_num

  let m := (Classical.choose (exists_pow_mul_odd_of_odd (2*k+1))).2
  have h_fact := Classical.choose_spec (exists_pow_mul_odd_of_odd (2*k+1))
  -- h_fact.1 : 3*(2*k+1)+1 = 2^(β n) * m
  -- h_fact.2 : Odd m

  by_contra h0
  have hb : β (2*k+1) = 0 := by
    have := le_of_not_gt h0
    exact eq_zero_of_le_zero this

  simp only [β] at hb
  rw [hb, pow_zero, one_mul] at h_fact

  -- 拆解 Odd / Even 的存在量詞
  rcases h_even with ⟨ke, he⟩
  rcases h_fact.2 with ⟨ko, ho⟩

  -- 2*ke = 2*ko + 1 → impossible
  omega


--new--
lemma S_odd_of_odd {n : ℕ} : Odd n → Odd (S n) :=
  fun _ => (Classical.choose_spec (exists_pow_mul_odd_of_odd n)).2




lemma syracuse_step_factor (n : ℕ) :
  3 * n + 1 = 2^(β n) * S n :=
by exact (Classical.choose_spec (exists_pow_mul_odd_of_odd n)).1



def collatz_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    n / 2
  else
    3 * n + 1

def iter (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x     => x
  | k+1, x   => iter f k (f x)

/-- Collatz/Syracuse conjecture (computable version) -/
def collatzConjecture : Prop :=
  ∀ x : ℕ, x > 0 → ∃ k : ℕ, iter collatz_step k x = 1

noncomputable def g (x : ℕ) : ℕ → ℕ
  | 0     => 0
  | k+1   => g x k + β (S^[k] x)

noncomputable def R (x : ℕ) : ℕ → ℕ
  | 0     => 0
  | k+1   => 3 * R x k + 2^(g x k)




lemma g_monotone (x : ℕ) : Monotone (g x) := by
  intro k1 k2 hle
  induction hle with
  | refl => rfl
  | step k ih =>
    dsimp [g]
    (expose_names; exact le_add_right_of_le ih)



lemma S_iter_odd (x : ℕ) [hx : Fact (Odd x)] :
  ∀ k : ℕ, Odd (S^[k] x)
| 0     => hx.1
| k+1   => by
    -- 遞歸取出 IH：Odd (S^[k] x)
    have ih : Odd (S^[k] x) := S_iter_odd x k
    -- 對 ih 應用你給的 lemma，得到 Odd (S (S^[k] x))
    have hS : Odd (S (S^[k] x)) := S_odd_of_odd ih
    -- 把 S^[k+1] x 展開成 S (S^[k] x)，然後結束
    simp [Function.iterate_succ_apply'] at hS ⊢
    exact hS


--new--
lemma g_strictMono' (x : ℕ) [hx : Fact (Odd x)] :
  StrictMono (g x) := by
  -- 只需證明 ∀ k, g x k < g x (k+1)
  have hstep : ∀ k, g x k < g x (k+1) := by
    intro k
    -- 展開定義
    simp [g]
    have hodd : Odd (S^[k] x) := S_iter_odd x k
    have hβpos : 0 < β (S^[k] x) := β_pos_of_odd _ hodd
    exact hβpos

  -- 逐步累加到任意 k₁ < k₂
  intros k₁ k₂ hlt
  induction k₂ with
  | zero =>
      -- impossible: k₁ < 0
      exact (Nat.not_lt_zero _ hlt).elim
  | succ k₂ ih =>
      by_cases h : k₁ = k₂
      · subst h
        exact hstep k₁
      · have hlt' : k₁ < k₂ := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) h
        exact lt_trans (ih hlt') (hstep k₂)






@[simp] lemma S_iterate_succ (x k : ℕ) :
  S^[k+1] x = S (S^[k] x) := by rw [Function.iterate_succ_apply']


lemma syracuse_identity (x k : ℕ) :
  3^k * x + R x k = 2^(g x k) * S^[k] x :=
by
  induction k with
  | zero => simp [R, g, Nat.iterate]
  | succ k ih =>
    -- expand R and g
    simp [R, g, Nat.iterate]
    calc
      3^(k+1) * x + (3 * R x k + 2^g x k)
          = 3 * (3^k * x + R x k) + 2^g x k := by ring
      _ = 3 * (2^g x k * S^[k] x) + 2^g x k := by rw [ih]
      _ = 2^g x k * (3 * S^[k] x + 1) := by ring
      _ = 2^g x k * (2^(β (S^[k] x)) * S (S^[k] x)) := by rw [syracuse_step_factor (S^[k] x)]
      _ = 2^g x k * 2^(β (S^[k] x)) * S (S^[k] x) := by
         exact Eq.symm (Nat.mul_assoc (2 ^ g x k) (2 ^ β (S^[k] x)) (S (S^[k] x)))
      _ = 2^(g x k + β (S^[k] x)) * S (S^[k] x) := by rw [Nat.pow_add]
      _ = 2^(g x k + β (S^[k] x)) * S^[k+1] x := by rw [Function.iterate_succ_apply']




/-- Characteristic function of odd numbers -/
def phi (n : ℕ) : ℕ :=
  if n % 2 = 1 then 1 else 0

/-- The h_k map: h_k(n) = (n + 3^k * phi(n)) / 2 -/
def h (k n : ℕ) : ℕ :=
  (n + 3^k * phi n) / 2

/-- Iterate h_k j times -/
def h_iter (k n : ℕ) : ℕ → ℕ
  | 0     => n
  | j+1   => h k (h_iter k n j)


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

      -- 展開 h_iter，套用 IH，加入最後一項
      simp [h_iter, sum_eq, ih]

      -- rewrite 2^(j+1)
      have hpow : 2 ^ (j+1) = 2^j * 2 := by
        simp [pow_succ]

      -- 展開 h 的定義
      --simp [h, hpow, Nat.mul_comm]
      have h1 : (n + 3^k * phi n) / 2 = (n + phi n * 3^k) / 2 := by ring_nf

      dsimp [h]  -- 展開 h 的定義
      set s := (List.map (fun i => phi (h_iter k n i) * 2 ^ i) (List.range j)).sum with hs
      -- 我們要處理 ((n + 3^k * s) / 2^j + 3^k * phi ((n + 3^k * s) / 2^j)) / 2
      -- 用 Nat.div_div_eq_div_mul 把 ( ... / 2^j) / 2 變成 ... / (2^j * 2)
      have hpow2 : 2^(j+1) = 2^j * 2 := by simpa using hpow
      have hdiv :
        ((n + 3 ^ k * s) / 2 ^ j + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j)) / 2
        =((n + 3 ^ k * s) + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j) * 2 ^ j) / (2 ^ j * 2):= by
              -- 利用共同分母把兩個分式合併
          have h1 :
            ((n + 3 ^ k * s) / 2 ^ j + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j))
              =
            ((n + 3 ^ k * s) + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j) * 2 ^ j) / 2^j :=
          by
            have : 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j)
                  = (3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j) * 2^j) / 2^j := by
              refine Nat.eq_div_of_mul_eq_left ?_ rfl
              exact pow_ne_zero _ (by decide)
              --field_simp
            have hpos : (2 ^ j : ℕ) ≠ 0 := by
              simp

            have hrewrite :
                3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j)
                  = 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j) * 2 ^ j / 2 ^ j := by exact this
              --field_simp [hpos]

            refine
              Eq.symm (add_mul_div_right (n + 3 ^ k * s)
              (3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j)) ?_)
              --simp [hrewrite]
            exact Nat.two_pow_pos j
          -- 再除以 2 → 分母乘 2
          -- (A / 2^j) / 2 = A / (2^j * 2)
          calc
            ((n + 3 ^ k * s) / 2 ^ j + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j)) / 2
                = (( (n + 3 ^ k * s) + 3 ^ k *
                phi ((n + 3 ^ k * s) / 2 ^ j) * 2 ^ j) / 2^j) / 2 := by
              rw [h1]
            _ = ((n + 3 ^ k * s) + 3 ^ k * phi ((n + 3 ^ k * s) / 2 ^ j) * 2 ^ j)
            / (2 ^ j * 2) := by
              apply Nat.div_div_eq_div_mul
      rw [hdiv]
      rw [pow_succ]      -- 2^j * 2 = 2^(j+1)
      simp [Nat.mul_add]
      simp [Nat.add_assoc]
      ring_nf

-------------from hsu

/-- Characteristic function of odd numbers -/


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

#check Nat.add_div
#check add_div -- add_div only work for DivisionSemiring
-- #synth DivisionSemiring ℕ -- by ℕ is not a DivisionSemiring

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
----------------end of from hsu on 20251119




-- Define x_k
noncomputable def x_k (x : ℕ) (k : ℕ) : ℕ :=
  ((List.range (g x k)).map (fun i => phi (h_iter k (R x k) i) * 2^i)).sum














--working on




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

lemma exists_k0 (x : ℕ) : ∃ k, k0_pred x k := by
  -- use x+1
  -- have h_iter : (g x (x+1)) ≥ x+1 := by
  --   -- 利用嚴格單調性或 monotone lemma
  --   sorry -- 這裡可以用 g 的單調性歸納或 monotone lemma 完成
  -- have h_pow : 2^(g x (x+1)) ≥ 2^(x+1) := by
  --   apply? --exact Nat.pow_le_pow_left (by norm_num) h_iter
  -- exact lt_of_lt_of_le (pow_two_gt_self x) h_pow
  sorry

open scoped Classical

noncomputable def k₀ (x : ℕ) : ℕ := Nat.find (exists_k0 x)

lemma k₀_spec (x : ℕ) : 2 ^ (g x (k₀ x)) > x :=
  Nat.find_spec (exists_k0 x)

lemma k₀_minimal (x : ℕ) (k : ℕ) (h : 2 ^ (g x k) > x) :
  k₀ x ≤ k :=
  Nat.find_min' (exists_k0 x) h
















--after-working







-- Lemma: for k ≥ k₀, x_k = x and S^k(x) = h_k^{g(k)}(R_k)
-- Here S is assumed defined elsewhere, e.g., the Syracuse map
lemma xk_equals_x_and_Sk_equals_hk {S : ℕ → ℕ} (x : ℕ)
  (k : ℕ) (h_k_large : k ≥ k₀ x) :
  x_k x k = x ∧ (S^[k] x) = h_iter k (R x k) (g x k) := by
  -- proof outline:
  -- 1. By definition of x_k and k₀, 0 ≤ x_k < 2^(g x k)
  -- 2. By the merge formula: 2^(g(k)) * (S^k(x) - h_k^{g(k)}(R_k)) = 3^k * (x - x_k)
  -- 3. Since 0 ≤ x, x_k < 2^(g x k), the difference must be zero: x_k = x
  -- 4. Therefore, S^k(x) = h_iter k (R x k) (g x k)
  sorry

  -- Proof outline:
  -- 1. x_k < 2^(g k) for k ≥ k₀ by definition of k₀
  -- 2. 2^{g(k)} * (S^k(x) - h_k^{g(k)}(R_k)) = 3^k * (x - x_k)
  -- 3. Since 2^{g(k)} and 3^k are coprime, x - x_k divisible by 2^{g(k)}
  -- 4. But 0 ≤ x_k < 2^{g(k)} and x < 2^{g(k)}, so x - x_k = 0
  -- 5. Therefore x_k = x and equality of iterates follows



def unbounded_orbit (x : ℕ) : Prop := ∀ M : ℕ, ∃ k : ℕ, (S^[k] x) > M


-- Lemma: If the orbit is unbounded, then β_k has infinitely many 1's
lemma orbit_unbounded_β_infinite (x : ℕ):
  unbounded_orbit  x → ∀ n : ℕ, ∃ k ≥ n, β k = 1 := by
  sorry


-- Orbit unbounded
open Filter -- brings Tendsto and atTop into scope

--- Lemma 2: If orbit is unbounded, then either 3^k / 2^g(k) → ∞ or R_k / 2^g(k) → ∞
lemma orbit_unbounded_limit_cases (x : ℕ):
  unbounded_orbit x →
  Tendsto (fun k => 3^k / (2 : ℝ) ^ (g x k)) atTop atTop ∨
  Tendsto (fun k => (R x k : ℝ) / (2 : ℝ) ^ (g x k)) atTop atTop := by
  sorry

-- Lemma 3: If 3^k / 2^g(k) → ∞, contradiction
lemma lim_3_over_2g_contradiction (x : ℕ) :
  Tendsto (fun k => 3^k / (2 : ℝ) ^ (g x k)) atTop atTop → False := by
  sorry

-- Lemma 4: If R_k / 2^g(k) → ∞, then limsup g(k)/k ≤ log_2(3)
lemma limR_over_2g_limsup (x : ℕ):
  Tendsto (fun k => (R x k : ℝ) / (2 : ℝ) ^ (g x k)) atTop atTop →
  limsup (fun k => (g x k : ℝ) / k) atTop ≤ Real.log 3 / Real.log 2 := by
  sorry

-- Lemma 5: If limsup g(k)/k > log_2(3), then orbit is periodic → contradiction
lemma limsup_g_over_k_gt_log3_contradiction (x : ℕ):
  limsup (fun k => (g x k : ℝ) / k) atTop > Real.log 3 / Real.log 2 → False := by
  sorry

-- Lemma 6: If limsup g(k)/k = log_2(3), then x → ∞ → contradiction
lemma limsup_g_over_k_eq_log3_contradiction (x : ℕ) :
  limsup (fun k => (g x k : ℝ) / k) atTop = Real.log 3 / Real.log 2 → False := by
  sorry



/-- Main theorem: orbit cannot be unbounded -/
theorem orbit_not_unbounded (x : ℕ) : ¬ unbounded_orbit  x := by
  intro h
  -- Apply lemmas step by step
  apply False.elim
  --exact final_contradiction
  sorry



/-- The Collatz / Syracuse claim: for every starting odd x there exists k with `S^k x = 1`.
    This is the conjecture and thus left unproved (`by admit`). -/
theorem collatz_syracuse_conjecture : ∀ x, odd_nat x → ∃ k, (S^[k] x) = 1 :=
  by admit

--end noncomputable


#check ((↑) : ℕ → ℤ)
#check instNatCastInt
#check Int.ofNat_eq_coe

example (a b : ℤ) : a - b = 0 ↔ a = b := by exact Int.sub_eq_zero

example (n m : ℕ) : (n : ℤ) = (m : ℤ) ↔ n = m := by exact Int.ofNat_inj
#min_imports in
example (n m : ℕ) : (n : ℤ) - (m : ℤ) = 0 ↔ n = m := by
  rw [Int.sub_eq_zero, Int.ofNat_inj]
