import Mathlib.Tactic
import LeanCopilot

lemma exists_pos_lt_lt {a b : ℝ} (ha : a > 0) (hb : b > 0) : ∃ c > 0, c < a ∧ c < b := by
  refine ⟨min a b / 2, ?_, ?_, ?_⟩
  . simp [ha, hb]
  . linarith [min_le_left a b, half_lt_self (a := a)]
  . linarith [min_le_right a b, half_lt_self (a := b)]

example (q : ℝ)(hq : q ≠ 0) :
  ∀ ε > (0 : ℝ), True := by
  intro ε hε
  have hqpos : 2/|q| > 0 := by positivity
  obtain ⟨ε', hε'0, hε'1, hε'2⟩:= exists_pos_lt_lt hε hqpos
  trivial



example (p : ℝ) :
  |p| / (|p| + 1) < 1 := by
  field_simp
  simp

-- (a-b)/(c-d)*(e-d)+(p/q)
-- <=
-- |a-b|/|c-d|*|e-d|+|p/q|
-- how?
#check le_abs_self
#check abs_add_le
#check abs_mul
#check abs_div

example (a b c d e p q : ℝ):
  (a - b) / (c - d) * (e - d) + (p / q)
  ≤ |a - b| / |c - d| * |e - d| + |p / q| := by
  calc (a - b) / (c - d) * (e - d) + (p / q)
    _ ≤ |(a - b) / (c - d) * (e - d) + p / q| := by
      apply le_abs_self
    _ ≤ |(a - b) / (c - d) * (e - d)| + |p / q| := by
      apply abs_add_le
    _ ≤ |(a - b) / (c - d)| * |e - d| + |p / q| := by
      rw [abs_mul]
    _ = |a - b| / |c - d| * |e - d| + |p / q| := by
      rw [abs_div]

-- example (a b c d e p q : ℝ):
--   (a - b) / (c - d) * (e - d) + (p / q)
--   ≤ |a - b| / |c - d| * |e - d| + |p / q| := by
--   calc (a - b) / (c - d) * (e - d) + (p / q)
--     _ ≤ |(a - b) / (c - d) * (e - d) + p / q| := by
--       search_proof
--     _ ≤ |(a - b) / (c - d) * (e - d)| + |p / q| := by
--       search_proof
--     _ ≤ |(a - b) / (c - d)| * |e - d| + |p / q| := by
--       search_proof
--     _ = |a - b| / |c - d| * |e - d| + |p / q| := by
--       search_proof

example (a b c d e p q : ℝ):
  (a - b) / (c - d) * (e - d) + (p / q)
  ≤ |a - b| / |c - d| * |e - d| + |p / q| := by
  calc (a - b) / (c - d) * (e - d) + (p / q)
    _ ≤ |(a - b) / (c - d) * (e - d) + p / q| := by
      exact le_abs_self _
    _ ≤ |(a - b) / (c - d) * (e - d)| + |p / q| := by
      apply abs_add_le
    _ ≤ |(a - b) / (c - d)| * |e - d| + |p / q| := by
      simp_all only [abs_mul, le_refl]
    _ = |a - b| / |c - d| * |e - d| + |p / q| := by
      simp_all only [add_left_inj, mul_eq_mul_right_iff, abs_eq_zero]
      simp [abs_div]

example (a b c d : ℝ) :
  a / b * c + d ≤ |a| / |b| * |c| + |d| := by
  calc a / b * c + d
    _ ≤ |a / b * c + d| := by
      suggest_tactics
    _ ≤ |a / b * c| + |d| := by
      suggest_tactics
    _ ≤ |a / b| * |c| + |d| := by
      suggest_tactics
    _ = |a| / |b| * |c| + |d| := by
      suggest_tactics

example (a b c d e p q : ℝ):
  (a - b) / (c - d) * (e - d) + (p / q)
  ≤ |a - b| / |c - d| * |e - d| + |p / q| := by
  apply ((le_abs_self _).trans (abs_add_le _ _)).trans
  rw [abs_mul, abs_div]
