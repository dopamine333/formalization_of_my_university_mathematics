import Mathlib.Tactic

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

example (a b c d e p q : ℝ):
  (a - b) / (c - d) * (e - d) + (p / q)
  ≤ |a - b| / |c - d| * |e - d| + |p / q| := by
  apply ((le_abs_self _).trans (abs_add_le _ _)).trans
  rw [abs_mul, abs_div]
