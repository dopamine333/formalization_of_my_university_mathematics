import Mathlib.Tactic

example (a : EReal) : a ^ 2 ≥ 0 := by
  by_cases h : a ≥ 0
  . exact pow_nonneg h 2
  . have : a < 0 := by exact lt_of_not_ge h
    have h1 : -a > 0 := by exact EReal.neg_pos.mpr this
    have h2 : (-a) ^ 2 ≥ 0 := by exact pow_nonneg h1.le 2
    convert h2 using 1
    simp

example (a : EReal) : a ^ 2 ≥ 0 := by
  obtain h | h := le_or_gt 0 a
  . exact pow_nonneg h 2
  . have : a < 0 := by exact h
    have h1 : -a > 0 := by exact EReal.neg_pos.mpr this
    have h2 : (-a) ^ 2 ≥ 0 := by exact pow_nonneg h1.le 2
    convert h2 using 1
    simp

example (a : EReal) : a ^ 2 ≥ 0 := by
  obtain h | h := em (a ≥ 0)
  . exact pow_nonneg h 2
  . have : a < 0 := by exact lt_of_not_ge h
    have h1 : -a > 0 := by exact EReal.neg_pos.mpr this
    have h2 : (-a) ^ 2 ≥ 0 := by exact pow_nonneg h1.le 2
    convert h2 using 1
    simp

-- for the case hL_fin : L < (T: EReal)
--       have h_upper : ∀ (B : ℝ), (L : EReal) < B → ∃ δ > 0, ∀ x ∈ open_interval c (c + δ), (f x / g x : EReal) < (B : EReal) := by sorry
--     for the case hL_fin : L > (T: EReal)
--       have hB :∀ (B : ℝ),(L : EReal) > B → ∃ δ > 0, ∀ x ∈ open_interval c (c + δ), (f x / g x : EReal) >(B : EReal) := by sorry

theorem cases_lt_top_gt_bot (L : EReal) : L < ⊤ ∨ L > ⊥ := by
  refine L.rec ?_ ?_ ?_ <;> simp

example (L : EReal) : L = L := by
  obtain L_lt_top | L_gt_bot := cases_lt_top_gt_bot L
  . trivial
  . trivial
