import Mathlib.Tactic

example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  rw [neg_div, neg_div, sub_zero,
      -- normalize terms
      sub_eq_iff_eq_add,
      -- move -(1 / b) to rhs
      ← neg_inj, neg_neg, neg_add, neg_neg, neg_add_eq_sub,
      -- remove neg
      ← div_one (1 / b - c), div_eq_div_iff_comm, div_one
      -- reciprocal both sides
      ] at h
  exact h

example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  apply_fun (fun x => 1 / -(x + (-1 / b))) at h
  -- apply function to both sides, but do not simplify it.
  convert h using 1
  · ring; field_simp -- use `ring` to automatically simplify.
  . ring;

example (a b c : ℝ)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  rw [sub_zero] at h
  rw [← h]
  ring
  -- now goal is a = a⁻¹⁻¹
  -- this indeed do not need a ≠ 0
  field_simp

example (a b c : ℝ)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  by_cases ha : a = 0
  . simp [ha] at h ⊢
    -- a b c : ℝ
    -- ha : a = 0
    -- h : -(-1 / b) = c
    -- ⊢ 0 = b⁻¹ - c
    rw [← h]
    ring
  by_cases hb : b = 0
  . simp [hb] at h ⊢
    -- a b c : ℝ
    -- ha : ¬a = 0
    -- hb : b = 0
    -- h : -1 / a = c
    -- ⊢ a = -(-1 / a)⁻¹
    rw [← h]
    ring
    field_simp
  rw [sub_zero] at h
  rw [← h]
  ring
  field_simp

example (a b c : ℝ)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  apply_fun (fun x => 1 / -(x + (-1 / b))) at h
  linear_combination (norm := field_simp) h
  ring
  sorry



  /-
  Could not parse SageMath output (error: offset 0: unexpected input)
  SageMath output:
  error code: 520Lean 4
  -/



/-

這是一個關於lean寫法的問題，不知道要問哪裡比較好，姑且在這裡問了。

如果目標是交換環內成立的等式，可以用`ring` tactic解決，如果表達式還帶除法的話還可以先用`field_simp`化簡。

但如果是從一個等式推出另一個等式，我就不知道有沒有比較方便的方法了，例如：

```
a b c : ℝ
ha : a ≠ 0
hb : b ≠ 0
h : (-1 / a) - (-1 / b) = c - 0
⊢ a = 1 / (1 / b - c)
```
這個化簡涉及到了幾個步驟，兩側同時加上某個數字，同時消去負號，同時倒數。

我目前想到兩個解法：

1. 用 `rw` 來控制移項的每個步驟
好處用了比較少量的 tactic 。
壞處是真的要一步一步自己寫用到的 theorem 很辛苦。

```
import Mathlib.Tactic

example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  rw [neg_div, neg_div, sub_zero,
      -- normalize terms
      sub_eq_iff_eq_add,
      -- move -(1 / b) to rhs
      ← neg_inj, neg_neg, neg_add, neg_neg, neg_add_eq_sub,
      -- remove neg
      ← div_one (1 / b - c), div_eq_div_iff_comm, div_one
      -- reciprocal both sides
      ] at h
  exact h
```

2. 使用 `apply_fun + convert + ring` 修改原本的假設，再來和目標匹配，使得可以讓 lean 自動用 `ring` 化簡。
好處是讓 `ring` 可以發揮作用，
壞處是中途算式會變得比較龐大。

```
import Mathlib.Tactic

example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
  (h : (-1 / a) - (-1 / b) = c - 0) :
  a = 1 / (1 / b - c) := by
  apply_fun (fun x => 1 / -(x + (-1 / b))) at h
  -- apply function to both sides, but do not simplify it.
  convert h using 1
  · ring; field_simp -- use `ring` to automatically simplify.
  . ring;
```

不知道這樣的情境，有沒有更推薦或更簡便的寫法呢？
-/
