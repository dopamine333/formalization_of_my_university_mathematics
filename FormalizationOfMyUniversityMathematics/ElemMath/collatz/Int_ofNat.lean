import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

example (n m : ℕ) : n - m = 0 ↔ n ≤ m := by
  rw [Nat.sub_eq_zero_iff_le]

example (n m : ℕ) : (n : ℤ) - (m : ℤ) = 0 ↔ n = m := by
  rw [Int.sub_eq_zero, Int.ofNat_inj]
