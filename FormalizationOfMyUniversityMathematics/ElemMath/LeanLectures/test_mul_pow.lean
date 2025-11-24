import Mathlib.Tactic

#check mul_sub
#check Nat.mul_sub
#check mul_tsub
#check pow_add
#check Nat.sub_add_cancel
#check add_tsub_cancel_of_le
example (k i : ℕ) (hi : i ≤ k) :
  2 ^ i * (3 ^ k - 2 ^ (k - i)) = 3 ^ k * 2 ^ i - 2 ^ k := by
  rw [mul_tsub] -- or rw [Nat.mul_sub]
  rw [← pow_add]
  rw [Nat.add_sub_cancel' hi] -- or rw [add_tsub_cancel_of_le hi]
  rw [mul_comm]
