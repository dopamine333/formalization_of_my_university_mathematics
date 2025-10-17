import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.UniformOn

open MeasureTheory  ProbabilityTheory Measure
open scoped ENNReal

noncomputable section


#synth Monad PMF
#synth LawfulMonad PMF

#check uniformOn_isProbabilityMeasure
#check Measure.toPMF

abbrev dice_outcome : Set ℕ := {1,2,3,4,5,6}
theorem dice_outcome_finite : dice_outcome.Finite := Set.toFinite _
theorem dice_outcome_nonempty : dice_outcome.Nonempty := Set.insert_nonempty _ _

def dice : PMF ℕ :=
  haveI := uniformOn_isProbabilityMeasure dice_outcome_finite dice_outcome_nonempty
  (ProbabilityTheory.uniformOn dice_outcome).toPMF

theorem dice_apply : ∀ i ∈ dice_outcome, dice i = 1 / 6 := by
  intro i hi
  rw [dice, Measure.toPMF_apply,
      uniformOn, cond_apply .of_discrete,
      Measure.count_apply_finite _ dice_outcome_finite,
      Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hi), count_singleton]
  simp

theorem dice_apply_eq_zero : ∀ i ∉ dice_outcome, dice i = 0 := by
  intro i hi
  rw [dice, Measure.toPMF_apply, ← uniformOn_inter_self dice_outcome_finite,
      Set.inter_singleton_eq_empty.2 hi , uniformOn_empty]

def roll_two_dice : PMF ℕ := do
  let x ← dice
  let y ← dice
  return x + y

/-
roll_two_dice = 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12
with probabity (1  2  3  4  5  6  5  4  3   2   1)/36
-/

theorem roll_two_dice_apply_7 : roll_two_dice 7 = 6 / 36 := by
  calc roll_two_dice 7
    _ = PMF.bind dice (fun x ↦
        PMF.bind dice (fun y ↦
        PMF.pure (x + y))) 7 := rfl
    _ = ∑' x, dice x *
        ∑' y, dice y *
        PMF.pure (x + y) 7 := by simp
    _ = ∑' x, dice x *
        ∑ y ∈ dice_outcome, dice y *
        PMF.pure (x + y) 7 := by
        congr! 3
        refine tsum_eq_sum (fun y hy ↦ ?_)
        rw [Set.mem_toFinset.not] at hy
        rw [dice_apply_eq_zero y hy, zero_mul]
    _ = ∑ x ∈ dice_outcome, dice x *
        ∑ y ∈ dice_outcome, dice y *
        PMF.pure (x + y) 7 := by
        refine tsum_eq_sum (fun x hx ↦ ?_)
        rw [Set.mem_toFinset.not] at hx
        rw [dice_apply_eq_zero x hx, zero_mul]
    _ = 6 / 36 := by
      simp [dice_apply]
      ring_nf
      rw [← ENNReal.inv_pow, ENNReal.div_eq_inv_mul]
      norm_num
