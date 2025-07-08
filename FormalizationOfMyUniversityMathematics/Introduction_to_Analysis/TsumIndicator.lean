/-
  tsum_indicator_eq_card.lean
  Lean 4 + mathlib4 ≥ 4.10.0
-/

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Set.Countable

open Classical Set
open scoped BigOperators ENNReal

#check tendsto_prod_nat_add

noncomputable section

variable {I X : Type*} [Countable I]

/-- `(0,1)`-indicator valued in `ℝ≥0∞`. -/
def ind (E : I → Set X) (x : X) (i : I) : ℝ≥0∞ :=
  if _ : x ∈ E i then 1 else 0

/-- Helper: rewrite the big sum over `I` as a sum over the relevant subtype. -/
lemma tsum_ind_eq_subtype (E : I → Set X) (x : X) :
    (∑' i : I, ind E x i) =
      ∑' i : {i : I // x ∈ E i}, (1 : ℝ≥0∞) := by
  classical
  -- `tsum_eq_tsum_subtype` is the Lean-4 name of the old lemma
  simpa [ind] using
    tsum_eq_tsum_subtype (f := fun i : I ↦ (if _ : x ∈ E i then (1 : ℝ≥0∞) else 0))

/-- **Main theorem**:
`∑' i, ind E x i = #( { i | x ∈ E i } )`, valued in `ℝ≥0∞`. -/
theorem tsum_ind_eq_card (E : I → Set X) (x : X) :
    (∑' i, ind E x i) =
      if h : (Set.Finite {i : I | x ∈ E i})
      then (h.toFinset.card : ℝ≥0∞)
      else (∞) := by
  classical
  -- Step 1 : reduce to the subtype
  have := tsum_ind_eq_subtype (I := I) E x
  -- Now distinguish the finite / infinite cases
  by_cases hfin : (Set.Finite {i : I | x ∈ E i})
  · -- **finite** case
    haveI : Fintype {i : I // x ∈ E i} := hfin.fintype
    have h' : (∑' i : {i : I // x ∈ E i}, (1 : ℝ≥0∞)) =
        (Fintype.card {i : I // x ∈ E i} : ℝ≥0∞) := by
      simpa using tsum_fintype (fun _ : {i : I // x ∈ E i} ↦ (1 : ℝ≥0∞))
    simpa [this, h, hfin, dif_pos hfin] using this
  · -- **infinite** case
    have : (∑' i : {i : I // x ∈ E i}, (1 : ℝ≥0∞)) = ∞ := by
      -- a non-zero constant over an infinite type is not summable
      have hns : ¬ Summable (fun _ : {i : I // x ∈ E i} ↦ (1 : ℝ≥0∞)) := by
        simpa using summable_const_nz.mpr (by simp)
      simpa using tsum_eq_top_of_not_summable hns
    simpa [this, h, hfin, dif_neg hfin] using this
