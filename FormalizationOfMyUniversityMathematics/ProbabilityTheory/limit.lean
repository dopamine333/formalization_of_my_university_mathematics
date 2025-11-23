import Mathlib
-- import Mathlib.Probability.StrongLaw
-- import Mathlib.Order.LiminfLimsup


open MeasureTheory Filter Finset Asymptotics ProbabilityTheory

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal


#check strong_law_ae

#check MeasureTheory.TendstoInMeasure.congr'

#check MeasureTheory.tendstoInMeasure_of_tendsto_ae

#check Filter.limsup_le_iff
#check Filter.le_limsup_iff

#check ConditionallyCompleteLattice
#check CompleteLattice

example {α : Type} : ConditionallyCompleteLattice (Set α) := inferInstance
example {α : Type} : CompleteLattice (Set α) := inferInstance
-- example {α : Type} : ConditionallyCompleteLinearOrder (Set α) := inferInstance

-- example {Ω : Type} (E : ℕ → Set Ω) (F : Set Ω) :
--   limsup E atTop ⊆ F ↔ ∀ G ⊃ F, ∀ᶠ n in atTop, E n ⊂ G := by
--   -- refine Filter.limsup_le_iff ?_ ?_
--   sorry

  -- apply Filter.limsup_le_iff'

#check MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff

-- |aₙ - L| ≥ ε 一直發生 那麼 ∃ subsequence {a_σ(n)}, ∀ n, |a_σ(n) - L| ≥ ε
#check ae_all_iff
#check Measure.ae_count_iff
#check ae
-- ∀ᶠ ω in ae μ, ∀ n : ℕ, ω ∈ E n ↔ ∀ n : ℕ, ∀ᶠ ω in ae μ, ω ∈ E n

#check extraction_forall_of_eventually

#check TendstoInMeasure.exists_seq_tendsto_ae

#check measure_limsup_eq_one
#check measure_limsup_atTop_eq_zero

#check AECover.ae_eventually_mem

-- set_option trace.Meta.synthInstance true in
example : MeasurableSpace ℝ := inferInstance
#check Real.measurableSpace
-- set_option trace.Meta.synthInstance true in
example : MeasurableSpace EReal := inferInstance
#check EReal.measurableSpace
