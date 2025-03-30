import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

-- variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- variable [IsProbabilityMeasure (ℙ : Measure ℝ)]

#check MeasurableSpace
#check MeasureSpace
#check IsProbabilityMeasure
#check ProbabilityMeasure
#check volume
#synth MeasureSpace ℝ
#check Real.measureSpace
#check Set.Icc
#check Real.volume_univ

example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s

example (a b : ℝ) : ℙ (Set.Icc a b : Set ℝ) = ENNReal.ofReal (b - a) := Real.volume_Icc

example : ℙ (Set.univ : Set ℝ) = ⊤ := Real.volume_univ

-- #check MeasurableSet
#check Measurable

noncomputable example (Ω E : Type) [MeasurableSpace Ω] [MeasurableSpace E]
  (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
  : Measure E := P.map X

noncomputable example (Ω E : Type) [MeasurableSpace Ω] [MeasurableSpace E]
  (P : Measure Ω) (X : Ω → E) (hX : Measurable X) (S : Set E) (hS : MeasurableSet S)
  : (P.map X) S = P (X ⁻¹' S) := Measure.map_apply hX hS

#check gaussianReal
#synth PartialOrder ℕ
#synth PartialOrder Prop
#check DiscreteMeasurableSpace
#check PMF
#check PMF.toMeasure

#check BorelSpace
#check StandardBorelSpace

#check pdf

#check uniformOn
#check IdentDistrib

variable (Ω E : Type) [MeasurableSpace Ω] [MeasurableSpace E]
  (P : Measure Ω) (X : Ω → E) (x : E)
#check P[|X ← x]
