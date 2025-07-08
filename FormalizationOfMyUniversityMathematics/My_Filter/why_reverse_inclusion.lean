import Mathlib.Topology.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic

#check TopologicalSpace

example {X : Type} {τ τ': TopologicalSpace X}
    : τ ≤ τ' ↔ ∀ s : Set X, τ'.IsOpen s → τ.IsOpen s := by
  rfl

#check TopologicalSpace.instPartialOrder


open scoped MeasureTheory

example {α :Type} {m m' : MeasurableSpace α}
    : m ≤ m' ↔ ∀ s : Set α, MeasurableSet[m] s → MeasurableSet[m'] s := by
  rfl

#check MeasurableSpace.instPartialOrder
