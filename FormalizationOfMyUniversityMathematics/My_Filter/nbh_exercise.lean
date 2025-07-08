import Mathlib.Topology.MetricSpace.Defs


open Filter Topology
-- open scoped Topology

-- This is how we can talk about two topological spaces X and Y
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-
Given a topological space `X` and some `A : set X`, we have the usual zoo of predicates
`is_open A`, `is_closed A`, `is_connected A`, `is_compact A` (and some more)

There are also additional type classes referring to properties of `X` itself,
like `compact_space X` or `connected_space X`
-/


/-- We can talk about continuous functions from `X` to `Y` -/
example (f : X → Y) : Continuous f ↔ ∀ V, IsOpen V → IsOpen (f ⁻¹' V) := continuous_def

/- Each point `x` of a topological space has a neighborhood filter `𝓝 x`
   made of sets containing an open set containing `x`.
   It is always a proper filter, as recorded by `nhds_ne_bot`
   Asking for continuity is the same as asking for continuity at each point
   the right-hand side below is known as `continuous_at f x` -/
example (f : X → Y) : Continuous f ↔ ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) := continuous_iff_continuousAt

#check HasBasis.tendsto_iff
#check HasBasis.tendsto_left_iff

#check nhds_basis_opens
#check nhds_basis_closeds
#loogle T3Space