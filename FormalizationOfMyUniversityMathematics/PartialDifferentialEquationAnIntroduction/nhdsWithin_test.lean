import Mathlib.Topology.ContinuousOn


open scoped Topology Filter

#check nhdsWithin
#check mem_nhdsWithin_iff_eventually
example {α : Type u} [TopologicalSpace α ] (s t: Set α) (x : α)  :
  t ∈ 𝓝[s] x ↔ ∃ U ∈ 𝓝 x, U ∩ s ⊆ t := by
  exact mem_nhdsWithin_iff_exists_mem_nhds_inter

#check Filter.instInf
example {α : Type u} [TopologicalSpace α] (s t: Set α) (x : α)  :
  t ∈ 𝓝[s] x ↔ ∃ U ∈ 𝓝 x, U ∩ s ⊆ t := by
  simp_rw [
    nhdsWithin,
    Filter.mem_inf_iff,
    Filter.mem_principal]
  constructor
  . rintro ⟨U, hU, s', hs', rfl⟩
    refine ⟨U, hU, ?_⟩
    intro x ⟨hxU, hxs⟩
    exact ⟨hxU, hs' hxs⟩
  . rintro ⟨U, hU, h⟩
    refine ⟨U ∪ t, ?_, s ∪ t, ?_, ?_⟩
    . apply Filter.mem_of_superset hU
      tauto
    . tauto
    rw [← Set.inter_union_distrib_right, Set.union_eq_right.2 h]

#check Filter.mem_sup
#check Filter.mem_inf_iff
#check nhdsWithin
example {α : Type u} [TopologicalSpace α] (s : Set α) (x : α)  :
  𝓝[s] x = 𝓝 x ⊓ 𝓟 s := rfl

example {α : Type u} [TopologicalSpace α] (s : Set α) (x : α)  :
  𝓝[s] x ≤ 𝓝 x := inf_le_left
example {α : Type u} [TopologicalSpace α] (s : Set α) (x : α)  :
  𝓝[s] x ≤ 𝓟 s := inf_le_right

-- irreducible_def nhds (x : X) : Filter X :=
--   ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

example {α : Type u} [TopologicalSpace α] (s : Set α) (x : α) (h : x ∈ s ∧ IsOpen s) :
  𝓝 x ≤ 𝓟 s := by
  calc 𝓝 x
    _ = ⨅ t ∈ {s | x ∈ s ∧ IsOpen s}, 𝓟 t := by rw [nhds]
    _ = (⨅ (t : Set α), ⨅ (_ : t ∈ {s | x ∈ s ∧ IsOpen s}), 𝓟 t) := rfl
    _ ≤ (⨅ (_ : s ∈ {s | x ∈ s ∧ IsOpen s}), 𝓟 s) :=
      iInf_le (fun t ↦ (⨅ (_ : t ∈ {s | x ∈ s ∧ IsOpen s}), 𝓟 t)) s
    _ ≤ 𝓟 s:= iInf_le (fun h' : s ∈ {s | x ∈ s ∧ IsOpen s} ↦ 𝓟 s) h
