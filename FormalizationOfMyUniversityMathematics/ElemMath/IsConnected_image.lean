import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Connected.Basic


#check Metric.isOpen_iff

/-
# Definition 10.1.
A set S ⊆ ℝᵏ is said to be disconnected
if there exist S₁,S₂ ⊆ ℝᵏ such that
  S₁ ≠ ∅, S₂ ≠ ∅, S = S₁ ∪ S₂, S₁ ∩ S₂ = ∅ and S₁ ∩ S₂ = ∅;
equivalently, if there exist open subsets O₁,O₂ ⊆ ℝᵏ such that,
  O₁ ∩ S ≠ ∅, O₂ ∩ S ≠ ∅, S ⊆ O₁ ∪ O₂ and O₁ ∩ O₂ ∩ S = ∅.
A set S ⊆ ℝᵏ is said to be connected if it is not disconnected.
-/
def MyIsDisconnected {X : Type u} [MetricSpace X] (S : Set X) : Prop :=
  ∃ S₁ S₂ : Set X, S₁ ≠ ∅ ∧ S₂ ≠ ∅ ∧ S = S₁ ∪ S₂ ∧ S₁ ∩ S₂ = ∅

theorem MyIsDisconnected_iff_open {X : Type u} [MetricSpace X] (S : Set X) :
  MyIsDisconnected S ↔
  ∃ O₁ O₂ : Set X, IsOpen O₁ ∧ IsOpen O₂ ∧ O₁ ∩ S ≠ ∅ ∧ O₂ ∩ S ≠ ∅ ∧ S ⊆ O₁ ∪ O₂ ∧ O₁ ∩ O₂ ∩ S = ∅ := sorry

def MyIsConnected {X : Type u} [MetricSpace X] (S : Set X) : Prop :=
  ¬ MyIsDisconnected S

-- MyIsConnected equivalent to Mathlib's IsPreconnected
theorem MyIsConnected_iff_IsPreconnected {X : Type u} [MetricSpace X] {S : Set X} :
    MyIsConnected S ↔ IsPreconnected S := by
    constructor
    . intro h
      rw [MyIsConnected, MyIsDisconnected_iff_open] at h
      push_neg at h
      rw [IsPreconnected]
      intro u v hu hv hSuv hSu hSv
      rw [Set.inter_comm] at hSu hSv
      have := h u v hu hv hSu hSv hSuv
      rw [Set.inter_comm] at this
      exact this
    . intro h
      rw [MyIsConnected, MyIsDisconnected_iff_open]
      push_neg
      rw [IsPreconnected] at h
      intro O₁ O₂ hO₁ hO₂ hO₁S hO₂S hO₁O₂S
      rw [Set.inter_comm] at hO₁S hO₂S
      have := h O₁ O₂ hO₁ hO₂ hO₁O₂S hO₁S hO₂S
      rw [Set.inter_comm] at this
      exact this

-- MyIsConnected and Nonempty is equivalent to Mathlib's IsConnected
theorem MyIsConnected_iff_IsConnected {X : Type u} [MetricSpace X] {S : Set X} (hS : S.Nonempty) :
    MyIsConnected S ↔ IsConnected S := by
    constructor
    . intro h
      rw [MyIsConnected_iff_IsPreconnected] at h
      exact ⟨hS, h⟩
    . intro h
      rw [MyIsConnected_iff_IsPreconnected]
      exact h.2

theorem MyIsConnected_iff_open {X : Type u} [MetricSpace X] {S : Set X} :
    MyIsConnected S ↔
    ∀ O₁ O₂ : Set X, IsOpen O₁ → IsOpen O₂ →
      (O₁ ∩ S ≠ ∅ → O₂ ∩ S ≠ ∅ → S ⊆ O₁ ∪ O₂ → O₁ ∩ O₂ ∩ S ≠ ∅) := by
    rw [MyIsConnected, MyIsDisconnected_iff_open]
    push_neg
    rfl

theorem MyIsConnected_image {X Y : Type u} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Continuous f) {S : Set X} (hS : MyIsConnected S) :
    MyIsConnected (f '' S) := by
    simp_rw [MyIsConnected_iff_open, ← Set.nonempty_iff_ne_empty] at hS ⊢
    intro O₁ O₂ hO₁ hO₂ hO₁fS hO₂S hO₁O₂S
    let U₁ := f ⁻¹' O₁
    let U₂ := f ⁻¹' O₂
    have hU₁ : IsOpen U₁ := hf.isOpen_preimage O₁ hO₁
    have hU₂ : IsOpen U₂ := hf.isOpen_preimage O₂ hO₂
    have hU₁S : (U₁ ∩ S).Nonempty := by
      obtain ⟨_, hfxO₁, ⟨x, hxS, rfl⟩⟩ := hO₁fS
      use x
      have : x ∈ U₁ := hfxO₁
      exact ⟨this, hxS⟩
    have hU₂S : (U₂ ∩ S).Nonempty := by
      obtain ⟨_, hfxO₂, ⟨x, hxS, rfl⟩⟩ := hO₂S
      exact ⟨x, hfxO₂, hxS⟩
    have hU₁U₂S : S ⊆ U₁ ∪ U₂ := by
      calc
        S ⊆ f ⁻¹' (f '' S) := Set.subset_preimage_image f S
        _ ⊆ f ⁻¹' (O₁ ∪ O₂) := Set.preimage_mono hO₁O₂S
        _ = U₁ ∪ U₂ := Set.preimage_union
    have hU₁U₂S : (U₁ ∩ U₂ ∩ S).Nonempty := hS U₁ U₂ hU₁ hU₂ hU₁S hU₂S hU₁U₂S
    obtain ⟨x, ⟨⟨hxU₁, hxU₂⟩, hxS⟩⟩ := hU₁U₂S
    use f x
    refine ⟨⟨hxU₁, hxU₂⟩, ?_⟩
    exact ⟨x, hxS, rfl⟩

theorem MyIsConnected_nonempty_image {X Y : Type u} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Continuous f) {S : Set X} (hS : S.Nonempty)
    (hconn : MyIsConnected S) : (f '' S).Nonempty ∧ MyIsConnected (f '' S) := by
    exact ⟨hS.image f, MyIsConnected_image f hf hconn⟩

#check MyIsConnected_image
#check IsPreconnected.image
#check IsConnected.image
#check MyIsConnected_nonempty_image
