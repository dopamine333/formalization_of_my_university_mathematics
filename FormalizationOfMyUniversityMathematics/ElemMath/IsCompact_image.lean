import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Basic

open Set

#check IsCompact.image
#check IsCompact.elim_finite_subcover
#check isCompact_of_finite_subcover
#check isCompact_iff_finite_subcover

theorem thm_9_3_2
  {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {f : X → Y} {K : Set X}
  (hK : IsCompact K) (hf : Continuous f) :
  IsCompact (f '' K) := by
  -- Expand the definition of compactness
  rw [isCompact_iff_finite_subcover] at ⊢
  intro ι U hUopen hcover

  -- Pull back each open set along f
  let V := fun i ↦ f ⁻¹' U i
  have hVopen : ∀ i, IsOpen (V i) := fun i ↦ hf.isOpen_preimage _ (hUopen i)
  have hVcover : K ⊆ ⋃ i, V i := by
    intro x hx
    have : f x ∈ ⋃ i, U i := hcover (mem_image_of_mem f hx)
    rcases mem_iUnion.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, hi⟩

  -- Apply compactness of K to get a finite subcover
  rcases hK.elim_finite_subcover V hVopen hVcover with ⟨t, hKsub⟩

  -- Push forward the finite subcover to f '' K
  use t
  intro y hy
  rcases hy with ⟨x, hxK, rfl⟩
  have : x ∈ ⋃ i ∈ t, V i := hKsub hxK
  rcases mem_iUnion₂.1 this with ⟨i, hit, hxV⟩
  exact mem_iUnion₂.2 ⟨i, hit, hxV⟩

theorem thm_9_4
  {X : Type u} [MetricSpace X]
  {f : X → ℝ} {K : Set X} (hK : IsCompact K) (hf : Continuous f) (hK_ne : K.Nonempty) :
  ∃ x_min x_max, x_min ∈ K ∧ x_max ∈ K ∧
    (∀ x ∈ K, f x_min ≤ f x) ∧ (∀ x ∈ K, f x ≤ f x_max) := by
  -- f '' K is compact since f is continuous on K
  have h_image_compact : IsCompact (f '' K) := thm_9_3_2 hK hf

  -- f '' K is nonempty
  have h_fK_nonempty : (f '' K).Nonempty := hK_ne.image f

  -- Compact sets in ℝ have greatest/least elements
  obtain ⟨y_max, hy_max_mem, h_is_max⟩ := h_image_compact.exists_isGreatest h_fK_nonempty
  obtain ⟨y_min, hy_min_mem, h_is_min⟩ := h_image_compact.exists_isLeast h_fK_nonempty

  -- Pull back the witnesses to K
  obtain ⟨x_max, hx_maxK, rfl⟩ := hy_max_mem
  obtain ⟨x_min, hx_minK, rfl⟩ := hy_min_mem


  -- Translate greatest/least on the image to inequalities on K
  have h_max : ∀ x ∈ K, f x ≤ f x_max := fun x hx => h_is_max (mem_image_of_mem f hx)
  have h_min : ∀ x ∈ K, f x_min ≤ f x := fun x hx => h_is_min (mem_image_of_mem f hx)

  -- 5. Return the extremal points
  exact ⟨x_min, x_max, hx_minK, hx_maxK, h_min, h_max⟩
