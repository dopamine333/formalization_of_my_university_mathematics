import Mathlib.Topology.Compactness.Compact

open Set

#check IsCompact.image
#check IsCompact.elim_finite_subcover
#check isCompact_of_finite_subcover
#check isCompact_iff_finite_subcover

theorem IsCompact_image
  {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {K : Set X}
  (hK : IsCompact K) (hf : Continuous f) :
  IsCompact (f '' K) := by
  -- Expand the definition of compactness
  rw [isCompact_iff_finite_subcover] at hK ⊢
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
  rcases hK V hVopen hVcover with ⟨t, hKsub⟩

  -- Push forward the finite subcover to f '' K
  use t
  intro y hy
  rcases hy with ⟨x, hxK, rfl⟩
  have : x ∈ ⋃ i ∈ t, V i := hKsub hxK
  rcases mem_iUnion₂.1 this with ⟨i, hit, hxV⟩
  exact mem_iUnion₂.2 ⟨i, hit, hxV⟩

theorem IsCompact_image'
  {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
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


def compact_via_finite_subcover.{u, v}
  {X : Type u} [TopologicalSpace X] (S : Set X) : Prop :=
  ∀ {ι : Type v} (U : ι → Set X),
    (∀ i, IsOpen (U i)) →
    S ⊆ ⋃ i, U i →
    ∃ t : Finset ι, S ⊆ ⋃ i ∈ t, U i

theorem IsCompact_image''
  {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {K : Set X}
  (hK : compact_via_finite_subcover K) (hf : Continuous f) :
  compact_via_finite_subcover (f '' K) := by
  -- Expand the definition of compactness
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
  rcases hK V hVopen hVcover with ⟨t, hKsub⟩

  -- Push forward the finite subcover to f '' K
  use t
  intro y hy
  rcases hy with ⟨x, hxK, rfl⟩
  have : x ∈ ⋃ i ∈ t, V i := hKsub hxK
  rcases mem_iUnion₂.1 this with ⟨i, hit, hxV⟩
  exact mem_iUnion₂.2 ⟨i, hit, hxV⟩
