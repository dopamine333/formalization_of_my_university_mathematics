import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Commutator.Finite
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.Finsupp


#check commutatorElement
#check commutatorSet
#check commutator
#check Subgroup.commutator

example {G : Type u} [Group G] (a b : G)
  : commutatorElement.bracket a b  = ⁅a, b⁆ := rfl

example {G : Type u} [Group G] (a b : G)
  : a * b * a⁻¹ * b⁻¹ = ⁅a, b⁆ := rfl

example {G : Type u} [Group G]
  : commutatorSet G  = { h | ∃ a b : G, ⁅a, b⁆ = h} := rfl

example {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  : Subgroup.commutator.bracket H₁ H₂ = ⁅H₁, H₂⁆  := rfl

-- #check closure --topologacal.closure
#check Subgroup.closure
example {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  : Subgroup.closure { h | ∃ a ∈ H₁, ∃ b ∈ H₂ , ⁅a, b⁆ = h} = ⁅H₁, H₂⁆  := rfl

example {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  : Subgroup.closure { h | ∃ (a : H₁) (b : H₂) , ⁅(a : G), (b : G)⁆ = h} = ⁅H₁, H₂⁆ := by
    have : Subgroup.closure { h | ∃ a ∈ H₁, ∃ b ∈ H₂ , ⁅a, b⁆ = h} = ⁅H₁, H₂⁆ := rfl
    convert this
    constructor
    . rintro ⟨a, b, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
    . rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

#check conjugate_commutatorElement
#check MulAut.conj
#check MulEquiv

theorem my_map_commutatorElement
  {G G' F : Type*} [Group G] [Group G'] [FunLike F G G'] [MonoidHomClass F G G']
  (f : F) (g₁ g₂ : G)
  : f ⁅g₁, g₂⁆ = ⁅f g₁, f g₂⁆ := by
  simp_rw [commutatorElement_def, map_mul, map_inv]

theorem my_conjugate_commutatorElement
  {G : Type u} [Group G] (g₁ g₂ g₃ : G)
  : g₃ * ⁅g₁, g₂⁆ * g₃⁻¹ = ⁅g₃ * g₁ * g₃⁻¹, g₃ * g₂ * g₃⁻¹⁆ := by
  let f := MulAut.conj g₃
  show f ⁅g₁, g₂⁆ = ⁅f g₁, f g₂⁆
  apply my_map_commutatorElement

theorem my_conjugate_commutatorElement'
  {G : Type u} [Group G] (g₁ g₂ g₃ : G)
  : g₃ * ⁅g₁, g₂⁆ * g₃⁻¹ = ⁅g₃ * g₁ * g₃⁻¹, g₃ * g₂ * g₃⁻¹⁆ :=
  my_map_commutatorElement (MulAut.conj g₃) g₁ g₂

#check Subgroup.mem_closure
theorem my_commutator_mem_commutator
  {G : Type u} [Group G] {g₁ g₂ : G} {H₁ H₂ : Subgroup G}
  (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂)
  : ⁅g₁, g₂⁆ ∈ ⁅H₁, H₂⁆ := by
  apply Subgroup.mem_closure_of_mem
  exact ⟨_, h₁, _, h₂, rfl⟩

theorem my_commutator_mem_commutator'
  {G : Type u} [Group G] {g₁ g₂ : G} {H₁ H₂ : Subgroup G}
  (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂)
  : ⁅g₁, g₂⁆ ∈ ⁅H₁, H₂⁆ :=
    Subgroup.subset_closure ⟨g₁, h₁, g₂, h₂, rfl⟩

theorem my_commutator_mono
  {G : Type u} [Group G] {H₁ H₂ K₁ K₂ : Subgroup G}
  (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂)
  : ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ := by
  rw [Subgroup.commutator_def, Subgroup.commutator_def]
  apply Subgroup.closure_mono
  rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  exact ⟨g₁, h₁ hg₁, g₂, h₂ hg₂, rfl⟩

#check Subgroup.centralizer
#check Subgroup.le_centralizer_iff
#check Subgroup.mem_centralizer_iff
theorem my_commutator_eq_bot_iff_le_centralizer
  {G : Type u} [Group G] {H₁ H₂ : Subgroup G}
  : ⁅H₁, H₂⁆ = ⊥ ↔ H₁ ≤ Subgroup.centralizer ↑H₂ := by
  constructor
  . intro h
    intro g₁ hg₁
    rw [Subgroup.mem_centralizer_iff]
    intro g₂ hg₂
    symm
    rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h]
    exact Subgroup.commutator_mem_commutator hg₁ hg₂
  . intro h
    have : ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, g₂ * g₁ = g₁ * g₂ := h
    have : ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁, g₂⁆ = 1 := by
      refine fun g₁ hg₁ g₂ hg₂ ↦ commutatorElement_eq_one_iff_mul_comm.2 (this g₁ hg₁ g₂ hg₂).symm
    rw [Subgroup.commutator_def, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    exact this g₁ hg₁ g₂ hg₂

theorem my_commutator_eq_bot_iff_le_centralizer'
  {G : Type u} [Group G] {H₁ H₂ : Subgroup G}
  : ⁅H₁, H₂⁆ = ⊥ ↔ H₁ ≤ Subgroup.centralizer ↑H₂ := by
  calc ⁅H₁, H₂⁆ = ⊥
    _ ↔ ⁅H₁, H₂⁆ ≤ ⊥ := eq_bot_iff
    _ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁, g₂⁆ ∈ ⊥ := Subgroup.commutator_le
    _ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁, g₂⁆ = 1 := by simp_rw [Subgroup.mem_bot]
    _ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, g₁ * g₂ = g₂ * g₁ := by simp_rw [commutatorElement_eq_one_iff_mul_comm]
    _ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, g₂ * g₁ = g₁ * g₂ := by simp_rw [eq_comm]
    _ ↔ H₁ ≤ Subgroup.centralizer H₂ := Iff.rfl

theorem my_commutator_commutator_eq_bot_of_rotate
  {G : Type u} [Group G] {H₁ H₂ H₃ : Subgroup G}
  (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥)
  : ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by
  simp_rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.commutator_le,
    Subgroup.mem_centralizer_iff_commutator_eq_one,
     ← commutatorElement_def] at h1 h2 ⊢
  intro x hx y hy z hz
  trans x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹
  . simp [commutatorElement_def, mul_assoc]
  . rw [h2, h1]
    simp
    all_goals simpa

theorem my_commutator_comm_le
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  : ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [← Subgroup.inv_mem_iff, commutatorElement_inv]
  apply Subgroup.commutator_mem_commutator
  assumption'

theorem my_commutator_comm
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ := by
  apply le_antisymm <;> apply Subgroup.commutator_comm_le

def my_commutator_normal
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  [h₁ : H₁.Normal] [h₂ : H₂.Normal]
  : ⁅H₁, H₂⁆.Normal := by
  let base : Set G := { x | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = x }
  change (Subgroup.closure base).Normal
  let A' : Set G := { n | ∀ g, MulAut.conj g n ∈ ⁅H₁, H₂⁆ }
  let A : Subgroup G := {
    carrier := A'
    mul_mem' := by
      intro a b ha hb g
      rw [map_mul]
      exact ⁅H₁, H₂⁆.mul_mem (ha g) (hb g)
    one_mem' := by
      intro g
      rw [map_one]
      exact ⁅H₁, H₂⁆.one_mem
    inv_mem' := by
      intro a ha g
      rw [map_inv]
      exact ⁅H₁, H₂⁆.inv_mem (ha g)
  }
  suffices base ⊆ A' by
    have : base ⊆ A := this
    rw [← Subgroup.closure_le] at this
    exact ⟨this⟩

  rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩ g
  rw [map_commutatorElement]
  apply Subgroup.commutator_mem_commutator
  . exact h₁.conj_mem g₁ hg₁ g
  . exact h₂.conj_mem g₂ hg₂ g

def my_commutator_normal'
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  [h₁ : H₁.Normal] [h₂ : H₂.Normal]
  : ⁅H₁, H₂⁆.Normal := by
  let base : Set G := { x | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = x }
  change (Subgroup.closure base).Normal
  let A : Subgroup G := ⨅ g, ⁅H₁, H₂⁆.comap (MulAut.conj g).toMonoidHom
  have hA {n} : n ∈ A ↔ (∀ g, (MulAut.conj g) n ∈ ⁅H₁, H₂⁆) := by
     simp_rw [A, Subgroup.mem_iInf, Subgroup.mem_comap]
     rfl
  suffices base ⊆ A by
    rw [← Subgroup.closure_le] at this
    refine ⟨fun n hn ↦ hA.1 (this hn)⟩
  rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  show ⁅g₁, g₂⁆ ∈ A
  rw [hA]
  intro g
  rw [map_commutatorElement]
  apply Subgroup.commutator_mem_commutator
  . exact h₁.conj_mem g₁ hg₁ g
  . exact h₂.conj_mem g₂ hg₂ g

#check Subgroup.normalClosure_closure_eq_normalClosure
#check Subgroup.normalClosure_eq_self
theorem my_commutator_def'
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G) [H₁.Normal] [H₂.Normal] :
  ⁅H₁, H₂⁆ = Subgroup.normalClosure {g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := by
  rw [← Subgroup.normalClosure_eq_self ⁅H₁, H₂⁆]
  exact Subgroup.normalClosure_closure_eq_normalClosure

theorem my_commutator_le_right
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G) [h : H₂.Normal] : ⁅H₁, H₂⁆ ≤ H₂ := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  refine H₂.mul_mem (h.conj_mem _ ?_ _) (H₂.inv_mem ?_)
  assumption'

theorem my_commutator_le_left
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G) [H₁.Normal] : ⁅H₁, H₂⁆ ≤ H₁ := by
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le_right

theorem my_commutator_bot_left
  {G : Type u} [Group G] (H₁ : Subgroup G)
  : ⁅(⊥ : Subgroup G), H₁⁆ = ⊥ := by
  rw [eq_bot_iff]
  apply Subgroup.commutator_le_left

theorem my_commutator_le_inf
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G) [H₁.Normal] [H₂.Normal] :
  ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
    le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)

theorem my_map_commutator
  {G G' : Type*} [Group G] [Group G']
  (H₁ H₂ : Subgroup G) (f : G →* G')
  : ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ := by
  rw [Subgroup.commutator_def, f.map_closure, Subgroup.commutator_def]
  congr
  ext
  constructor
  . rintro ⟨_, ⟨g₁,h₁,g₂,h₂,rfl⟩, rfl⟩
    refine ⟨f g₁, ⟨g₁, h₁ , rfl⟩, f g₂, ⟨g₂, h₂, rfl⟩, ?_⟩
    rw [map_commutatorElement]
  . rintro ⟨_, ⟨g₁, h₁, rfl⟩, _, ⟨g₂, h₂, rfl⟩, rfl⟩
    refine ⟨⁅g₁, g₂⁆, ⟨g₁,h₁,g₂,h₂,rfl⟩, ?_⟩
    rw [map_commutatorElement]

theorem my_map_commutator'
  {G G' : Type*} [Group G] [Group G']
  (H₁ H₂ : Subgroup G) (f : G →* G')
  : ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ := by
  rw [Subgroup.commutator_def, f.map_closure, Subgroup.commutator_def]
  congr
  ext
  simp
  simp_rw [map_commutatorElement]

theorem my_map_commutator''
  {G G' : Type*} [Group G] [Group G']
  (H₁ H₂ : Subgroup G) (f : G →* G')
  : ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ := by
  simp_rw [le_antisymm_iff, Subgroup.map_le_iff_le_comap, Subgroup.commutator_le, Subgroup.mem_comap]
  constructor
  . intro g₁ h₁ g₂ h₂
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator ⟨g₁, h₁, rfl⟩ ⟨g₂,h₂, rfl⟩
  . rintro _ ⟨g₁,h₁,rfl⟩ _ ⟨g₂,h₂,rfl⟩
    rw [← map_commutatorElement]
    exact ⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator h₁ h₂, rfl⟩

theorem my_commutator_le_map_commutator
  {G : Type u} {G' : Type u} [Group G] [Group G']
  {H₁ H₂ : Subgroup G} {f : G →* G'} {K₁ K₂ : Subgroup G'}
  (h₁ : K₁ ≤ Subgroup.map f H₁) (h₂ : K₂ ≤ Subgroup.map f H₂)
  : ⁅K₁, K₂⁆ ≤ Subgroup.map f ⁅H₁, H₂⁆ :=
    Subgroup.map_commutator H₁ H₂ f ▸ Subgroup.commutator_mono h₁ h₂

#check Subgroup.Characteristic
#check Subgroup.characteristic_iff_le_map
theorem my_commutator_characteristic
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  [h₁ : H₁.Characteristic] [h₂ : H₂.Characteristic]
  : ⁅H₁, H₂⁆.Characteristic := by
  rw [Subgroup.characteristic_iff_le_map] at h₁ h₂ ⊢
  intro f
  exact Subgroup.commutator_le_map_commutator (h₁ f) (h₂ f)

#check Subgroup.map_map
#check Subgroup.map_id
#check Subgroup.ext
#check MonoidHom.fst_comp_prod
#check MonoidHom.fst_comp_inl
theorem my_commutator_prod_prod
  {G : Type u_1} {G' : Type u_2} [Group G] [Group G']
  (H₁ H₂ : Subgroup G) (K₁ K₂ : Subgroup G')
  : ⁅H₁.prod K₁, H₂.prod K₂⁆ = ⁅H₁, H₂⁆.prod ⁅K₁, K₂⁆ := by
  apply le_antisymm
  . rw [Subgroup.commutator_le]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    constructor; all_goals apply Subgroup.commutator_mem_commutator
    assumption'
  . simp_rw [Subgroup.prod_le_iff, Subgroup.map_commutator]
    constructor; all_goals apply Subgroup.commutator_mono
    all_goals simp [Subgroup.le_prod_iff, Subgroup.map_map,
      MonoidHom.fst_comp_inr, MonoidHom.fst_comp_inl]

#check Subgroup.closure_prod
theorem my_commutator_prod_prod'
  {G : Type u_1} {G' : Type u_2} [Group G] [Group G']
  (H₁ H₂ : Subgroup G) (K₁ K₂ : Subgroup G')
  : ⁅H₁.prod K₁, H₂.prod K₂⁆ = ⁅H₁, H₂⁆.prod ⁅K₁, K₂⁆ := by
  apply le_antisymm
  . rw [Subgroup.commutator_le]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩
    constructor
    all_goals apply Subgroup.commutator_mem_commutator
    assumption'
  . simp_rw [Subgroup.prod_le_iff, Subgroup.map_commutator]
    constructor
    all_goals apply Subgroup.commutator_mono
    all_goals simp [Subgroup.le_prod_iff, Subgroup.map_map,
      MonoidHom.fst_comp_inr, MonoidHom.fst_comp_inl]

#check Subgroup.commutator_pi_pi_le

theorem my_commutator_pi_pi_le
  {η : Type u_4} {Gs : η → Type u_5}
  [(i : η) → Group (Gs i)]
  (H K : (i : η) → Subgroup (Gs i))
  : ⁅Subgroup.pi Set.univ H, Subgroup.pi Set.univ K⁆ ≤ Subgroup.pi Set.univ fun i ↦ ⁅H i, K i⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂ i hi
  -- dsimp
  apply Subgroup.commutator_mem_commutator (h₁ i hi) (h₂ i hi)


#check Subgroup.pi_le_iff
#check Subgroup.le_pi_iff
#check Subgroup.pi
/-
DirectSum
-/
#check DirectSum
#check DirectSum.IsInternal
-- example

#check Finsupp
set_option trace.Meta.synthInstance true
example {ι : Type u} {G : ι → Type v} [∀ i, Group (G i)] : Group ((i : ι) → G i) := inferInstance
#check Pi.group
example {ι : Type u} {G : Type v} [Group G] : Group (ι → G) := inferInstance
#check Pi.group
example {ι : Type u} {G : ι → Type v} [∀ i, AddGroup (G i)] : AddGroup (Π₀ (i : ι), G i) := inferInstance
#check DFinsupp.instAddGroup
noncomputable example {ι : Type u} {G : Type v} [AddGroup G] : AddGroup (ι →₀ G) := inferInstance
#check DFinsupp.instAddGroup
#check Finsupp

-- example {ι : Type u} {G : ι → Type v} [∀ i, AddGroup (G i)] : AddGroup ((i : ι) →₀ G i) := inferInstance

set_option trace.Meta.synthInstance false



-- theorem commutator_eq_bot_iff_center_eq_top : commutator G = ⊥ ↔ Subgroup.center G = ⊤ := by
--   simp [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]

/-
[⊤, ⊤] = ⊥
⊤ ≤ Centra ⊤ = Center
T = Center
-/

/-
  ⁅centralizer ↑(commutator G), centralizer ↑(commutator G)⁆ ≤ center G

[Centra [T, T], Centra [T, T]] ≤ Center G
[Centra [T, T], Centra [T, T]] ≤ Centra ⊤
[[Centra [T, T], Centra [T, T]], ⊤] = ⊥

-/


#check Std.Commutative.mk
#check QuotientGroup.eq_one_iff
#check QuotientGroup.mk_mul
#check QuotientGroup.mk'
#check QuotientGroup.mk'_apply

#check Subgroup.Normal.quotient_commutative_iff_commutator_le
theorem my_quotient_commutative_iff_commutator_le
  {G : Type u_1} [Group G] {N : Subgroup G} [N.Normal] :
  Std.Commutative (· * · : G ⧸ N → _ → _) ↔ commutator G ≤ N := by
  constructor
  . intro h
    rw [commutator_def, Subgroup.commutator_le]
    rintro g₁ - g₂ -
    rw [commutatorElement_def]
    simp_rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h.comm (g₁ * g₂), inv_mul_cancel_left, mul_inv_cancel]
  . intro h
    apply Std.Commutative.mk
    rintro ⟨x⟩ ⟨y⟩
    have : ⁅x, y⁆ ∈ N := by
      apply h
      apply Subgroup.commutator_mem_commutator <;> trivial
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff] at this
    simp_rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at this
    exact this


theorem my_commutator_le_right'
  {G : Type u} [Group G] (H₁ H₂ : Subgroup G)
  [h : H₂.Normal]
  : ⁅H₁, H₂⁆ ≤ H₂ := by
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro g ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  rw [commutatorElement_def]
  have hmem1 : g₁ * g₂ * g₁⁻¹ ∈ H₂ := h.conj_mem g₂ hg₂ g₁
  have hmem2 : g₂⁻¹ ∈ H₂ := H₂.inv_mem hg₂
  exact H₂.mul_mem hmem1 hmem2
