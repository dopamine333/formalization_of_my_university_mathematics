import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SimpRw
import Mathlib.Data.SProd

class SetTheory (set : Type u) where
  mem : set → set → Prop

namespace SetTheory

variable {set : Type u} [SetTheory set]

-- notation: ∈
instance : Membership set set where
  mem x S := SetTheory.mem x S

def subset (S T : set) : Prop := ∀ x ∈ S, x ∈ T

-- notation: ⊆, ⊇ (do not have ⊂, ⊃)
instance : HasSubset set where
  Subset S T := SetTheory.subset S T

example (x S T : set) (hxS : x ∈ S) (hST : S ⊆ T) : x ∈ T := hST x hxS

end SetTheory

class AxiomOfExtensionality (set : Type u) [SetTheory set] where
  extensionality : ∀ a b : set, a = b ↔ ∀ x, x ∈ a ↔ x ∈ b

-- let you can write `extensionality` instead of `AxiomOfExtensionality.extensionality`
export AxiomOfExtensionality (extensionality)

namespace AxiomOfExtensionality

variable {set : Type u} [SetTheory set]

theorem subset_refl (S : set) : S ⊆ S := fun _ hxS ↦ hxS

theorem subset_trans (A B C : set) : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAB hBC x hxA
  exact hBC x (hAB x hxA)

theorem subset_antisymm [AxiomOfExtensionality set] (A B : set) : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  rw [extensionality]
  intro x
  constructor
  . intro hxA
    exact hAB x hxA
  . intro hxB
    exact hBA x hxB

end AxiomOfExtensionality

class HasEmptyset (set : Type u) where
  empty : set

instance (set : Type u) [HasEmptyset set] : EmptyCollection set
  where emptyCollection := HasEmptyset.empty

class AxiomOfEmptyset (set : Type u) [SetTheory set] extends HasEmptyset set where
  not_mem_empty : ∀ x, x ∉ (∅ : set)

namespace AxiomOfEmptyset

variable {set : Type u} [SetTheory set] [AxiomOfEmptyset set]

theorem mem_empty_iff (x : set) : x ∈ (∅ : set) ↔ False := ⟨fun h ↦ not_mem_empty x h, False.elim⟩

theorem empty_subset (S : set) : ∅ ⊆ S := by
  intro x hxempty
  have := not_mem_empty x
  contradiction

theorem empty_unique [AxiomOfExtensionality set] :
  ∃! S : set, ∀ x, x ∉ S := by
  refine ⟨∅, ?_, ?_⟩
  . exact not_mem_empty
  . intro y hy
    rw [extensionality]
    intro x
    constructor
    . intro h
      exfalso
      exact hy x h
    . intro h
      exfalso
      exact not_mem_empty x h

end AxiomOfEmptyset

-- let you can write `not_mem_empty` instead of `AxiomOfEmptyset.not_mem_empty`
export AxiomOfEmptyset (not_mem_empty mem_empty_iff)

class AxiomOfReplacement (set : Type u) [SetTheory set] where
  replacement : (set → set → Prop) → set → set
  mem_replacement_iff (P : set → set → Prop) (U : set) :
    (∀ x, ∃! y, P x y) → (∀ y, y ∈ replacement P U ↔ ∃ x, x ∈ U ∧ P x y)

export AxiomOfReplacement (replacement mem_replacement_iff)

class AxiomOfSpecification (set : Type u) [SetTheory set] where
  specification : (set → Prop) → set → set
  mem_specification_iff (P : set → Prop) (U : set) :
    ∀ x, x ∈ specification P U ↔ x ∈ U ∧ P x

export AxiomOfSpecification (specification mem_specification_iff)

-- Proposition 15.1.1
noncomputable instance {set : Type u} [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] : AxiomOfSpecification set where
  specification P U :=
    haveI := Classical.propDecidable
    if h : ∃ x ∈ U, P x then
      let l := Classical.choose h
      let Q x y := P x ∧ y = x ∨ ¬ P x ∧ y = l
      replacement Q U
    else
      ∅
  mem_specification_iff P U y := by
    by_cases h : ∃ x ∈ U, P x
    case neg =>
      simp [h]
      constructor
      . intro h
        exfalso
        exact not_mem_empty _ h
      . intro ⟨hyU, hPy⟩
        exfalso
        exact h ⟨y, hyU, hPy⟩
    let l := Classical.choose h
    have ⟨(hlU : l ∈ U), (hPl : P l)⟩ := Classical.choose_spec h
    let Q x y := P x ∧ y = x ∨ ¬ P x ∧ y = l
    simp [h]
    change _ ∈ replacement Q U ↔ _
    rw [mem_replacement_iff Q U]
    constructor
    . rintro ⟨x, hxU, hQxy⟩
      apply hQxy.elim
      . rintro ⟨hPx, rfl⟩
        exact ⟨hxU, hPx⟩
      . rintro ⟨_, rfl⟩
        exact ⟨hlU, hPl⟩
    . rintro ⟨hyU, hPy⟩
      use y, hyU
      left
      exact ⟨hPy, rfl⟩
    intro x
    by_cases h : P x
    . use x
      dsimp
      constructor
      . unfold Q
        left
        exact ⟨h, rfl⟩
      . intro y hy
        apply hy.elim
        . exact fun h' ↦ h'.2
        . exact fun h' ↦ (h'.1 h).elim
    . use l
      dsimp
      constructor
      . unfold Q
        right
        exact ⟨h, rfl⟩
      . intro y hy
        apply hy.elim
        . exact fun h' ↦ (h h'.1).elim
        . exact fun h' ↦ h'.2

class AxiomOfPowerset (set : Type u) [SetTheory set] where
  powerset : set → set
  mem_powerset_iff (S : set) : ∀ T, T ∈ powerset S ↔ T ⊆ S

prefix:100 "𝒫 " => AxiomOfPowerset.powerset

export AxiomOfPowerset (powerset mem_powerset_iff)

class HasUnion (set : Type u) where
  union : set → set → set

instance (set : Type u) [HasUnion set] : Union set where union := HasUnion.union

class AxiomOfUnion (set : Type u) [SetTheory set] extends HasUnion set where
  mem_union_iff (S T : set) : ∀ x, x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T

export AxiomOfUnion (mem_union_iff)

class HassUnion (set : Type u) where
  sUnion : set → set

prefix:110 "⋃₀ " => HassUnion.sUnion

class AxiomOfsUnion (set : Type u) [SetTheory set] extends HassUnion set where
  mem_sUnion_iff (S : set) : ∀ x, x ∈ ⋃₀ S ↔ ∃ A ∈ S, x ∈ A

export AxiomOfsUnion (mem_sUnion_iff)

class HasInter (set : Type u) where
  inter : set → set → set

instance (set : Type u) [HasInter set] : Inter set where inter := HasInter.inter

class AxiomOfInter (set : Type u) [SetTheory set] extends HasInter set  where
  mem_inter_iff (S T : set) : ∀ x, x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T

export AxiomOfInter (mem_inter_iff)

class HassInter (set : Type u) where
  sInter : set → set

prefix:110 "⋂₀ " => HassInter.sInter

class AxiomOfsInter (set : Type u) [SetTheory set] extends HassInter set where
  mem_sInter_iff (S : set) : ∀ x, x ∈ ⋂₀ S ↔ ∀ A ∈ S, x ∈ A

export AxiomOfsInter (mem_sInter_iff)

class HasSingleton (set : Type u) where
  singleton : set → set

instance (set : Type u) [HasSingleton set] : Singleton set set where singleton := HasSingleton.singleton

class AxiomOfSingleton (set : Type u) [SetTheory set] extends HasSingleton set where
  mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x

export AxiomOfSingleton (mem_singleton_iff)

class AxiomOfInfinity (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfUnion set] [AxiomOfSingleton set] where
  infinity : set
  empty_mem_infinity : ∅ ∈ infinity
  succ_mem_infinity : ∀ x ∈ infinity, x ∪ {x} ∈ infinity

class AxiomOfRegularity (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfInter set] where
  regularity : ∀ S ≠ (∅ : set), ∃ A ∈ S, A ∩ S = ∅

-- Definition 8.1.1
class HasOrderPair (set : Type u) where
  ordered_pair : set → set → set

notation :150 "(" a:150 ", " b:150 ")ˢ" => HasOrderPair.ordered_pair a b

class AxiomOfOrderedPair (set : Type u) [SetTheory set] extends HasOrderPair set where
  ordered_pair_inj (a b x y : set) : (a, b)ˢ = (x, y)ˢ ↔ a = x ∧ b = y

export AxiomOfOrderedPair (ordered_pair_inj)

class HasProduct (set : Type u) where
  product : set → set → set

instance (set : Type u) [HasProduct set] : SProd set set set where sprod := HasProduct.product

-- Definition 8.1.2
class AxiomOfProduct (set : Type u) [SetTheory set] [AxiomOfOrderedPair set] extends HasProduct set where
  mem_product_iff (A B : set) : ∀ x, x ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ

export AxiomOfProduct (mem_product_iff)

section Function

variable {set : Type u} [SetTheory set] [AxiomOfOrderedPair set] [AxiomOfProduct set]

def is_function (A B f : set) : Prop := f ⊆ A ×ˢ B ∧ ∀ a ∈ A, ∃! b ∈ B, (a, b)ˢ ∈ f

noncomputable def toFun
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A) : set :=
  Classical.choose (hf.2 a ha)

theorem toFun_spec
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A) :
  toFun hf ha ∈ B ∧ (a, toFun hf ha)ˢ ∈ f := by
  rw [toFun]
  exact (Classical.choose_spec (hf.2 a ha)).1

theorem toFun_unique
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A)
  {b : set} (hb : b ∈ B) (habf : (a, b)ˢ ∈ f) : b = toFun hf ha := by
  rw [toFun]
  have := (Classical.choose_spec (hf.2 a ha)).2
  exact this b ⟨hb, habf⟩

theorem toFun_ext [AxiomOfExtensionality set]
  {A B f g : set} (hf : is_function A B f) (hg : is_function A B g)
  : f = g ↔ ∀ a, (ha : a ∈ A) → toFun hf ha = toFun hg ha := by
  constructor
  . intro heq a ha
    have h1 := toFun_spec hf ha
    have h2 := toFun_spec hg ha
    nth_rw 2 [heq] at h1
    exact (hg.2 a ha).unique h1 h2
  . intro h
    rw [extensionality]
    intro x
    constructor
    . intro hxf
      have := hf.1 x hxf
      rw [mem_product_iff] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := this
      have := toFun_unique hf ha hb hxf
      rw [this, h]
      exact (toFun_spec hg ha).2
    . intro hxg
      have := hg.1 x hxg
      rw [mem_product_iff] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := this
      have := toFun_unique hg ha hb hxg
      rw [this, ← h]
      exact (toFun_spec hf ha).2

-- more over, assume axiom of specification, axiom_of_powerset holds
variable [AxiomOfSpecification set] [AxiomOfPowerset set]

def function (A B : set) : set := specification (is_function A B) (𝒫 (A ×ˢ B))

theorem mem_function_iff (A B f : set) : f ∈ function A B ↔ is_function A B f := by
  constructor
  . intro h
    rw [function, mem_specification_iff] at h
    exact h.2
  . intro h
    have : f ⊆ A ×ˢ B := by
      rw [is_function] at h
      exact h.1
    rw [function, mem_specification_iff, mem_powerset_iff]
    exact ⟨this, h⟩

end Function

class AxiomOfChoice (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfOrderedPair set] [AxiomOfProduct set] [AxiomOfPowerset set] where
  choice (S : set) : set -- S ↦ (f : 𝒫 S → S)
  choice_is_function (S : set) (hS : S ≠ ∅) : is_function (𝒫 S) S (choice S)
  choice_mem (S : set) (hS : S ≠ ∅) : ∀ T, (hT : T ∈ 𝒫 S) → T ≠ ∅ → toFun (choice_is_function S hS) hT ∈ T


instance (set : Type u) [SetTheory set] [AxiomOfSpecification set] : AxiomOfInter set where
  inter S T := specification (. ∈ T) S
  mem_inter_iff S T := by
    intro x
    change _ ∈ specification (. ∈ T) S ↔ _
    rw [mem_specification_iff]

class AxiomOfPairing (set : Type u) [SetTheory set] where
  pair : set → set → set
  mem_pair_iff S T : ∀ x, x ∈ pair S T ↔ x = S ∨ x = T

export AxiomOfPairing (pair mem_pair_iff)

class AxiomOfInsert (set : Type u) [SetTheory set] where
  insert : set → set → set
  mem_insert_iff' x S : ∀ y, y ∈ insert x S ↔ y = x ∨ y ∈ S -- insert x S = {x} ∪ S

-- export AxiomOfInsert (mem_insert_iff)

instance (set : Type u) [SetTheory set] [AxiomOfInsert set] : Insert set set := ⟨AxiomOfInsert.insert⟩

theorem mem_insert_iff (set : Type u) [SetTheory set] [AxiomOfInsert set] (x S : set) :
  ∀ y, y ∈ insert x S ↔ y = x ∨ y ∈ S := AxiomOfInsert.mem_insert_iff' x S

instance (set : Type u) [SetTheory set] [AxiomOfExtensionality set]
  [AxiomOfEmptyset set] [AxiomOfInsert set]  [AxiomOfSingleton set] : LawfulSingleton set set where
  insert_empty_eq x := by
    -- simp [extensionality, mem_insert_iff, mem_singleton_iff, not_mem_empty]
    rw [extensionality]
    intro h
    rw [mem_insert_iff, mem_empty_iff, mem_singleton_iff, or_false]

example (set : Type u) [SetTheory set] [AxiomOfExtensionality set]
  [AxiomOfEmptyset set] [AxiomOfInsert set] [AxiomOfSingleton set]
  (a b c : set) : ∀ x, x ∈ ({a,b,c} : set) ↔ x = a ∨ x = b ∨ x = c := by
  intro x
  rw [mem_insert_iff, mem_insert_iff, mem_singleton_iff]

instance (set : Type u) [SetTheory set] [AxiomOfExtensionality set]
  [AxiomOfEmptyset set] [AxiomOfInsert set] [AxiomOfSingleton set] : AxiomOfOrderedPair set where
  ordered_pair a b := {{a}, {a, b}}
  ordered_pair_inj a b a' b' := by
    constructor
    case mpr => rintro ⟨rfl, rfl⟩; rfl
    intro h
    have key (x y z : set) : ({x} : set) = {y, z} ↔ x = y ∧ x = z ∧ y = z:= by
      constructor
      . intro h
        have hy : y ∈ ({x} : set) := by simp [h, mem_insert_iff]
        have hz : z ∈ ({x} : set) := by simp [h, mem_insert_iff, mem_singleton_iff]
        simp [ mem_singleton_iff] at hy hz
        exact ⟨hy.symm, hz.symm, hy.trans hz.symm⟩
      . rintro ⟨rfl, rfl, _⟩
        simp [extensionality, mem_insert_iff, mem_singleton_iff]
    by_cases heq : a = b
    . rw [heq, ← (key b b b).mpr (by simp), ← (key {b} {b} {b}).mpr (by simp), key, key] at h
      obtain ⟨_, ⟨hba', hbb', ha'b'⟩, _⟩ := h
      exact ⟨heq.trans hba', hbb'⟩
    by_cases heq' : a' = b'
    . rw [Eq.comm, heq', ← (key b' b' b').mpr (by simp), ← (key {b'} {b'} {b'}).mpr (by simp), key, key] at h
      obtain ⟨_, ⟨hb'a, hb'b, hab⟩, _⟩ := h
      exact ⟨hb'a.symm.trans heq'.symm, hb'b.symm⟩
    have hab : {a, b} ∈ ({{a'}, {a', b'}} : set) := by simp [← h, mem_insert_iff, mem_singleton_iff]
    rw [mem_insert_iff, mem_singleton_iff, Eq.comm,
        key, or_iff_right (fun h' ↦ heq h'.2.2)] at hab
    have ha : {a} ∈ ({{a'}, {a', b'}} : set) := by simp [← h, mem_insert_iff, mem_singleton_iff]
    rw [mem_insert_iff, mem_singleton_iff, Eq.comm,
        key, or_iff_left (fun h' ↦ heq' h'.2.2)] at ha
    have ha : a ∈ ({a'} : set):= by simp [ha, mem_singleton_iff]
    rw [mem_singleton_iff] at ha
    have hb : b ∈ ({a, b'} : set) := by simp [ha, ← hab, mem_insert_iff, mem_singleton_iff]
    rw [mem_insert_iff, mem_singleton_iff, or_iff_right (fun h' ↦ heq h'.symm)] at hb
    exact ⟨ha, hb⟩

instance (set : Type u) [SetTheory set] [AxiomOfExtensionality set]
  [AxiomOfEmptyset set] [AxiomOfInsert set]  [AxiomOfSingleton set]
  [AxiomOfUnion set] [AxiomOfPowerset set] [AxiomOfSpecification set] : AxiomOfProduct set where
  product A B := specification (fun x ↦ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ) (𝒫 (𝒫 (A ∪ B)))
  mem_product_iff A B x := by
    change x ∈ specification _ _ ↔ _
    simp [mem_specification_iff]
    intro a ha b hb h
    rw [mem_powerset_iff]
    change x = {{a}, {a, b}} at h
    rw [h]
    intro x hx
    rw [mem_insert_iff, mem_singleton_iff] at hx
    apply hx.elim
    . rintro rfl
      simp [mem_powerset_iff]
      intro x hx
      simp [mem_singleton_iff, mem_union_iff] at hx ⊢
      left
      rw [hx]
      exact ha
    . rintro rfl
      simp [mem_powerset_iff]
      intro x hx
      simp [mem_singleton_iff, mem_insert_iff, mem_union_iff] at hx ⊢
      obtain rfl | rfl := hx
      . left; exact ha
      . right; exact hb

instance (set : Type u) [SetTheory set]
  [AxiomOfExtensionality set] [AxiomOfReplacement set] [AxiomOfEmptyset set] [AxiomOfPowerset set]: AxiomOfPairing set where
  pair a b := replacement (fun x y ↦ x = ∅ ∧ y = a ∨ x ≠ ∅ ∧ y = b) (𝒫 𝒫 ∅)
  mem_pair_iff a b y := by
    rw [mem_replacement_iff]
    . constructor
      . rintro ⟨x, _, (⟨_, ha⟩ | ⟨_, hb⟩)⟩
        . exact Or.inl ha
        . exact Or.inr hb
      . rintro (rfl | rfl)
        . refine ⟨∅, ?_, ?_⟩
          . rw [mem_powerset_iff]
            exact AxiomOfEmptyset.empty_subset _
          . left
            exact ⟨rfl, rfl⟩
        . refine ⟨𝒫 ∅, ?_, ?_⟩
          . rw [mem_powerset_iff]
            exact AxiomOfExtensionality.subset_refl _
          . right
            refine ⟨fun h ↦ ?_, rfl⟩
            have : ∅ ∈ (∅ : set) := by
              nth_rw 1 [← h, mem_powerset_iff]
              exact AxiomOfEmptyset.empty_subset _
            exact not_mem_empty _ this
    . intro x
      by_cases h : x = ∅
      . refine ⟨a, ?_, ?_⟩
        . simp [h]
        intro y h'
        rw [or_iff_left fun h' ↦ h'.1 h] at h'
        exact h'.2
      . refine ⟨b, ?_, ?_⟩
        . simp [h]
        intro y h'
        rw [or_iff_right fun h' ↦ h h'.1] at h'
        exact h'.2

instance (set : Type u) [SetTheory set]
  [AxiomOfPairing set] [AxiomOfsUnion set] : AxiomOfUnion set where
  union a b := ⋃₀ (pair a b)
  mem_union_iff a b x:= by
    change x ∈ ⋃₀ (pair a b) ↔ _
    simp [mem_sUnion_iff, mem_pair_iff]

instance (set : Type u) [SetTheory set]
  [AxiomOfPairing set] : AxiomOfSingleton set where
  singleton a := pair a a
  mem_singleton_iff a x := by
    change _ ∈ pair a a ↔ _
    simp [mem_pair_iff]

instance (set : Type u) [SetTheory set]
  [AxiomOfSingleton set] [AxiomOfUnion set] : AxiomOfInsert set where
  insert x S := {x} ∪ S
  mem_insert_iff' x S y := by
    simp [mem_union_iff, mem_singleton_iff]

class ZFC (set : Type u) [SetTheory set] extends
  AxiomOfExtensionality set,
  AxiomOfEmptyset set,
  AxiomOfReplacement set,
  AxiomOfPowerset set,
  AxiomOfsUnion set,
  AxiomOfRegularity set,
  AxiomOfInfinity set,
  AxiomOfChoice set
