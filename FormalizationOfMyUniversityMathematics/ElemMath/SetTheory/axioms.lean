import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
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
export AxiomOfEmptyset (not_mem_empty)

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
theorem specification_is_redundant_in_ZFC {set : Type u} [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] :
  ∀ P : set → Prop, ∀ U : set, ∃ S : set, ∀ x, x ∈ S ↔ x ∈ U ∧ P x := by
  intro P U
  by_cases h : ∀ x ∈ U, ¬ P x
  . use ∅
    intro x
    constructor
    . intro h
      exfalso
      exact not_mem_empty x h
    . intro ⟨hxU, hPx⟩
      exfalso
      exact h x hxU hPx
  . push_neg at h
    choose l hlU hPl using h
    let Q x y := P x ∧ y = x ∨ ¬ P x ∧ y = l
    have hQ : ∀ x, ∃! y, Q x y := by
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
    use replacement Q U
    intro y
    rw [mem_replacement_iff Q U hQ]
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


noncomputable instance {set : Type u} [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] : AxiomOfSpecification set where
  specification P U := Classical.choose (specification_is_redundant_in_ZFC P U)
  mem_specification_iff P U := Classical.choose_spec (specification_is_redundant_in_ZFC P U)

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

class AxiomOfsUnion (set : Type u) [SetTheory set] where
  sUnion : set → set
  mem_sUnion_iff (S : set) : ∀ x, x ∈ sUnion S ↔ ∃ A ∈ S, x ∈ A

prefix:110 "⋃₀ " => AxiomOfsUnion.sUnion

class HasInter (set : Type u) where
  inter : set → set → set

instance (set : Type u) [HasInter set] : Inter set where inter := HasInter.inter

class AxiomOfInter (set : Type u) [SetTheory set] extends HasInter set  where
  mem_inter_iff (S T : set) : ∀ x, x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T

export AxiomOfInter (mem_inter_iff)

class AxiomOfsInter (set : Type u) [SetTheory set] where
  sInter : set → set
  mem_sInter_iff (S : set) : ∀ x, x ∈ sInter S ↔ ∀ A ∈ S, x ∈ A

prefix:110 "∩₀ " => AxiomOfsInter.sInter

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

instance (set : Type u) [SetTheory set]
  [AxiomOfReplacement set] [AxiomOfEmptyset set] [AxiomOfPowerset set] : AxiomOfSingleton set where
  singleton a := replacement (fun x y ↦ y = a) (𝒫 ∅)
  mem_singleton_iff a := by
    intro y
    change _ ∈ replacement (fun x y ↦ y = a) (𝒫 ∅) ↔ _
    simp [mem_replacement_iff, mem_powerset_iff]
    exact fun _ ↦ ⟨∅, AxiomOfEmptyset.empty_subset _⟩

instance (set : Type u) [SetTheory set]
  [AxiomOfSingleton set] [AxiomOfUnion set] [AxiomOfExtensionality set] : AxiomOfOrderedPair set where
  ordered_pair a b := {{a}} ∪ {{a} ∪ {b}}
  ordered_pair_inj a b a' b' := by
    constructor
    case mpr => rintro ⟨rfl, rfl⟩; rfl
    intro h
    by_cases heq : a = b
    . sorry
    . sorry

instance (set : Type u) [SetTheory set]
  [AxiomOfOrderedPair set] [AxiomOfUnion set] [AxiomOfPowerset set] [AxiomOfSpecification set] : AxiomOfProduct set where
  product A B := specification (fun x ↦ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ) (𝒫 (𝒫 (A ∪ B)))
  mem_product_iff A B := by sorry

class ZFC (set : Type u) [SetTheory set] extends
  AxiomOfExtensionality set,
  AxiomOfEmptyset set,
  AxiomOfReplacement set,
  AxiomOfPowerset set,
  AxiomOfUnion set,
  AxiomOfRegularity set,
  AxiomOfInfinity set,
  AxiomOfChoice set
