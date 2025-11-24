class SetNotation (set : Type u) where
  mem : set → set → Prop
  emptyset : set
  powerset : set → set
  union : set → set → set
  sUnion : set → set
  inter : set → set → set
  sInter : set → set
  singleton : set → set
  sprod : set → set → set
  pair : set → set → set
notation:50 x:50 " ∈' " S:50 => SetNotation.mem x S
binder_predicate x " ∈' " y:term => `($x ∈' $y)
notation:110 " 𝓟' " S:110 => SetNotation.powerset S
notation " ∅' " => SetNotation.emptyset
notation:65 S:65 " ∪' " T:65  => SetNotation.union S T
notation:110 " ∪₀' " S:110  => SetNotation.sUnion S
notation:65 S:65 " ∩' " T:65  => SetNotation.inter S T
notation:110 " ∩₀' " S:110  => SetNotation.sInter S
notation:150 "{" x "}'" => SetNotation.singleton x
notation:82 S:82 " ×ˢ' " T:82 => SetNotation.sprod S T
notation:150 "(" a:150 "," b:150 ")'" => SetNotation.pair a b

def SetNotation.subset {set : Type u} [SetNotation set]
  (S T : set) : Prop := ∀ x, x ∈' S → x ∈' T
notation:50 S:50 " ⊆' " T:50 => SetNotation.subset S T
binder_predicate x " ⊆' " y:term => `($x ∈' $y)

def SetNotation.is_a_set {set : Type u} [SetNotation set]
  (p : set → Prop) : Prop := ∃ s, ∀ x, x ∈' s ↔ p x
export SetNotation (is_a_set)

def exists_unique {α : Sort u} (p : α → Prop) : Prop := ∃ x, p x ∧ ∀ y, p y → y = x
section
open Lean
open TSyntax.Compat
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``exists_unique xs b
end
-- example of ∃! n : Nat, 0 < n < 2
example : ∃! n : Nat, 0 < n ∧ n < 2 := by
  unfold exists_unique
  refine ⟨1, ?_, ?_⟩
  . exact ⟨Nat.lt_add_one _, Nat.lt_add_one _⟩
  . intro y hy
    have h1 : 1 ≤ y := Nat.succ_le_of_lt hy.1
    have h2 : y ≤ 1 := Nat.le_of_lt_succ hy.2
    exact Nat.le_antisymm h2 h1


def SetNotation.is_a_function {set : Type u} [SetNotation set]
  (f A B : set) : Prop := f ⊆' A ×ˢ' B ∧ ∀ x ∈' A, ∃! y, (x, y)' ∈' f
export SetNotation (is_a_function)

namespace redundten_zfc

-- Definition 14.1 (unfinished)
class ZFC (set : Type u) extends SetNotation set where
  extensionality (A B : set) : A = B ↔ (∀ x, x ∈' A ↔ x ∈' B)
  emptyset_def : ∀ x : set, ¬ x ∈' ∅'
  replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y) :
    ∀ U : set, is_a_set fun y ↦ ∃ x ∈' U, P x y
  powerset_def (S : set) : ∀ T, T ∈' 𝓟' S ↔ T ⊆' S
  union_def (S T : set) : ∀ x, x ∈' S ∪' T ↔ x ∈' S ∨ x ∈' T -- redundten
  sUnion_def (S : set) : ∀ x, x ∈' ∪₀' S ↔ ∃ A ∈' S, x ∈' A
  inter_def (S T : set) : ∀ x, x ∈' S ∩' T ↔ x ∈' S ∧ x ∈' T -- redundten
  sInter_def (S : set) : ∀ x, x ∈' ∩₀' S ↔ ∀ A ∈' S, x ∈' A -- redundten
  infinity : ∃ S : set, ∅' ∈' S ∧ ∀ x ∈' S, x ∪' {x}' ∈' S
  regularity : ∀ S ≠ (∅' : set), ∃ A ∈' S, A ∩' S = ∅'
  pair_def (a b : set) : (a,b)' = { {a}' }' ∪' { {a}' ∪' {b}' }' -- (a,b) = {{a},{a,b}}, redundten
  sprod_def (A B : set) : ∀ x, x ∈' A ×ˢ' B ↔ ∃ a ∈' A, ∃ b ∈' B, x = (a, b)' -- redundten
  choice (S : set) (hs : S ≠ ∅') :
    ∃ f, is_a_function f S (𝓟' S) ∧ ∀ T, T ≠ ∅' → T ⊆' S → ∃ y ∈' T, (T, y)' ∈' f

-- Proposition 15.1.2
theorem pairing {set : Type u} [ZFC set] (a b : set) :
  is_a_set fun x ↦ x = a ∨ x = b := by
  -- zero = ∅
  let zero : set := ∅'
  let hzero := ZFC.emptyset_def (set := set)
  -- one = {∅}
  let one := 𝓟' zero
  let hone := ZFC.powerset_def zero
  have zero_mem_one : zero ∈' one := by
    rw [hone]
    intro x hxzero
    exact (hzero x hxzero).elim
  -- two = {∅, {∅}}
  let two := 𝓟' one
  let htwo := ZFC.powerset_def one
  have zero_mem_two : zero ∈' two := by
    rw [htwo]
    intro x hxzero
    exact (hzero x hxzero).elim
  have one_mem_two : one ∈' two := by
    rw [htwo]
    intro x hxzero
    exact hxzero
  have zero_ne_one : zero ≠ one := by
    intro h
    rw [ZFC.extensionality] at h
    have := h zero
    exact hzero zero (this.mpr zero_mem_one)
  -- ∀ x, ∃! y, P x y
  -- → {y | ∃ x ∈ U, P(x, y)} is a set
  -- x will replace by zero, one, y will replace by a, b
  let P x y := (x = zero ∧ y = a) ∨ (x ≠ zero ∧ y = b)
  have hP : ∀ x, ∃ y, (P x y ∧ (∀ z, P x z → z = y)) := by
    intro x
    by_cases h : x = zero
    . refine ⟨a, ?_, ?_⟩ -- choose y := a
      . unfold P -- y satisfy P(x, y)
        left
        exact ⟨h, rfl⟩
      . intro z hz -- y is the unique one that satisfies P(x,y)
        unfold P at hz
        apply hz.elim
        . exact fun h' ↦ h'.2
        . exact fun h' ↦ (h'.1 h).elim
    . refine ⟨b, ?_, ?_⟩ -- choose y := b
      . unfold P -- y satisfy P(x, y)
        right
        exact ⟨h, rfl⟩
      . intro z hz  -- y is the unique one that satisfies P(x,y)
        unfold P at hz
        apply hz.elim
        . exact fun h' ↦ (h h'.1).elim
        . exact fun h' ↦ h'.2

  let ⟨S, hS⟩ := ZFC.replacement P hP two
  refine ⟨S, ?_⟩
  intro y
  constructor
  . intro hyS
    let ⟨x, hxtwo, pxy⟩ := (hS y).mp hyS
    apply pxy.elim
    . exact fun h ↦ Or.inl h.2
    . exact fun h ↦ Or.inr h.2
  . refine fun h ↦ h.elim (fun h ↦ ?_) (fun h ↦ ?_)
    . rw [hS]
      refine ⟨zero, zero_mem_two, ?_⟩
      left
      exact ⟨rfl, h⟩
    . rw [hS]
      refine ⟨one, one_mem_two, ?_⟩
      right
      exact ⟨Ne.symm zero_ne_one, h⟩
