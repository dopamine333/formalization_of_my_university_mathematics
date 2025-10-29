import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic.Choose
import Mathlib.Data.SProd
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SimpRw

-- introduce all axioms of zfc
section Axioms

/-- A basic class for set theory, providing the membership relation `∈`.
-/
class SetTheory (set : Type u) extends Membership set set

variable (set : Type u) [SetTheory set]

instance : HasSubset set := ⟨fun S T ↦ ∀ {x}, x ∈ S → x ∈ T⟩

/-- ### Definition 14.1.1. axiom of extensionality:
two sets are equal if and only if they have the same elements
that is, for any x, one has x ∈ A ↔ x ∈ B.
-/
class AxiomOfExtensionality where
  extensionality : ∀ a b : set, a = b ↔ ∀ x, x ∈ a ↔ x ∈ b

/-- ### Definition 14.1.2. axiom of empty set:
there exists a set S such that for all x, the statement x ∈ S is false.
-/
class AxiomOfEmptyset extends EmptyCollection set where
  not_mem_empty : ∀ x, x ∉ (∅ : set)

/-- ### Definition 14.1.3. axiom of replacement:
if P(x,y) is a predicate in two variables such that
for each x, there is a unique y such that P(x,y) holds,
then for every set U, {y | there exists x ∈ U such that P(x,y) holds} is a set.
-/
class AxiomOfReplacement where
  replacement (P : set → set → Prop) (U : set) : set
  mem_replacement_iff (P : set → set → Prop) (U : set) :
    (∀ x, ∃! y, P x y) → (∀ y, y ∈ replacement P U ↔ ∃ x, x ∈ U ∧ P x y)

/-- ### Definition 14.1.4. axiom of power set:
if S is a set, then the collection of all subsets of S is also a set, that is,
if S is a set, then the set {T | T ⊆ S} is a set.
-/
class AxiomOfPowerset where
  powerset : set → set
  mem_powerset_iff (S : set) : ∀ T, T ∈ powerset S ↔ T ⊆ S
prefix:100 "𝒫 " => AxiomOfPowerset.powerset

/-- ### Definition 14.1.5. axiom of union:
if S is a set, then the union of all sets that are elements in S is also a set, that is,
if S is a set then the set ⋃ A ∈ S, A = {x ∈ A | A ∈ S} is a set.
-/
class AxiomOfUnion where
  sUnion : set → set
  mem_sUnion_iff (S : set) : ∀ x, x ∈ sUnion S ↔ ∃ A ∈ S, x ∈ A
prefix:110 "⋃₀ " => AxiomOfUnion.sUnion

/-- To state the axiom of infinity, we need union and singleton sets
-/
class PrerequisitesForInfinity extends Union set, Singleton set set where
  mem_union_iff (S T : set) : ∀ x, x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T
  mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x

/-- ### Definition 14.1.6. axiom of infinity:
there exists a set S such that ∅ ∈ S and if x ∈ S then x ∪ {x} ∈ S.
-/
class AxiomOfInfinity [AxiomOfEmptyset set] [PrerequisitesForInfinity set] where
  infinity : set
  empty_mem_infinity : ∅ ∈ infinity
  succ_mem_infinity : ∀ x ∈ infinity, x ∪ {x} ∈ infinity

/-- To state the axiom of regularity, we need intersection of two sets
-/
class PrerequisitesForRegularity extends Inter set where
  mem_inter_iff (S T : set) : ∀ x, x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T

/-- ### Definition 14.1.7. axiom of regularity:
every nonempty set S has an element which has empty intersection with S, that is,
if S ≠ ∅, then there exists A ∈ S such that A ∩ S = ∅.
-/
class AxiomOfRegularity [AxiomOfEmptyset set] [PrerequisitesForRegularity set] where
  regularity : ∀ S ≠ (∅ : set), ∃ A ∈ S, A ∩ S = ∅


/-- To state the axiom of choice, we need ordered pairs and Cartesian products
-/
class PrerequisitesForChoice extends SProd set set set where
  ordered_pair : set → set → set
  ordered_pair_inj (a b x y : set) : ordered_pair a b = ordered_pair x y ↔ a = x ∧ b = y
  mem_product_iff (A B : set) : ∀ x, x ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b
notation :150 "(" a:150 ", " b:150 ")ˢ" => PrerequisitesForChoice.ordered_pair a b

section Function
variable {set} [PrerequisitesForChoice set]
/-- ### Definition 11.1.1
Let A and B be two sets.
A function f ∶ A → B is defined to be a relation, denoted by f, from A to B
such that for any x ∈ A there exists a unique y ∈ B such that (x,y) ∈ f.
In this case, for x ∈ A, we denote such a unique y ∈ B by f(x),
-/
def is_function (A B f : set) : Prop := f ⊆ A ×ˢ B ∧ ∀ a ∈ A, ∃! b ∈ B, (a, b)ˢ ∈ f
noncomputable def toFun
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A) : set :=
  Classical.choose (hf.2 a ha)
end Function

/-- ### Definition 14.1.8. axiom of choice:
if S is a nonempty set and P(S) denotes the power set of S,
then there exists a function f ∶ P(S) → S such that f(T) ∈ T for any nonempty set T ∈ P(S).
-/
class AxiomOfChoice [AxiomOfEmptyset set] [AxiomOfPowerset set] [PrerequisitesForChoice set]  where
  choice (S : set) : set
  choice_is_function (S : set) (hS : S ≠ ∅) : is_function (𝒫 S) S (choice S)
  choice_mem (S : set) (hS : S ≠ ∅) : ∀ T, (hT : T ∈ 𝒫 S) → T ≠ ∅ → toFun (choice_is_function S hS) hT ∈ T

-- make all the definitions and axioms available when opening the SetTheory namespace
namespace SetTheory
export AxiomOfExtensionality (extensionality)
export AxiomOfEmptyset (not_mem_empty)
export AxiomOfReplacement (replacement mem_replacement_iff)
export AxiomOfPowerset (powerset mem_powerset_iff)
export AxiomOfUnion (mem_sUnion_iff)
export PrerequisitesForInfinity (mem_union_iff mem_singleton_iff)
export AxiomOfInfinity (infinity empty_mem_infinity succ_mem_infinity)
export PrerequisitesForRegularity (mem_inter_iff)
export AxiomOfRegularity (regularity)
export PrerequisitesForChoice (ordered_pair ordered_pair_inj mem_product_iff)
export AxiomOfChoice (choice choice_is_function choice_mem)
end SetTheory

end Axioms

-- justify that we can state the axiom of infinity, regularity, and choice
-- and so we can define ZFC
section ZFC

open SetTheory

/-- ### Proposition 15.1.1
The axioms of extensionality, empty set and replacement imply the axiom of specification,
that is, if U is a set and if P(x) is a predicate, then {x ∈ U | P(x)} is a set.
-/
noncomputable def specification {set : Type u} [SetTheory set]
    [AxiomOfEmptyset set] [AxiomOfReplacement set]
    (P : set → Prop) (U : set) : set :=
  haveI := Classical.propDecidable
  if h : ∃ x ∈ U, P x then
    let l := Classical.choose h
    let Q x y := P x ∧ y = x ∨ ¬ P x ∧ y = l
    replacement Q U
  else
    ∅

theorem mem_specification_iff {set : Type u} [SetTheory set]
    [AxiomOfEmptyset set] [AxiomOfReplacement set]
    (P : set → Prop) (U : set) (y : set) :
    y ∈ specification P U ↔ y ∈ U ∧ P y := by
    by_cases h : ∃ x ∈ U, P x
    case neg =>
      simp [specification, h]
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
    simp [specification,h]
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

/-- ### Proposition 15.1.2
The axioms of empty set, power set, and replacement together imply
that the collection of two sets is a set, which is called the axiom of pairing.
-/
def pairing {set : Type u} [SetTheory set]
    [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set]
    (a b : set) : set :=
  replacement (fun x y ↦ x = ∅ ∧ y = a ∨ x ≠ ∅ ∧ y = b) (𝒫 𝒫 ∅)

theorem mem_pairing_iff {set : Type u} [SetTheory set]
    [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set]
    (a b y : set) :
    y ∈ pairing a b ↔ y = a ∨ y = b := by
    rw [pairing, mem_replacement_iff]
    . constructor
      . rintro ⟨x, _, (⟨_, ha⟩ | ⟨_, hb⟩)⟩
        . exact Or.inl ha
        . exact Or.inr hb
      . rintro (rfl | rfl)
        . refine ⟨∅, ?_, ?_⟩
          . rw [mem_powerset_iff]
            exact fun h ↦ (not_mem_empty _ h).elim
          . left
            exact ⟨rfl, rfl⟩
        . refine ⟨𝒫 ∅, ?_, ?_⟩
          . rw [mem_powerset_iff]
            exact id
          . right
            refine ⟨fun h ↦ ?_, rfl⟩
            have : ∅ ∈ (∅ : set) := by
              nth_rw 1 [← h, mem_powerset_iff]
              exact fun h ↦ (not_mem_empty _ h).elim
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

instance prerequisitesForInfinitySatisfied (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set] [AxiomOfUnion set]
  : PrerequisitesForInfinity set where
  union S T := ⋃₀ (pairing S T)
  singleton x := pairing x x
  mem_union_iff S T x := by
    simp [mem_sUnion_iff, mem_pairing_iff]
  mem_singleton_iff x y := by
    simp [mem_pairing_iff]

noncomputable instance prerequisitesForRegularitySatisfied (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] : PrerequisitesForRegularity set where
  inter S T := specification (. ∈ T) S
  mem_inter_iff S T x := by
    simp [mem_specification_iff]

-- this enable notation like {a, b, c}
section notation_for_sets_of_finite_elements

instance SetTheory.instInsert (set : Type u) [SetTheory set]
  [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set] [AxiomOfUnion set] :
  Insert set set where insert x S := {x} ∪ S

theorem mem_insert_iff {set : Type u} [SetTheory set]
    [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set] [AxiomOfUnion set]
    (x S y : set) : y ∈ insert x S ↔ y = x ∨ y ∈ S := by
  simp [Insert.insert, mem_union_iff, mem_singleton_iff]

instance SetTheory.instLawfulSingleton (set : Type u) [SetTheory set]
  [AxiomOfExtensionality set] [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set] [AxiomOfUnion set] :
  LawfulSingleton set set where
  insert_empty_eq x := by simp [extensionality, mem_insert_iff, mem_singleton_iff, not_mem_empty]

end notation_for_sets_of_finite_elements

noncomputable instance prerequisitesForChoiceSatisfied (set : Type u) [SetTheory set]
  [AxiomOfExtensionality set] [AxiomOfEmptyset set] [AxiomOfReplacement set] [AxiomOfPowerset set] [AxiomOfUnion set]
  : PrerequisitesForChoice set where
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
  sprod A B := specification (fun x ↦ ∃ a ∈ A, ∃ b ∈ B, x = {{a}, {a, b}}) (𝒫 (𝒫 (A ∪ B)))
  mem_product_iff A B x := by
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

class ZFC (set : Type u) [SetTheory set] extends
  AxiomOfExtensionality set,
  AxiomOfEmptyset set,
  AxiomOfReplacement set,
  AxiomOfPowerset set,
  AxiomOfUnion set,
  AxiomOfInfinity set,
  AxiomOfRegularity set,
  AxiomOfChoice set

end ZFC
