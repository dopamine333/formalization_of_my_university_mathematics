import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

-- import MIL.Common

section I
variable {G : Type} [Group G]

--Consider the action of a group G on itself by left multiplication:
def leftmul : MulAction G G where
  smul g x := g * x
  one_smul := by
    intro x
    exact one_mul x
  mul_smul := by
    intro g1 g2 x
    exact mul_assoc g1 g2 x

--Consider the action of a group G on itself by conjugation:
def conj : MulAction G G where
  smul g x := g * x * g⁻¹
  one_smul := by
    intro x
    show 1 * x * 1⁻¹ = x
    rw [one_mul, inv_one, mul_one]
  mul_smul := by
    intro g1 g2 x
    show (g1 * g2) * x * (g1 * g2)⁻¹ = g1 * (g2 * x * g2⁻¹) * g1⁻¹
    rw [mul_inv_rev]
    simp only [mul_assoc]

end I

section II
variable {G X : Type} [Group G] [MulAction G X]
/-
A group action can be interpreted as
a group homomorphism from G to the symmetric group S(X) :
-/
#check X ≃ X
#synth Group (X ≃ X)

def ρ1 : G → (X → X) := fun g x ↦ g • x

def ρ2 : G → (X ≃ X) := fun g ↦ (
  { toFun := ρ1 g
    invFun := ρ1 g⁻¹
    left_inv := by
      intro x
      rw [ρ1, ρ1]
      rw [← mul_smul]
      rw [inv_mul_cancel, one_smul]
    right_inv := by
      intro x
      rw [ρ1, ρ1]
      rw [← mul_smul]
      rw [mul_inv_cancel, one_smul]
  }
)

def ρ3 : G →* (X ≃ X) where
  toFun := ρ2
  map_one' := by
    ext x
    rw [ρ2]; dsimp
    rw [ρ1]
    exact one_smul G x
  map_mul' := by
    intro g1 g2
    ext x
    dsimp [ρ2,ρ1]
    exact mul_smul g1 g2 x

example : ρ3 = MulAction.toPermHom G X := rfl
end II

section III

def orbit (G : Type) {X : Type} [Group G] [MulAction G X] (x : X) : Set X := {y : X | ∃ g : G, g • x = y}

example (G : Type) {X : Type} [Group G] [MulAction G X] (x : X)
  : orbit G x = Set.range ((. • x) : G → X) := by simp [orbit, Set.range]

@[ext]
structure InvariantSet (G X: Type) [Group G] [MulAction G X] where
  carriar : Set X
  invar : ∀ {g : G} {x : X}, x ∈ carriar → g • x ∈ carriar

instance {G X : Type} [Group G] [MulAction G X] : SetLike (InvariantSet G X) X  where
  coe := InvariantSet.carriar
  coe_injective' _ _ := InvariantSet.ext

instance {G X : Type} [Group G] [MulAction G X] : PartialOrder (InvariantSet G X) := by infer_instance

def orbit_invariant_set (G : Type) {X : Type} [Group G] [MulAction G X] (x : X)
  : InvariantSet G X where
  carriar := orbit G x
  invar := by
    rintro g _ ⟨g', rfl⟩
    use g * g'
    apply mul_smul

#check Subtype.partialOrder
instance {G X : Type} [Group G] [MulAction G X] (x : X) : PartialOrder ({ A : InvariantSet G X // x ∈ A}) := by infer_instance

-- Note that the G-orbit x is indeed the smallest G-invariant subset containing x.
#check OrderBot
instance {G X : Type} [Group G] [MulAction G X] (x : X)
  : OrderBot ({ A : InvariantSet G X // x ∈ A}) where
    bot := ⟨orbit_invariant_set G x, by use 1; rw [one_smul]⟩
    bot_le := by
      rintro ⟨A, hxA⟩ _ ⟨g, rfl⟩; dsimp
      exact A.invar hxA

end III

section IV

-- A group action is faithful if only the identity element acts trivially on all x ∈ X
def IsFaithful (G X : Type) [Group G] [MulAction G X] : Prop := ∀ g : G, (∀ x : X, g • x = x) → g = 1

example (G X :Type) [Group G] [MulAction G X]
  : IsFaithful G X ↔ Function.Injective (fun g : G ↦ ((g • .) : (X → X))) := by
  constructor
  . intro h g1 g2 h'
    dsimp at h'
    rw [funext_iff] at h'
    have : ∀ (x : X), (g2⁻¹ * g1) • x = x := by
      intro x
      rw [mul_smul, h' x, ← mul_smul, inv_mul_cancel, one_smul]
    have := h (g2⁻¹ * g1) this
    rwa [inv_mul_eq_iff_eq_mul, mul_one] at this
  . intro h g h'
    have : (g • .) =  (((1 : G) • .) : X → X) := by
      ext x
      rw [h' x, one_smul]
    exact h this

end IV

section V

-- A group action is transitive if there is only one orbit.
#check Nat.card_eq_one_iff_exists
def IsTransitive (G X : Type) [Group G] [MulAction G X] : Prop :=
  Nat.card (Set.range (orbit G : X → Set X)) = 1

theorem IsTransitive_iff (G X : Type) [Group G] [MulAction G X]
  : IsTransitive G X ↔ ∃ x : X, ∀ y : X, orbit G y = orbit G x := by
    simp [IsTransitive, Nat.card_eq_one_iff_exists]


example (G X :Type) [Group G] [MulAction G X]
  : IsTransitive G X ↔ ∃ x : X, Function.Surjective ((. • x) : G → X) := by
  rw [IsTransitive_iff]
  constructor
  . rintro ⟨x, h⟩
    use x
    intro y
    have orbit_eq := h y
    rw [orbit, orbit] at orbit_eq
    have : y ∈ {y_1 : X| ∃ g : G, g • y = y_1} := by
      use 1; rw [one_smul]
    rw [orbit_eq] at this
    rcases this with ⟨g, rfl⟩
    use g
  . rintro ⟨x, surj⟩
    use x
    intro y
    ext z
    dsimp [orbit]
    constructor
    . rintro ⟨g, rfl⟩
      obtain ⟨g',rfl⟩ := surj y; dsimp
      use g * g'
      rw [mul_smul]
    . rintro ⟨g, rfl⟩
      obtain ⟨g',rfl⟩ := surj y; dsimp
      use g * g'⁻¹
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]

end V
