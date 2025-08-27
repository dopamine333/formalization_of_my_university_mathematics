import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

variable (G : Type u) [Group G]


#check Abelianization G

#synth (⊤ : Subgroup G).Normal
#synth ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆.Normal
#synth (commutator G).Normal
example : Abelianization G = (G ⧸ commutator G) := rfl

def my_commGroup : CommGroup (Abelianization G) := by
  refine @CommGroup.ofIsMulCommutative (G ⧸ commutator G) _ {is_comm := ?_}
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]

set_option trace.Meta.synthInstance true in
example [One M] : Nonempty M := inferInstance
example [One M] : Inhabited M := ⟨1⟩


/-- `of` is the canonical projection from G to its abelianization. -/
def my_of : G →* Abelianization G := QuotientGroup.mk' (commutator G)

example : my_of G = Abelianization.of := rfl

open Abelianization (of)

theorem my_ker_of : of.ker = commutator G := by
  apply QuotientGroup.ker_mk'

theorem my_ker_of' : of.ker = commutator G := by
  ext g
  calc g ∈ of.ker
    _ ↔ of g = 1 := by rfl
    _ ↔ (g : G ⧸ commutator G) = 1 := by rfl
    _ ↔ g ∈ commutator G := by rw [QuotientGroup.eq_one_iff]

variable {A : Type v} [CommGroup A] (f : G →* A)

#check Subgroup.toCommGroup
#check QuotientGroup.quotientKerEquivRange
-- example [CommGroup M] [Group N] (h : M ≃* N) : CommGroup N := by apply?
#check CommGroup.ofIsMulCommutative
#check IsMulCommutative

theorem my_commutator_subset_ker : commutator G ≤ f.ker := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  -- have : CommGroup A := by infer_instance
  let : CommGroup f.range := Subgroup.toCommGroup _
  let : CommGroup (G ⧸ f.ker) := by
    refine {mul_comm a b := ?_}
    let φ : G ⧸ f.ker ≃* f.range := QuotientGroup.quotientKerEquivRange f
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  apply this.to_isCommutative

theorem my_commutator_subset_ker' : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨g₁, g₂, rfl⟩
  show f ⁅g₁, g₂⁆ = 1
  simp [commutatorElement_def, mul_inv_cancel_comm]


def my_lift : (G →* A) ≃ (Abelianization G →* A) where
  toFun f := QuotientGroup.lift _ f (Abelianization.commutator_subset_ker _)
  invFun f := f.comp (QuotientGroup.mk' _)
  right_inv f := MonoidHom.ext fun x ↦ QuotientGroup.induction_on x fun x ↦ rfl


example : my_lift G (A := A) = Abelianization.lift := by rfl


theorem my_lift_unique (φ : Abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
  {x : Abelianization G} : φ x = Abelianization.lift f x := by
  apply QuotientGroup.induction_on (C := fun y ↦ φ y = Abelianization.lift f y) x
  intro x
  calc φ (of x)
    _ = f x := hφ x
    _ = Abelianization.lift f (of x) := rfl

open Abelianization (lift)
theorem my_lift_of : lift of = MonoidHom.id (Abelianization G) := by
  apply MonoidHom.ext
  refine fun x ↦ QuotientGroup.induction_on x (fun x ↦ ?_)
  calc (lift of) (of x)
    _ = (of x) := rfl
    _ =  MonoidHom.id (Abelianization G) (of x) := rfl
theorem my_lift_of' : lift of = MonoidHom.id (Abelianization G) := by
  ext
  exact rfl


variable {H : Type v} [Group H] (f : G →* H)

open Abelianization (map)
theorem my_map_id
  {G : Type u} [Group G]
  : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) := by
  /-  map f = lift (of.comp f) -/
  apply MonoidHom.ext
  refine fun x ↦ QuotientGroup.induction_on x (fun x ↦ ?_)
  calc (map (MonoidHom.id G)) (of x)
    _ = lift (of.comp (MonoidHom.id G)) (of x) := rfl
    _ = (of.comp (MonoidHom.id G)) x := rfl
    _ = of ((MonoidHom.id G) x) := rfl
    _ = of x := rfl
    _ = MonoidHom.id (Abelianization G) (of x) := rfl

theorem my_map_comp
  {G : Type u} [Group G] {H : Type v} [Group H] (f : G →* H) {I : Type w} [Group I]
  (g : H →* I) : (map g).comp (map f) = map (g.comp f) := by
  apply MonoidHom.ext
  refine fun x ↦ QuotientGroup.induction_on x (fun x ↦ rfl)


theorem map_map_apply
  {G : Type u} [Group G] {H : Type v} [Group H] (f : G →* H) {I : Type w} [Group I]
  {g : H →* I} {x : Abelianization G}
  : (map g) ((map f) x) = (map (g.comp f)) x := by
  refine QuotientGroup.induction_on x (fun x ↦ rfl)

def my_equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := fun x ↦ QuotientGroup.induction_on x (fun x ↦ rfl)
  }

def my_equivOfComm' {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨x⟩
      exact rfl
  }
