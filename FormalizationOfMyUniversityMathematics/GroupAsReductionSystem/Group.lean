
namespace GroupAsReductionSystem

inductive Group (G : Type) [One G]: Type
  | of : G → Group G
  | one : Group G
  | mul : Group G → Group G → Group G
  | inv : Group G → Group G

variable {G : Type} [One G]
instance : One (Group G)  := ⟨Group.one⟩
instance : Mul (Group G) := ⟨Group.mul⟩
instance : Inv (Group G) := ⟨Group.inv⟩

inductive GroupEq : Group G → Group G → Type
  | rfl {a} : GroupEq a a
  | symm {a b}: GroupEq a b → GroupEq b a
  | trans {a b c} : GroupEq a b → GroupEq b c → GroupEq a c

  | mul_congr_left {a b c} : GroupEq a b → GroupEq (a * c) (b * c)
  | mul_congr_right {a b c} : GroupEq a b → GroupEq (c * a) (c * b)
  | inv_congr {a b} : GroupEq a b → GroupEq a⁻¹ b⁻¹
  | coe_of : GroupEq (.of 1) 1

  | one_mul {a} : GroupEq (1 * a) a
  | mul_one {a} : GroupEq (a * 1) a
  | mul_assoc {a b c} : GroupEq (a * b * c) (a * (b * c))
  | mul_inv {a} : GroupEq (a * a⁻¹) 1
  | inv_mul {a} : GroupEq (a⁻¹ * a) 1

infixl:50 " =G " => GroupEq

def trivial_group [Subsingleton G] : (g : Group G) → g =G 1
  | .of x => by
    have h1 : x = 1 := Subsingleton.allEq x 1
    have h2 : .of x =G .of 1 := by rw [h1]; exact .rfl
    have h3 : (.of 1 : Group G) =G 1 := .coe_of
    have h4 : .of x =G 1 := h2.trans h3
    exact h4
  | .one => .rfl
  | .mul a b => by
    have h1 : a =G 1 := trivial_group a
    have h2 : b =G 1 := trivial_group b
    have h3 : a * b =G a * 1 := .mul_congr_right h2
    have h4 : a * 1 =G 1 * 1 := .mul_congr_left h1
    have h5 : (1 : Group G) * 1 =G 1 := .mul_one
    have h6 : a * b =G 1 := (h3.trans h4).trans h5
    exact h6
  | .inv a => by
    have h1 : a =G 1 := trivial_group a
    have h2 : a⁻¹ =G 1⁻¹ := .inv_congr h1
    have h3 : (1⁻¹ : Group G) =G 1 * 1⁻¹ := .symm .one_mul
    have h4 : (1 : Group G) * 1⁻¹ =G 1 := .mul_inv
    have h5 : a⁻¹ =G 1 := (h2.trans h3).trans h4
    exact h5

#eval (trivial_group ((1 * 1) : Group (Fin 1)))
#eval (trivial_group (1⁻¹ : Group (Fin 1)))

def allEq [Subsingleton G] (a b : Group G) : a =G b := (trivial_group a).trans (trivial_group b).symm

#eval (@allEq (Fin 1) _ _ (1 * 1) (.of 0))

#check Nat.add_right_cancel

def add_right_cancel {a b c : Group G} (h : a * c =G b * c) : a =G b := by
  have h1 (x : Group G ): x =G (x * c) * c⁻¹ := .trans (.symm .mul_one) (.trans (.mul_congr_right (.symm .mul_inv)) (.symm .mul_assoc))
  have h2 : (a * c) * c⁻¹ =G (b * c) * c⁻¹ := .mul_congr_left h
  have h3 : a =G b := ((h1 a).trans h2).trans (h1 b).symm
  exact h3
