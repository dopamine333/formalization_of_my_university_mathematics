inductive Group : Type
  | one : Group
  | mul : Group → Group → Group
  | inv : Group → Group

#check Group.rec

instance : One Group := ⟨Group.one⟩
instance : Mul Group := ⟨Group.mul⟩
instance : Inv Group := ⟨Group.inv⟩

inductive GroupEq : Group → Group → Type
  | rfl {a} : GroupEq a a
  | symm {a b}: GroupEq a b → GroupEq b a
  | trans {a b c} : GroupEq a b → GroupEq b c → GroupEq a c

  | mul_congr_left {a b c} : GroupEq a b → GroupEq (a * c) (b * c)
  | mul_congr_right {a b c} : GroupEq a b → GroupEq (c * a) (c * b)
  | inv_congr {a b} : GroupEq a b → GroupEq a⁻¹ b⁻¹

  | one_mul {a} : GroupEq (1 * a) a
  | mul_one {a} : GroupEq (a * 1) a
  | mul_assoc {a b c} : GroupEq (a * b * c) (a * (b * c))
  | mul_inv {a} : GroupEq (a * a⁻¹) 1
  | inv_mul {a} : GroupEq (a⁻¹ * a) 1

infixl:50 "=G" => GroupEq

def trivial_group : (g : Group) → g =G 1
  | .one => .rfl
  | .mul a b => by
    have h1 : a =G 1 := trivial_group a
    have h2 : b =G 1 := trivial_group b
    have h3 : a * b =G a * 1 := .mul_congr_right h2
    have h4 : a * 1 =G 1 * 1 := .mul_congr_left h1
    have h5 : 1 * 1 =G 1 := .mul_one
    have h6 : a * b =G 1 := (h3.trans h4).trans h5
    exact h6
  | .inv a => by
    have h1 : a =G 1 := trivial_group a
    have h2 : a⁻¹ =G 1⁻¹ := .inv_congr h1
    have h3 : 1⁻¹ =G 1 * 1⁻¹ := .symm .one_mul
    have h4 : 1 * 1⁻¹ =G 1 := .mul_inv
    have h5 : a⁻¹ =G 1 := (h2.trans h3).trans h4
    exact h5

#eval (trivial_group (1 * 1))
#eval (trivial_group (1⁻¹))

def allEq (a b : Group) : a =G b := (trivial_group a).trans (trivial_group b).symm

#eval (allEq 1 1)
