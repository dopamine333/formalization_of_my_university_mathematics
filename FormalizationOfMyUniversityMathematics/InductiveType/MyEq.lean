namespace Hidden

universe u

inductive True : Type
  | intro : True

#check True
#check True.intro
#check (True.rec : {motive : True → Sort u} →
  (intro : motive True.intro) →
  (t : True) → motive t)

inductive False : Type

#check False
#check (False.rec : {motive : False → Sort u} →
  (t : False) → motive t)

def exfalso (α : Prop) : False → α := False.rec
-- def exfalso' (α : Type) : False → α := @False.rec (fun _ ↦ α)

inductive A : Type
  | a : A

inductive B : Type → Type
  | b (t : Type): B t

inductive B' (t : Type) : Type
  | b : B' t

inductive C : Type → Type → Type
  | c (t s : Type): C t s

inductive C' (t : Type) : Type → Type
  | c (s : Type): C' t s

inductive C'' (t s : Type) : Type
  | c : C'' t s

#check (A.rec :
  {motive : A → Sort u} →
  (a : motive A.a) →
  (x : A) → (motive x)
)
#check (B.rec :
  {t : Type} →
  {motive : B t → Sort u} →
  (b : motive (B.b t)) →
  (x : B t) → (motive x)
)
#check (B'.rec :
  {t : Type} →
  {motive : B' t → Sort u} →
  (b : motive (B'.b)) →
  (x : B' t) → (motive x)
)
#check (C.rec :
  {t s : Type} →
  {motive : C t s → Sort u} →
  (c : motive (C.c t s)) →
  (x : C t s) → (motive x)
)
#check (C'.rec :
  {t s : Type} →
  {motive : C' t s → Sort u} →
  (c : motive (C'.c s)) →
  (x : C' t s) → (motive x)
)
#check (C''.rec :
  {t s : Type} →
  {motive : C'' t s → Sort u} →
  (c : motive (C''.c)) →
  (x : C'' t s) → (motive x)
)


inductive D : (α : Type) → (a : α) → Type
  | d (β : Type) (b : β) : D β b

#check (D.rec :
  {α : Type} → {a : α} →
  {motive : D α a → Sort u} →
  (d : motive (D.d α a)) →
  (x : D α a) → (motive x)
)

inductive E : Type → Type → Type
  | e (t : Type): E t t

#check (E.rec :
  {t : Type} →
  {motive : (s : Type) → E t s → Sort u} →
  (e : motive t (E.e t)) →
  (s : Type) → (x : E t s) → (motive s x)
)


inductive E' : Type → Type → Type
  | e : E' True True

#check (E'.rec :
  {motive : (t s : Type) → E' t s → Sort u} →
  (e : motive True True (E'.e)) →
  (t s : Type) → (x : E' t s) → (motive t s x)
)

inductive MyEq (α : Type) (a : α) : α → Prop
  | refl : MyEq α a a

#check (MyEq.rec :
  {α : Type} → {a : α} →
  {motive : (b : α) → MyEq α a b → Sort u} →
  (refl : motive a MyEq.refl) →
  {b : α} → (x : MyEq α a b) → (motive b x)
)

-- set_option pp.all true

def symm (α : Type) (a b : α) : MyEq α a b → MyEq α b a
  | @MyEq.refl α a => @MyEq.refl α a

#print symm

def symm' (α : Type) (a b : α) : MyEq α a b → MyEq α b a :=
  @MyEq.rec α a (fun b _ ↦ MyEq α b a) (MyEq.refl) b

#print symm'

def trans (α : Type) (a b c : α) : MyEq α a b → MyEq α b c → MyEq α a c
  | .refl, .refl => .refl

def subst {α : Type} {a b : α} (p : α → Prop) (h : MyEq α a b) : p a → p b := by
  match h with
  | .refl => exact fun x ↦ x

def subst' {α : Type} {a b : α} (p : α → Prop) : MyEq α a b → p a → p b
  | .refl => id

def subst'' {α : Type} {a b : α} (p : α → Prop) (h : MyEq α a b) (ha : p a) : p b := by
  match h with
  | .refl => exact ha

inductive MyEq₂ {α : Type} : α → α → Prop
  | refl {a} : MyEq₂ a a

#check (MyEq₂.rec :
  {α : Type} → {a : α} →
  {motive : (b : α) → (MyEq₂ a b) → Sort u} →
  (refl : motive a MyEq₂.refl) →
  (b : α) → (t : MyEq₂ a b) → (motive b t)
)
