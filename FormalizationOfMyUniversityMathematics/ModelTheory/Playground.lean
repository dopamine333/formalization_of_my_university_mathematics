import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic


#check FirstOrder.Language
#check FirstOrder.Language.Term
#check FirstOrder.Language.Formula
#check FirstOrder.Language.BoundedFormula

#check Matrix.vecCons
#check (![1,2,-2] : Fin 3 → ℤ)
#check (![1,1,1,1,1] : Fin 5 → ℕ)

section
variable (L : FirstOrder.Language) (α : Type) (n : ℕ) (φ : L.Formula α)
#check FirstOrder.Language.BoundedFormula.falsum
#check (⊥ : L.BoundedFormula α n)
#check (⊥ : L.Formula α)
#check (φ.imp ⊥ : L.Formula α)
#check (FirstOrder.Language.BoundedFormula.imp)
#check (FirstOrder.Language.Formula.imp)

open scoped FirstOrder
#check ((. =' .)  : L.Term (α ⊕ Fin 0) → L.Term (α ⊕ Fin 0) → L.Formula α)
#check ((. ⟹ .)  : L.Formula α → L.Formula α → L.Formula α)
#check ((∀' .) : L.BoundedFormula α (n + 1) → L.BoundedFormula α n)
#check ((∼ .) : L.Formula α → L.Formula α )

end

section
-- def ε-δ definition of `limit_{x → a} f(x) = L` as a `L.Formula {x, a, L}`
open scoped FirstOrder

variable
  -- language
  {L : FirstOrder.Language}
  -- functions
  {zero : L.Constants} {f : L.Functions 1} {abs : L.Functions 1}
  {sub : L.Functions 2}
  -- relations
  {lt : L.Relations 2}
  -- indice of variables
  {α : Type} (x₀ y₀ : α)

def ε : L.Term (α ⊕ Fin 3) := L.var (Sum.inr 2)
def δ : L.Term (α ⊕ Fin 3) := L.var (Sum.inr 1)
def x : L.Term (α ⊕ Fin 3) := L.var (Sum.inr 0)

-- |f(x) - y₀|
example : L.Term (α ⊕ Fin 3) :=
  abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))

-- |f(x) - y₀| < ε
example : L.BoundedFormula α 3 :=
  lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε)

-- |x - x₀| < δ
example : L.BoundedFormula α 3 :=
  lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ)

-- |x - x₀| < δ → |f(x) - y₀| < ε
example : L.BoundedFormula α 3 :=
  (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ))
  ⟹
  (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε))

-- ∀ x, |x - x₀| < δ → |f(x) - y₀| < ε
example : L.BoundedFormula α 2 :=
  ∀'(
    (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ))
    ⟹
    (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε))
  )

-- 0 < δ → ∀ x, |x - x₀| < δ → |f(x) - y₀| < ε
example : L.BoundedFormula α 2 :=
  lt.boundedFormula₂ zero.term &0 -- `before ∀', δ = &1, after ∀', δ = &0` ?
  ⟹
  ∀'(
    (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ))
    ⟹
    (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε))
  )

-- ∃ δ, 0 < δ → ∀ x, |x - x₀| < δ → |f(x) - y₀| < ε
example : L.BoundedFormula α 1 :=
  ∀'(
    lt.boundedFormula₂ zero.term &0
    ⟹
    ∀'(
      (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ))
      ⟹
      (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε))
    )
  )

-- ∀ ε, 0 < ε → ∃ δ, 0 < δ → ∀ x, |x - x₀| < δ → |f(x) - y₀| < ε
example : L.Formula α :=
  ∀'(
    lt.boundedFormula₂ zero.term &0
    ⟹
    ∀'(
      lt.boundedFormula₂ zero.term &0
      ⟹
      ∀'(
        (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (x) (L.var (Sum.inl x₀)))) (δ))
        ⟹
        (lt.boundedFormula₂ (abs.apply₁ (sub.apply₂ (f.apply₁ x) (L.var (Sum.inl y₀)))) (ε))
      )
    )
  )

end

#check FirstOrder.Language.Structure
#check FirstOrder.Language.Term.realize
#check FirstOrder.Language.Formula.Realize
#check FirstOrder.Language.BoundedFormula.Realize
#check FirstOrder.Language.Sentence.Realize
#check (. ⊨ . : _ → FirstOrder.Language.Sentence _ → Prop)
#check FirstOrder.Language.Theory.Model

#check FirstOrder.Language.BoundedFormula.subst
#check FirstOrder.Language.BoundedFormula

/-

For each n ∈ ℕ, let Funcₙ, Relₙ be a set.
then L = {Funcₙ | n ∈ ℕ} ∪ {Relₙ | n ∈ ℕ} is called a language.

Let L be a language.
Define Term be the 'unique' set satisfying
1. ∃ var : ℕ → Term is 1-1
2. ∀ n ∈ ℕ, ∃ funcₙ : Funcₙ × Termⁿ → Term is 1-1
3. Term = Im(var) ⊔ (⨆_{n ∈ ℕ}, Im(funcₙ))

Let L be a language.
Define Formula be the 'unique' set satisfying
1. ∃ ⊥ ∈ Formula
2. ∃ equal : Term × Term → Formula is 1-1
3. ∀ n ∈ ℕ, ∃ relₙ : Relₙ × Termⁿ → Formula is 1-1
4. ∃ imp : Formula × Formula → Formula is 1-1
5. ∃ all : Formula → Formula is 1-1
6. Formula = {⊥} ⊔ Im(equal) ⊔ (⨆_{n ∈ ℕ}, Im(relₙ)) ⊔ Im(imp) ⊔ Im(all)


/-- `BoundedFormula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : BoundedFormula n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ (Fin n))) : BoundedFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) : BoundedFormula n
  /-- The implication between two bounded formulas -/
  | imp {n} (f₁ f₂ : BoundedFormula n) : BoundedFormula n
  /-- The universal quantifier over bounded formulas -/
  | all {n} (f : BoundedFormula (n + 1)) : BoundedFormula n

-/

#check FirstOrder.Language.Term.relabel
#check FirstOrder.Language.Formula.relabel

#check BooleanAlgebra
#synth BooleanAlgebra Prop
#check FirstOrder.Language.Sentence.Realize
#check FirstOrder.Language.Theory.Model
#check 1 + 1 = 2

#check Cardinal
#check Cardinal.mk Prop
#check Cardinal.mk_Prop

#check FirstOrder.Language.Theory.IsComplete
#check FirstOrder.Language.completeTheory

-- #check (. ⊩ .)
-- #check (. ⊢ .)
-- #check (. ⊨ .)
-- #check (. ⊨ᵇ .)

#check Empty
#check (Empty : Sort 1)
#check (PEmpty : Sort 0)
#check PEmpty.{0}
#check (PEmpty : Sort 1)
#check (PEmpty : Sort 2)
#check PEmpty.{0} → PEmpty.{2}
#check PEmpty.{3} → PEmpty.{2}
#check (PEmpty.{3} → PEmpty.{2} : Sort (max 3 1))

#check PSet
#check Nonempty PSet
#synth Nonempty PSet
#synth Inhabited PSet
#check PSet.instInhabited
#check PEmpty.elim
#check Empty.elim
#check (⟨PEmpty.{11}, PEmpty.elim.{12, 11}⟩ : PSet.{10})
#check (⟨Empty, Empty.elim⟩ : PSet)

#check FirstOrder.Language.Structure
#check ZFSet
#check FirstOrder.Language.Theory.IsSatisfiable

#check FirstOrder.Language.BoundedFormula.falsum
#check FirstOrder.Language.BoundedFormula.realize_all
#check FirstOrder.Language.BoundedFormula.realize_bot
#check FirstOrder.Language.BoundedFormula.realize_ex
#check FirstOrder.Language.BoundedFormula.realize_inf
#check FirstOrder.Language.BoundedFormula.realize_sup
#check FirstOrder.Language.BoundedFormula.realize_not
#print axioms FirstOrder.Language.BoundedFormula.realize_all
#print axioms FirstOrder.Language.BoundedFormula.realize_ex
#print axioms FirstOrder.Language.BoundedFormula.realize_bot
#print axioms FirstOrder.Language.BoundedFormula.realize_inf
#print axioms FirstOrder.Language.BoundedFormula.realize_sup
#print axioms FirstOrder.Language.BoundedFormula.realize_not
