import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace ProofSystem

inductive Formula : Type
  | falsum : Formula
  | imp : Formula → Formula → Formula

namespace Formula

def not (A : Formula) : Formula := A.imp falsum
def truth : Formula := falsum.not
def or (A B : Formula) : Formula := A.not.imp B
def and (A B : Formula) : Formula := (A.imp B.not).not

end Formula

inductive Proof : Set (Formula) → Formula → Type
  | axm Γ A : A ∈ Γ → Proof Γ A
  | impI Γ A B : Proof (insert A Γ) B → Proof Γ (A.imp B)
  | impE Γ A B : Proof Γ (A.imp B) → Proof Γ A → Proof Γ B
  | not_not Γ A : Proof Γ A.not.not → Proof Γ A

namespace Proof

#check rfl
def refl {Γ} {A : Formula} : Proof Γ (A.imp A) := by
  apply impI
  apply axm
  apply Set.mem_insert

#check trivial
def truth {Γ} : Proof Γ Formula.truth := by
  exact refl

def weakening {Γ Γ' A} (h : Γ ⊆ Γ'): Proof Γ A → Proof Γ' A
  | axm Γ A h' => by
    have : A ∈ Γ' := h h'
    apply axm
    exact this
  | impI Γ A B p => by
    let p' : Proof (insert A Γ') B := by
      have h' : insert A Γ ⊆ insert A Γ' := by
        apply Set.insert_subset_insert h
      apply weakening h'
      exact p
    apply impI
    exact p'
  | impE Γ A B p1 p2 => by
    let p1' : Proof Γ' (A.imp B) := weakening h p1
    let p2' : Proof Γ' A := weakening h p2
    apply impE
    exact p1'
    exact p2'
  | not_not Γ A p => not_not Γ' A (weakening h p)

-- def weakening' {Γ Γ' A} (h : Γ ⊆ Γ'): Proof Γ A → Proof Γ' A
--   | axm Γ A h' => axm _ _ (h h')
--   | impI Γ A B p => impI _ _ _ (p.weakening (Set.insert_subset_insert h))
--   | impE Γ A B p1 p2 => impE _ _ _ (p1.weakening h) (p2.weakening h)
--   | not_not Γ A p => not_not Γ' A (weakening h p)

def weakening1 {Γ A B} : Proof Γ B → Proof (insert A Γ) B := by
  intro h
  apply weakening _ h
  apply Set.subset_insert

def weakening2 {Γ A B C} : Proof (insert A Γ) C → Proof (insert A (insert B Γ)) C := by
  intro h
  apply weakening _ h
  apply Set.insert_subset_insert
  apply Set.subset_insert

def axm1 {Γ A} : Proof (insert A Γ) A := by
  apply axm
  apply Set.mem_insert

def axm2 {Γ A B} : Proof (insert A (insert B Γ)) B := by
  apply axm
  apply Set.mem_insert_of_mem
  apply Set.mem_insert

#check False.elim
def exfalso {Γ A} : Proof Γ .falsum → Proof Γ A := by
  intro h
  apply not_not
  apply impI
  apply weakening1 h

#check Or.inl
def orI1 {Γ A B} : Proof Γ A → Proof Γ (A.or B) := by
  intro p
  apply impI
  apply exfalso
  let Γ' := insert A.not Γ
  have h : Γ ⊆ Γ' := by apply Set.subset_insert
  let p1 : Proof Γ' A := by
    apply weakening h p
  let p2 : Proof Γ' A.not := by
    apply axm
    apply Set.mem_insert
  exact impE _ _ _ p2 p1

#check Or.inr
def orI2 {Γ A B} : Proof Γ B → Proof Γ (.or A B) := by
  intro p
  apply impI
  apply weakening _ p
  apply Set.subset_insert

#check Or.elim
def orE {Γ A B C} : Proof Γ (.or A B) → Proof Γ (A.imp C) → Proof Γ (B.imp C) → Proof Γ C := by
  intro p pA pB

  apply not_not
  apply impI
  have p1 : Proof (insert C.not Γ) C.not := axm _ _ (Set.mem_insert _ _)
  have p2 : Proof (insert C.not Γ) (B.imp C) := weakening1 pB
  have p3 : Proof (insert C.not Γ) (A.or B) := weakening1 p
  apply impE _ _ _ p1 (impE _ _ _ p2 (impE _ _ _ p3 _))

  apply impI
  apply impE _ _ _ (p1.weakening1) _
  apply impE _ _ _ (pA.weakening ?_) _
  . trans insert C.not Γ <;> apply Set.subset_insert
  apply axm
  apply Set.mem_insert

-- def and (A B : Formula) : Formula := (A.imp B.not).not
-- (A → (B → ⊥)) → ⊥

#check And.intro
def andI {Γ A B} : Proof Γ A → Proof Γ B → Proof Γ (A.and B) := by
  intro pA pB
  apply impI

  have p1 : Proof (insert (A.imp B.not) Γ) A := pA.weakening1
  have p2 : Proof (insert (A.imp B.not) Γ) (A.imp B.not) := axm1
  have p3 : Proof (insert (A.imp B.not) Γ) B.not := impE _ _ _ p2 p1
  have p4 : Proof (insert (A.imp B.not) Γ) B := pB.weakening1
  have p5 : Proof (insert (A.imp B.not) Γ) .falsum := impE _ _ _ p3 p4
  exact p5

/-
(A → (B → ⊥)) → ⊥ ⊢ A
(A → (B → ⊥)) → ⊥ ⊢ (A → ⊥) → ⊥
(A → ⊥) ⊢ (A → (B → ⊥))
-/
#check And.left
def andE1 {Γ A B} : Proof Γ (A.and B) → Proof Γ A := by
  intro p
  apply not_not
  apply impI
  apply impE _ _ _ p.weakening1
  apply impI
  apply exfalso

  have p1 : Proof (insert A (insert A.not Γ)) A := axm1
  have p2 : Proof (insert A (insert A.not Γ)) A.not := axm2
  apply impE _ _ _ p2 p1

/-
(A → (B → ⊥)) → ⊥ ⊢ B
(A → (B → ⊥)) → ⊥ ⊢ (B → ⊥) → ⊥
(B → ⊥) ⊢ (A → (B → ⊥))
-/
#check And.right
def andE2 {Γ A B} : Proof Γ (.and A B) → Proof Γ B := by
  intro p
  apply not_not
  apply impI
  apply impE _ _ _ p.weakening1
  apply impI

  apply axm2

#print axioms andI
end Proof
-- axiom Proof.em
