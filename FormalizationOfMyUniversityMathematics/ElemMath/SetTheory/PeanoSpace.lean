import FormalizationOfMyUniversityMathematics.ElemMath.SetTheory.Basic

open SetTheory

variable {set : Type u} [ZFC set]

class PeanoSpace (nat : set) where
  zero : nat
  succ : Function nat nat
  zero_not_succ : ∀ n : nat, succ n ≠ zero
  succ_inj : ∀ {m n : nat}, succ m = succ n → m = n
  induction : ∀ (P : set → Prop),
    P zero →
    (∀ n : nat, P n → P (succ n)) →
    ∀ n : nat, P n

noncomputable def nat : set := specification (fun x ↦ ∀ S : set, (∅ ∈ S ∧ ∀ x ∈ S, x ∪ {x} ∈ S) → x ∈ S) infinity

def nat.zero : (nat : set) := ⟨∅, by
  rw [nat, mem_specification_iff]
  constructor
  . exact empty_mem_infinity
  intro S ⟨hzero, hsucc⟩
  exact hzero
⟩

def nat.succ : Function (nat : set) nat where
  relation := specification (
    fun p ↦ ∃ x ∈ nat, ∃ y ∈ nat, p = (x, y)ˢ ∧ y = x ∪ {x}
  ) (nat ×ˢ nat)
  is_function := by
    apply function_relation_is_function
    intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_product_iff.mp ha
    use n ∪ {n}
    constructor
    . rw [mem_specification_iff]
      intro S ⟨hzero, hsucc⟩
      exact hsucc n hn
    . use n
      constructor
      . exact hn
      . rfl


x = f(x)
