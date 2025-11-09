import FormalizationOfMyUniversityMathematics.ElemMath.SetTheory.ZFC

open SetTheory

section do_not_need_ZFC

variable {set : Type u} [SetTheory set]
theorem russell_paradox :
  ¬∃ R : set, ∀ x, x ∈ R ↔ x ∉ x := by
  intro ⟨R, hR⟩
  have bad := hR R
  have : R ∉ R := by
    intro h
    have := bad.mp h
    contradiction
  have : R ∈ R := by
    exact bad.mpr this
  contradiction

end do_not_need_ZFC


section lemmas

variable {set : Type u} [ZFC set]

theorem mem_empty_iff (x : set) : x ∈ (∅ : set) ↔ False := by
  simp [not_mem_empty]

theorem ext_mem {A B : set} (h : ∀ x : set, x ∈ A ↔ x ∈ B) : A = B := by
  exact (extensionality _ _).mpr h

theorem product_induction {A B : set} {motive : set → Prop} :
  (∀ a ∈ A, ∀ b ∈ B, motive ((a, b)ˢ)) → (∀ x ∈ A ×ˢ B, motive x) := by
  intro h x hxAB
  rw [mem_product_iff] at hxAB
  obtain ⟨a, ha, b, hb, rfl⟩ := hxAB
  apply h
  assumption'

theorem product_induction_on {A B : set} {motive : set → Prop} {x : set}
  (hxAB : x ∈ A ×ˢ B) :
  (∀ a ∈ A, ∀ b ∈ B, motive ((a, b)ˢ)) → motive x := by
  intro h
  apply product_induction h x hxAB

theorem specification_subset {P : set → Prop} {A : set} :
  specification P A ⊆ A := by
  intro x hx
  rw [mem_specification_iff] at hx
  exact hx.1

theorem ordered_pair_mem_product {a b A B : set}
  (ha : a ∈ A) (hb : b ∈ B) :
  (a, b)ˢ ∈ A ×ˢ B := by
  rw [mem_product_iff]
  exact ⟨a, ha, b, hb, rfl⟩

end lemmas


section coe_set

variable {set : Type u} [ZFC set]

@[coe, reducible] def SetTheory.Elem (s : set) : Type u := {x // x ∈ s}

instance : CoeSort set (Type u) := ⟨Elem⟩

end coe_set


section Function

variable {set : Type u} [ZFC set]

structure Function (domain codomain : set) where
   relation : set
   is_function : is_function domain codomain relation

theorem toFun_spec
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A) :
  toFun hf ha ∈ B ∧ (a, toFun hf ha)ˢ ∈ f := by
  rw [toFun]
  exact (Classical.choose_spec (hf.2 a ha)).1

theorem toFun_unique
  {A B f : set} (hf : is_function A B f) {a : set} (ha : a ∈ A)
  {b : set} (hb : b ∈ B) (habf : (a, b)ˢ ∈ f) : b = toFun hf ha := by
  rw [toFun]
  have := (Classical.choose_spec (hf.2 a ha)).2
  exact this b ⟨hb, habf⟩

namespace Function

variable {A B : set}

noncomputable def apply (f : Function A B) (x : A) : B :=
    ⟨toFun f.is_function x.2, (toFun_spec f.is_function x.2).1⟩

noncomputable instance : CoeFun (Function A B) (fun _ ↦ A → B) where
  coe := Function.apply

attribute [coe] Function.apply

theorem apply_spec (f : Function A B) (x : A) :
  ((x : set), f x)ˢ ∈ f.relation := by
  rw [Function.apply]
  exact (toFun_spec f.is_function x.2).2

theorem apply_unique
  {f : Function A B} {x : A} {b : B}
  (habf : ((x : set), b)ˢ ∈ f.relation) : b = f x := by
  rw [Function.apply, Subtype.ext_iff]
  exact toFun_unique f.is_function x.2 b.2 habf

theorem apply_eq_iff
  {f : Function A B} {x : A} {b : B} :
  f x = b ↔ ((x : set), b)ˢ ∈ f.relation := by
  constructor
  · intro h
    rw [← h]
    exact apply_spec f x
  · intro habf
    symm
    apply apply_unique habf

theorem ext_relation {f g : Function A B}
  (h : f.relation = g.relation) : f = g := by
  cases f; cases g
  simp at *
  exact h

theorem ext_apply {f g : Function A B}
  (h : ∀ x : A, f x = g x) : f = g := by
  apply ext_relation
  apply ext_mem
  intro x
  constructor
  . intro hxf
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_product_iff _ _ _).mp (f.is_function.1 hxf)
    let a : A := ⟨a, ha⟩
    let b : B := ⟨b, hb⟩
    change (a.val, b.val)ˢ ∈ _ at hxf ⊢
    rw [← apply_eq_iff] at hxf ⊢
    exact h a ▸ hxf
  . intro hxg
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_product_iff _ _ _).mp (g.is_function.1 hxg)
    let a : A := ⟨a, ha⟩
    let b : B := ⟨b, hb⟩
    change (a.val, b.val)ˢ ∈ _ at hxg ⊢
    rw [← apply_eq_iff] at hxg ⊢
    exact h a ▸ hxg

noncomputable def define_function (map : A → B) : Function A B where
  relation := specification
    (fun p ↦ ∃ a, ∃ ha : a ∈ A, ∃ b ∈ B, p = (a, b)ˢ ∧ b = map ⟨a, ha⟩) (A ×ˢ B)
  is_function := by
    let rel := specification (fun p ↦ ∃ a, ∃ ha : a ∈ A, ∃ b ∈ B, p = (a, b)ˢ ∧ b = map ⟨a, ha⟩) (A ×ˢ B)
    change _root_.is_function A B rel
    constructor
    . apply specification_subset
    intro a ha
    let a : A := ⟨a, ha⟩
    let b : B := map a
    use b
    dsimp
    constructor
    . refine ⟨b.2, ?_⟩
      change (a.val, b.val)ˢ ∈ rel
      rw [mem_specification_iff]
      refine ⟨ordered_pair_mem_product a.2 b.2, ?_⟩
      use a.val, a.2, b.val, b.2
    . intro y ⟨hyB, hay⟩
      rw [mem_specification_iff] at hay
      obtain ⟨a', ha', b', hb', heq1, heq2⟩ := hay.2
      calc y
        _ = b' := by rw [ordered_pair_inj] at heq1; exact heq1.2
        _ = (map ⟨a', ha'⟩).val := heq2
        _ = (map ⟨a, ha⟩).val := by
          congr
          rw [ordered_pair_inj] at heq1
          exact heq1.1.symm
        _ = b.val := rfl

/-

define succ := { p ∈ nat × nat | ∃ x ∈ nat, ∃ y ∈ nat, p = (x, y) ∧ y = x ∪ {x})
goal : ∀ x ∈ nat, ∃! y ∈ nat, (x, y) ∈ succ

let x ∈ nat.

exist :
  choose x ∪ {x}
  goal : (x, x ∪ {x}) ∈ succ
  choose x, y
  goal : (x, x ∪ {x}) = (x, x ∪ {x}) ∧ x ∪ {x} = x ∪ {x}
  by refl
  done

unique :
  let y, z ∈ nat, (x, y) ∈ succ, (x, z) ∈ succ
  goal : y = z
  since (x, y) ∈ succ, obtain a ∈ nat, b ∈ nat, (x, y) = (a, b) ∧ b = a ∪ {a}
  since (x, z) ∈ succ, obtain c ∈ nat, d ∈ nat, (x, z) = (c, d) ∧ d = c ∪ {c}
  by ordered_pair_inj, x = a, y = b, x = c, z = d
  thus
    y = b = a ∪ {a} = x ∪ {x} = c ∪ {c} = d = z
  done


兩個集合 A, B
給我一個 "map" 我還不知道這 map 到底是什麼
但我希望對於 a ∈ A, 我可以寫 map a 是一個集合 並且 map a ∈ B
對於每個這樣的 map 我的能造一個集合 f 使得
f 是 A, B 上的函數
並且 ∀ a ∈ A, (a, map a) ∈ f

-/
