
-- Definition 14.1 (unfinished)
structure ZF where
  set : Type u
  mem : set → set → Prop
  extensionality : ∀ A B : set, A = B ↔ (∀ x, mem x A ↔ mem x B)
  emptyset : ∃ S, ∀ x, ¬ mem x S
  replacement :
    ∀ (P : set → set → Prop)
      (_ : ∀ x, ∃ y, (P x y ∧ (∀ z, P x z → z = y)))
      (U : set),
    ∃ U', ∀ y, mem y U' ↔ (∃ x, mem x U ∧ P x y)
  powerset :
    ∀ S, ∃ PS, ∀ T, mem T PS ↔ (∀ x, mem x T → mem x S)

-- Proposition 15.1.2
theorem pairing (zf : ZF) (a b : zf.set) :
  ∃ S, ∀ x, zf.mem x S ↔ x = a ∨ x = b := by
  -- zero = ∅
  let ⟨zero, hzero⟩ := zf.emptyset
  -- one = {∅}
  let ⟨one, hone⟩ := zf.powerset zero
  have zero_mem_one : zf.mem zero one := by
    rw [hone]
    intro x hxzero
    exact (hzero x hxzero).elim
  -- two = {∅, {∅}}
  let ⟨two, htwo⟩ := zf.powerset one
  have zero_mem_two : zf.mem zero two := by
    rw [htwo]
    intro x hxzero
    exact (hzero x hxzero).elim
  have one_mem_two : zf.mem one two := by
    rw [htwo]
    intro x hxzero
    exact hxzero
  have zero_ne_one : zero ≠ one := by
    intro h
    rw [zf.extensionality] at h
    have := h zero
    exact hzero zero (this.mpr zero_mem_one)
  -- ∀ x, ∃! y, P x y
  -- → {y | ∃ x ∈ U, P(x, y)} is a set
  -- x will replace by zero, one, y will replace by a, b
  let P x y := (x = zero ∧ y = a) ∨ (x ≠ zero ∧ y = b)
  have hP : ∀ x, ∃ y, (P x y ∧ (∀ z, P x z → z = y)) := by
    intro x
    by_cases h : x = zero
    . refine ⟨a, ?_, ?_⟩ -- choose y := a
      . unfold P -- y satisfy P(x, y)
        left
        exact ⟨h, rfl⟩
      . intro z hz -- y is the unique one that satisfies P(x,y)
        unfold P at hz
        apply hz.elim
        . exact fun h' ↦ h'.2
        . exact fun h' ↦ (h'.1 h).elim
    . refine ⟨b, ?_, ?_⟩ -- choose y := b
      . unfold P -- y satisfy P(x, y)
        right
        exact ⟨h, rfl⟩
      . intro z hz  -- y is the unique one that satisfies P(x,y)
        unfold P at hz
        apply hz.elim
        . exact fun h' ↦ (h h'.1).elim
        . exact fun h' ↦ h'.2

  let ⟨S, hS⟩ := zf.replacement P hP two
  refine ⟨S, ?_⟩
  intro y
  constructor
  . intro hyS
    let ⟨x, hxtwo, pxy⟩ := (hS y).mp hyS
    apply pxy.elim
    . exact fun h ↦ Or.inl h.2
    . exact fun h ↦ Or.inr h.2
  . refine fun h ↦ h.elim (fun h ↦ ?_) (fun h ↦ ?_)
    . rw [hS]
      refine ⟨zero, zero_mem_two, ?_⟩
      left
      exact ⟨rfl, h⟩
    . rw [hS]
      refine ⟨one, one_mem_two, ?_⟩
      right
      exact ⟨Ne.symm zero_ne_one, h⟩
