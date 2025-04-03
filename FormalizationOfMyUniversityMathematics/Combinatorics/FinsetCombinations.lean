import Mathlib

abbrev Combinations (α : Type) [Fintype α] (r : ℕ) : Finset (Finset α) := {s : Finset α | s.card = r}
abbrev nCr (n r : ℕ) := (Combinations (Fin n) r).card

theorem Combinations_card_iff {α : Type} [Fintype α] {r : ℕ} {s : Finset α} :  s ∈ Combinations α r ↔ s.card = r := by simp

theorem Combinations_subtype  {α : Type} [Fintype α] [DecidableEq α] {r : ℕ} {s t : Finset α} : (Finset.subtype _ s) ∈ (Combinations t r) ↔ (s ∩ t).card = r := by
  rw [Combinations, Finset.mem_filter]
  simp
  have : (Finset.filter (fun x ↦ x ∈ t) s).card = (s ∩ t).card := by congr
  rw [this]

theorem subtype_inclusion_card  {α : Type} [Fintype α] [DecidableEq α] {s t : Finset α} (hst : s ⊆ t): (Finset.subtype (. ∈ t) s).card = s.card := by
  rw [Finset.card_subtype, Finset.filter_mem_eq_inter]
  rw [Finset.inter_eq_left.mpr hst]

def Combinations_congr  (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (r : ℕ) (f : α ≃ β) :
    Combinations α r ≃ Combinations β r := by
  refine f.finsetCongr.subtypeEquiv ?_
  intro s
  rw [Combinations_card_iff, Combinations_card_iff]
  simp

def Combinations_compl (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (rlen : r ≤ Fintype.card α) :
    Combinations α r ≃ Combinations α (Fintype.card α - r) where
  toFun := fun ⟨s,hs⟩ ↦ ⟨sᶜ,by simp at *; rw [Finset.card_compl, hs]⟩
  invFun := fun ⟨s,hs⟩ ↦ ⟨sᶜ,by simp at *; rw [Finset.card_compl, hs, Nat.sub_sub_self rlen]⟩
  left_inv := by intro ⟨s,hs⟩; simp
  right_inv := by intro ⟨s,hs⟩; simp

theorem nCr_symm (n r : ℕ) (rlen : r ≤ n) : nCr n r = nCr n (n-r) := by
  rw [nCr, nCr]
  have := Finset.card_eq_of_equiv (Combinations_compl (Fin n) r (by rw [Fintype.card_fin]; exact rlen))
  rw [Fintype.card_fin] at this
  exact this

theorem nCr_eq_finset_card (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) :
    (Combinations α r).card = nCr (Fintype.card α) r := by
  rw [nCr]
  have : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have : Combinations α r ≃ Combinations (Fin (Fintype.card α)) r := by
    exact Combinations_congr _ _ r this
  exact Finset.card_eq_of_equiv this

#check Finset.card_eq_of_equiv_fintype
theorem nCr_eq_fintype_card (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) :
    Fintype.card (Combinations α r) = nCr (Fintype.card α) r := by
  convert nCr_eq_finset_card _ _
  simp
  assumption

#check Finset.powersetCard_one
#check Finset.card_eq_one

noncomputable
def n_choose_1_equiv_fin_n (n : ℕ) :
    {s : Finset (Fin n) | s.card = 1} ≃ Fin n where
  toFun := by
    intro ⟨s,hs⟩
    rcases Finset.card_eq_one.mp hs with h
    exact h.choose
  invFun := fun a ↦ ⟨{a}, Finset.card_singleton a⟩
  left_inv := by
    intro ⟨s, hs⟩
    simp
    rcases Finset.card_eq_one.mp hs with h
    have := h.choose_spec
    symm
    exact this
  right_inv := by
    intro a
    simp

theorem nCr_one (n : ℕ) :
    nCr n 1 = n := by
  rw [nCr]
  nth_rw 4 [← Fintype.card_fin n]
  apply Finset.card_eq_of_equiv_fintype
  simp only [Combinations_card_iff]
  exact n_choose_1_equiv_fin_n n

-- theorem nCr_one (n : ℕ) :
--     nCr n 1 = n := by
--   simp [nCr]

-- #check Finset.product
-- #check Prod
-- #check Sum
-- #check Sum.inr
-- #check Finset.sdiff_eq_filter
-- #check Finset.erase
-- #check Finset.card_erase_eq_ite
-- #check Finset.compl_empty
-- #check Sum.elim
-- #check Finset.insert_compl_insert
-- #check Finset.subtype_map
-- #check Finset.inter_filter
-- #check Sum.forall
-- #check Sum.forall

def pascal (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (x : α) :
    Combinations α (r + 1) ≃ Combinations ({x}ᶜ : Finset α) r ⊕ Combinations ({x}ᶜ : Finset α) (r + 1) where
  toFun := by
    refine fun ⟨s,hs⟩ ↦ if h : x ∈ s then Sum.inl ?_ else Sum.inr ?_
    repeat
      use Finset.subtype _ (s.erase x)
      rw [Combinations_subtype]
      rw [Combinations_card_iff] at hs
      rw [Finset.inter_eq_left.mpr (by simp)]
      rw [Finset.card_erase_eq_ite]
      simp [h, hs]
  invFun := by
    refine Sum.elim (fun ⟨s,hs⟩ ↦ ?_) (fun ⟨s,hs⟩ ↦ ?_)
    . use insert x (Finset.map (Function.Embedding.subtype _ : ({x}ᶜ : Finset α) ↪ α) s)
      simp_rw [Combinations_card_iff] at *
      simp [hs]
    . use Finset.map (Function.Embedding.subtype _ : ({x}ᶜ : Finset α) ↪ α) s
      simp_rw [Combinations_card_iff] at *
      simp [hs]
  left_inv := by
    intro ⟨s, hs⟩
    by_cases h : x ∈ s
    . simp [h]
      rw [Finset.filter_ne', Finset.erase_idem, Finset.insert_erase h]
    . simp [h, Finset.filter_eq_self]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse, Sum.forall]
    constructor
    . intro ⟨s, hs⟩
      simp
      ext y
      rw [Finset.mem_subtype]
      rw [← Finset.mem_map' (Function.Embedding.subtype (. ∈ ({x}ᶜ : Finset α)))]
      rfl
    . intro ⟨s, hs⟩
      simp
      ext y
      rw [Finset.mem_subtype]
      rw [← Finset.mem_map' (Function.Embedding.subtype (. ∈ ({x}ᶜ : Finset α)))]
      rfl

-- #check Equiv.sumCongr

def Combinations_pascal_rule' (n r : ℕ) : Combinations (Fin (n + 1)) (r + 1) ≃ Combinations (Fin n) r ⊕ Combinations (Fin n) (r + 1) :=
  let zero : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let s : Finset (Fin (n + 1)) := {zero}ᶜ
  let p := pascal (Fin (n + 1)) r zero
  have s_card : s.card = n := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton, Nat.add_sub_cancel]
  let f : s ≃ Fin n := (s.orderIsoOfFin s_card).symm.toEquiv
  let g : Combinations s r ≃ Combinations (Fin n) r := Combinations_congr _ _ _ f
  let h : Combinations s (r + 1) ≃ Combinations (Fin n) (r + 1) := Combinations_congr _ _ _ f
  let φ : Combinations (Fin (n + 1)) (r + 1) ≃ Combinations (Fin n) r ⊕ Combinations (Fin n) (r + 1) :=
    p.trans (Equiv.sumCongr g h)
  φ

theorem pascal_rule' (n r : ℕ) : nCr (n + 1) (r + 1) = nCr n r + nCr n (r + 1) := by
  let φ := Combinations_pascal_rule' n r
  repeat rw [nCr, ← Nat.card_eq_finsetCard]
  rw [← Nat.card_sum]
  rw [Nat.card_eq_of_bijective]
  use φ
  exact φ.bijective

-- #eval Combinations (Fin (4 + 1)) (2 + 1)
-- #eval (Combinations (Fin (4 + 1)) (2 + 1)).attach
-- #eval (Combinations_pascal_rule' 4 2) ⟨{0, 1, 3}, by rw [Combinations_card_iff]; simp⟩
-- #eval Finset.map (Combinations_pascal_rule' 4 2).toEmbedding (Combinations (Fin (4 + 1)) (2 + 1)).attach

-- #check Sum.forall
-- #check Sigma.forall
-- #check Sigma

def choose_leader_toFun {α : Type} [Fintype α] [DecidableEq α] {k : ℕ} :
    (t : Combinations α (k + 1)) × Combinations t 1 → (b : Combinations α 1) × Combinations (bᶜ : Finset α) k := by
  intro ⟨⟨t,ht⟩,⟨a,ha⟩⟩
  let inclusion_t : Finset t → Finset α := Finset.map (Function.Embedding.subtype (. ∈ t))
  let b : Finset α :=  inclusion_t a
  have : b.card = 1 := by
    rw [Finset.card_map, Combinations_card_iff.mp ha]
  let restriction_b_compl : Finset α → Finset (bᶜ : Finset α) := Finset.subtype (. ∈ bᶜ)
  let s : Finset (bᶜ : Finset α) := restriction_b_compl (t \ b)
  have : s.card = k := by
    rw [subtype_inclusion_card]
    . rw [Finset.card_sdiff, Combinations_card_iff.mp ht, ‹b.card = 1›, Nat.add_sub_cancel]
      intro x
      apply Finset.property_of_mem_map_subtype
    . rw [Finset.compl_eq_univ_sdiff]
      apply Finset.sdiff_subset_sdiff
      apply Finset.subset_univ
      rfl
  exact ⟨⟨b, Combinations_card_iff.mpr ‹b.card = 1›⟩, ⟨s, Combinations_card_iff.mpr ‹s.card = k›⟩⟩

def choose_leader_invFun {α : Type} [Fintype α] [DecidableEq α] {k : ℕ} :
    (b : Combinations α 1) × Combinations (bᶜ : Finset α) k → (t : Combinations α (k + 1)) × Combinations t 1 := by
  intro ⟨⟨b,hb⟩,⟨s,hs⟩⟩
  let inclusion_b_compl : Finset (bᶜ : Finset α) → Finset α := Finset.map (Function.Embedding.subtype (. ∈ bᶜ))
  have : Disjoint b (inclusion_b_compl s) := by
    have : inclusion_b_compl s ⊆ bᶜ := by apply Finset.property_of_mem_map_subtype
    rw [← le_compl_iff_disjoint_left]
    exact this
  let t : Finset α := b ∪ inclusion_b_compl s
  have : t.card = k + 1 := by
    rw [Finset.card_union_of_disjoint (by assumption), Finset.card_map,
        Combinations_card_iff.mp hb, Combinations_card_iff.mp hs, add_comm]
  let restriction_t : Finset α → Finset t := Finset.subtype (. ∈ t)
  let a := restriction_t b
  have : a.card = 1 := by
    rw [subtype_inclusion_card, Combinations_card_iff.mp hb]
    simp [t]
  exact ⟨⟨t, Combinations_card_iff.mpr ‹t.card = k + 1›⟩, ⟨a, Combinations_card_iff.mpr ‹a.card = 1›⟩⟩

#check HEq
#check heq_iff_eq
#check rec_heq_iff_heq
#check rec_heq_iff_heq
#check Subtype.heq_iff_coe_eq
#check cast_eq_iff_heq
#check Subtype.heq_iff_coe_heq
#check HEq
def choose_leader_left_inv {α : Type} [Fintype α] [DecidableEq α] {k : ℕ} :
    Function.LeftInverse (@choose_leader_invFun α _ _ k) choose_leader_toFun := by
  intro ta
  set bs := choose_leader_toFun ta
  set t'a' := choose_leader_invFun bs
  let t := ta.1.1; let ht := ta.1.2;
  let a := ta.2.1; let ha := ta.2.2;
  let b := bs.1.1; let hb := bs.1.2;
  let s := bs.2.1; let hs := bs.2.2;
  let t' := t'a'.1.1; let ht' := t'a'.1.2;
  let a' := t'a'.2.1; let ha' := t'a'.2.2;
  let inclusion_t : Finset t → Finset α := Finset.map (Function.Embedding.subtype (. ∈ t))
  let restriction_t : Finset α → Finset t := Finset.subtype (. ∈ t)
  -- let inclusion_t' : Finset t' → Finset α := Finset.map (Function.Embedding.subtype (. ∈ t'))
  let restriction_t' : Finset α → Finset t' := Finset.subtype (. ∈ t')
  let inclusion_b_compl : Finset (bᶜ : Finset α) → Finset α := Finset.map (Function.Embedding.subtype (. ∈ bᶜ))
  let restriction_b_compl : Finset α → Finset (bᶜ : Finset α) := Finset.subtype (. ∈ bᶜ)

  -- have : b = inclusion_t a := rfl
  -- have : s = restriction_b_compl (t \ b) := rfl
  -- have : t' = b ∪ inclusion_b_compl s := rfl
  -- have : a' = restriction_t' b := rfl

  have : t' = t := by
    change (b ∪ inclusion_b_compl (restriction_b_compl (t \ b))) = t
    simp [inclusion_b_compl, restriction_b_compl]
    rw [← Finset.sdiff_eq_filter, Finset.sdiff_idem, Finset.union_sdiff_of_subset]
    change (inclusion_t a) ⊆ t
    apply Finset.map_subtype_subset
  have : Finset t' = Finset t := by rw [‹t' = t›]
  have : t'a'.1 = ta.1 := by
    rw [Subtype.ext_iff]
    exact ‹t' = t›

  have : restriction_t (inclusion_t a) = a := by
    have : inclusion_t (restriction_t (inclusion_t a)) = inclusion_t a := by
      simp [inclusion_t, restriction_t]
      rw [Finset.filter_eq_self]
      apply Finset.property_of_mem_map_subtype
    rwa [Finset.map_inj] at this
  have : HEq (restriction_t' b) (restriction_t b) := by
    dsimp [restriction_t', restriction_t]
    rw [‹t' = t›]
  have : HEq a' a := by
    convert this
    symm
    assumption
  have : HEq (Membership.mem (Combinations t' 1)) (Membership.mem (Combinations t 1)) := by
    rw [‹t' = t›]
  have : HEq t'a'.2 ta.2 := by
    rw [Subtype.heq_iff_coe_heq ‹Finset t' = Finset t›]
    . exact ‹HEq a' a›
    . exact ‹HEq (Membership.mem (Combinations t' 1)) (Membership.mem (Combinations t 1))›

  rw [Sigma.ext_iff]
  constructor
  . exact ‹t'a'.fst = ta.fst›
  . exact ‹HEq t'a'.2 ta.2›

def choose_leader_right_inv {α : Type} [Fintype α] [DecidableEq α] {k : ℕ} :
    Function.RightInverse (@choose_leader_invFun α _ _ k) choose_leader_toFun := by
  rw [Function.RightInverse]
  intro bs
  set ta := choose_leader_invFun bs
  set b's' := choose_leader_toFun ta
  let t := ta.1.1; let ht := ta.1.2;
  let a := ta.2.1; let ha := ta.2.2;
  let b := bs.1.1; let hb := bs.1.2;
  let s := bs.2.1; let hs := bs.2.2;
  let b' := b's'.1.1; let hb' := b's'.1.2;
  let s' := b's'.2.1; let hs' := b's'.2.2;
  let inclusion_t : Finset t → Finset α := Finset.map (Function.Embedding.subtype (. ∈ t))
  let restriction_t : Finset α → Finset t := Finset.subtype (. ∈ t)
  -- let inclusion_t' : Finset t' → Finset α := Finset.map (Function.Embedding.subtype (. ∈ t'))
  -- let restriction_t' : Finset α → Finset t' := Finset.subtype (. ∈ t')
  let inclusion_b_compl : Finset (bᶜ : Finset α) → Finset α := Finset.map (Function.Embedding.subtype (. ∈ bᶜ))
  let restriction_b_compl : Finset α → Finset (bᶜ : Finset α) := Finset.subtype (. ∈ bᶜ)
  let inclusion_b'_compl : Finset (b'ᶜ : Finset α) → Finset α := Finset.map (Function.Embedding.subtype (. ∈ b'ᶜ))
  let restriction_b'_compl : Finset α → Finset (b'ᶜ : Finset α) := Finset.subtype (. ∈ b'ᶜ)

  -- have : t = b ∪ inclusion_b_compl s := rfl
  -- have : a = restriction_t b := rfl
  -- have : b' = inclusion_t a := rfl
  -- have : s' = restriction_b'_compl (t \ b') := rfl

  have : b ⊆ t := by apply Finset.subset_union_left
  have : Disjoint b (inclusion_b_compl s) := by
    have : inclusion_b_compl s ⊆ bᶜ := by apply Finset.property_of_mem_map_subtype
    rw [← le_compl_iff_disjoint_left]
    exact this
  have : b' = b := by
    change inclusion_t (restriction_t b) = b
    simp [restriction_t, inclusion_t]
    rw [Finset.filter_eq_self]
    exact ‹b ⊆ t›

  have : restriction_b_compl (inclusion_b_compl s) = s := by
    have : inclusion_b_compl (restriction_b_compl (inclusion_b_compl s)) = inclusion_b_compl s := by
      simp [restriction_b_compl, inclusion_b_compl]
      rw [Finset.filter_eq_self]
      simp_rw [← Finset.mem_compl]
      apply Finset.property_of_mem_map_subtype
    rwa [Finset.map_inj] at this
  have : restriction_b_compl (t \ b) = s := by
    change restriction_b_compl ((b ∪ inclusion_b_compl s) \ b) = s
    convert this
    rw [Finset.union_sdiff_cancel_left]
    exact ‹Disjoint b (inclusion_b_compl s)›
  have : HEq (restriction_b'_compl (t \ b')) (restriction_b_compl (t \ b)) := by
    dsimp [restriction_b'_compl]
    rw [‹b' = b›]
  have : HEq s' s := by
    convert this
    symm
    exact ‹restriction_b_compl (t \ b) = s›

  have : Finset (b'ᶜ : Finset α) = Finset (bᶜ  : Finset α) := by
    rw [‹b' = b›]
  have : HEq (Membership.mem (Combinations (b'ᶜ : Finset α) k)) (Membership.mem (Combinations (bᶜ : Finset α) k)) := by
    rw [‹b' = b›]


  have : HEq b's'.2 bs.2 := by
    rw [Subtype.heq_iff_coe_heq ‹Finset (b'ᶜ : Finset α) = Finset (bᶜ  : Finset α)›]
    . exact ‹HEq s' s›
    . exact ‹HEq (Membership.mem (Combinations (b'ᶜ : Finset α) k)) (Membership.mem (Combinations (bᶜ : Finset α) k))›



  rw [Sigma.ext_iff]
  constructor
  . rw [Subtype.ext_iff]
    exact ‹b' = b›
  . exact ‹HEq b's'.2 bs.2›

def choose_leader {α : Type} [Fintype α] [DecidableEq α] {k : ℕ} :
    (t : Combinations α (k + 1)) × Combinations t 1 ≃ (l : Combinations α 1) × Combinations (lᶜ : Finset α) k where
  toFun := choose_leader_toFun
  invFun := choose_leader_invFun
  left_inv := choose_leader_left_inv
  right_inv := choose_leader_right_inv

#check Fintype.card_sigma

def nCr_choose_leader (n k : ℕ) :
    nCr (n + 1) (k + 1) * (k + 1) = (n + 1) * nCr n k := by
  have := @choose_leader (Fin (n + 1)) _ _ k
  have := Fintype.card_congr this
  rw [Fintype.card_sigma, Fintype.card_sigma] at this
  simp_rw [nCr_eq_fintype_card] at this
  rw [@Finset.sum_const_nat _ _ (k + 1)] at this
  rw [@Finset.sum_const_nat _ _ (nCr n k)] at this
  simp_rw [Finset.card_univ, nCr_eq_fintype_card, Fintype.card_fin] at this

  change (Combinations (Fin (n + 1)) (k + 1)).card * (k + 1) = (Combinations (Fin (n + 1)) (1)).card * (nCr n k) at this
  rw [← nCr,← nCr,nCr_one (n + 1)] at this
  exact this

  intro ⟨x, hx⟩ _
  congr
  rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  rw [Combinations_card_iff] at hx
  rw [hx, Nat.add_sub_cancel]

  intro ⟨x, hx⟩ _
  convert nCr_one (k + 1)
  simp [Combinations_card_iff.mp hx]
