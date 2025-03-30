import Mathlib
import Paperproof
#check LinearOrder
#check le_total

#check Finite
#check finite_iff_exists_equiv_fin
#check Finite.exists_equiv_fin

#check OrderHom
#check OrderEmbedding
#check OrderIso

#check Monotone
#check StrictMono

#check Fin
#synth LinearOrder (Fin 42)
#synth Finite (Fin 42)

#check Bot
#synth Bot (Fin 42)
#check (⊥ : Fin 42)
#check IsBot
#check Subsingleton.isBot

#check Nonempty
#check Nat.card
#check Nat.card_eq_of_equiv_fin
#check Fin.equiv_iff_eq

#check compl
#check Set.ncard_diff
example (s t : Set ℕ) [hs : Finite s] [Finite t] (hst : s ⊆ t) : (t \ s).ncard = t.ncard - s.ncard := by
    apply Set.ncard_diff hst
#check Set.ncard_diff_singleton_of_mem
#check Set.ncard_add_ncard_compl
#check Set.ncard_singleton
#check Set.ncard_pos
#check Set.eq_univ_iff_ncard


example (s : Set ℕ) [Finite s] : s.ncard = Nat.card s := rfl
example {α : Type} [Finite α] : (Set.univ : Set α).ncard = Nat.card α := by
  exact Set.ncard_univ α

#check Set.Nonempty
#check Set.nonempty_of_ncard_ne_zero
#check Set.Nonempty.of_subtype
#check Set.Nonempty.to_subtype

#check Finite.equivFinOfCardEq
#check Finite.equivFin
#check Finite.exists_max

#check Set.ncard
#check Set.Nat.card_coe_set_eq

#check Subtype.instLinearOrder
#check Subtype.mono_coe

example {α : Type} [LinearOrder α] (s : Set α) (a b : s) : (Subtype.instLinearOrder s).le a b ↔ (a : α) ≤ (b : α) := by rfl

namespace FiniteLinearOrder

variable {α : Type} [Finite α] [LinearOrder α]

example (s : Set α) : Finite s := by infer_instance
example (s : Set α) : LinearOrder s := by infer_instance


-- set_option pp.all true in
theorem has_bot {α : Type} [Finite α] [LinearOrder α] [Nonempty α] :
    ∃ m : α, IsBot m := by
-- -- revert α
  have ⟨n,⟨f⟩⟩ := Finite.exists_equiv_fin α
  have npos : n ≥ 1 := by
    by_contra!
    simp at this
    rw [this] at f
    have : Nat.card α = 0 := Nat.card_eq_of_equiv_fin f
    have : Nat.card α > 0 := Nat.card_pos_iff.mpr ⟨‹Nonempty α›, ‹Finite α›⟩
    linarith
  revert α
  induction' n, npos using Nat.le_induction with n npos ih
  . intros α _ _ _ f
    have : Nat.card α = 1 := Nat.card_eq_of_equiv_fin f
    have ⟨x,hx⟩ := Nat.card_eq_one_iff_exists.mp this
    use x
    intro y
    exact (hx y).ge
  . intros α _ _ _ f
    have x : α := Classical.ofNonempty
    set s : Set α := {x}ᶜ with s_def
    have : Finite s := by infer_instance
    let _ : LinearOrder s := Subtype.instLinearOrder s
    have : Nonempty s := by
      have := Set.ncard_add_ncard_compl {x}
      rw [Nat.card_eq_of_equiv_fin f, Set.ncard_singleton] at this
      rw [add_comm, Nat.succ_inj] at this
      rw [← s_def] at this
      have : s.ncard ≠ 0 := by linarith
      apply Set.Nonempty.to_subtype
      apply Set.nonempty_of_ncard_ne_zero this
    have : s ≃ Fin n := by
      have : Nat.card α = n + 1 := by
        exact Nat.card_eq_of_equiv_fin f
      have : Nat.card s = n := by
        rw [s_def, Set.compl_eq_univ_diff, Set.Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem]
        rw [Set.ncard_univ, this, Nat.add_sub_cancel]
        trivial
      exact Finite.equivFinOfCardEq this
    have ⟨m, botm⟩ := @ih s _ _ _ this
    rcases le_total (m : α) x with hx | hx
    . use m
      intro a
      by_cases ha : a ∈ s
      . exact botm ⟨a,ha⟩
      . have : a = x := by
          contrapose ha
          simp [s_def, ha]
        rw [this]
        exact hx
    . use x
      intro a
      by_cases ha : a ∈ s
      . exact hx.trans (botm ⟨a,ha⟩)
      . have : a = x := by
          contrapose ha
          simp [s_def, ha]
        rw [this]


end FiniteLinearOrder

#check Finset.orderIsoOfFin
#eval List.map (({2,3,5} : Finset ℕ).orderIsoOfFin (by norm_num : ({2,3,5}: Finset ℕ).card = 3)) [0,2,0,2,1]

abbrev Combinations (α : Type) [Fintype α] (r : ℕ) : Finset (Finset α) := {s : Finset α | s.card = r}
abbrev nCr (n r : ℕ) := (Combinations (Fin n) r).card

theorem Combinations_card_iff {α : Type} [Fintype α] {r : ℕ} {s : Finset α} :  s ∈ Combinations α r ↔ s.card = r := by simp

theorem Combinations_subtype  {α : Type} [Fintype α] [DecidableEq α] {r : ℕ} {s t : Finset α} : (Finset.subtype _ s) ∈ (Combinations t r) ↔ (s ∩ t).card = r := by
  rw [Combinations, Finset.mem_filter]
  simp
  have : (Finset.filter (fun x ↦ x ∈ t) s).card = (s ∩ t).card := by congr
  rw [this]

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

#check Finset.product
#check Prod
#check Sum
#check Sum.inr
#check Finset.sdiff_eq_filter
#check Finset.erase
#check Finset.card_erase_eq_ite
#check Finset.compl_empty
#check Sum.elim
#check Finset.insert_compl_insert
#check Finset.subtype_map
#check Finset.inter_filter
#check Sum.forall
#check Sum.forall

def pascal (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (x : α) :
    Combinations α (r + 1) ≃ Combinations ({x}ᶜ : Finset α) r ⊕ Combinations ({x}ᶜ : Finset α) (r + 1) :=
  let n := Fintype.card α
  {
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

  }

#check Equiv.sumCongr

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

#eval Combinations (Fin (4 + 1)) (2 + 1)
#eval (Combinations (Fin (4 + 1)) (2 + 1)).attach
#eval (Combinations_pascal_rule' 4 2) ⟨{0, 1, 3}, by rw [Combinations_card_iff]; simp⟩
#eval Finset.map (Combinations_pascal_rule' 4 2).toEmbedding (Combinations (Fin (4 + 1)) (2 + 1)).attach
