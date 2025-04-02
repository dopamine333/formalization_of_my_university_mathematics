
import Mathlib

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
