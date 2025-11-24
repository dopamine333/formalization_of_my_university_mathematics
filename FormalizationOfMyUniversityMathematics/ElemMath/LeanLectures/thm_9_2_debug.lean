import Mathlib
open Metric Set Classical

namespace thm_9_2_debug

-- strictly increasing predicate
def StrictlyIncreasing (v : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → v i < v j

-- compact via finite subcover
def compact_via_finite_subcover
  {X : Type} [MetricSpace X] (S : Set X) : Prop :=
  ∀ {ι : Type} (U : ι → Set X),
    (∀ i, IsOpen (U i)) →
    S ⊆ ⋃ i, U i →
    ∃ t : Finset ι, S ⊆ ⋃ i ∈ t, U i

-- sequentially compact
def SequentiallyCompact_def_9_2_b {X : Type} [MetricSpace X] (S : Set X) : Prop :=
  ∀ (u : ℕ → X), (∀ n, u n ∈ S) →
    ∃ p ∈ S, ∃ s : ℕ → ℕ,
      (StrictlyIncreasing s) ∧ (∀ ε > 0, ∃ N, ∀ n ≥ N, dist ((u ∘ s) n) p < ε)

theorem IsCompact.sequentially_compact_by_contra2 {X : Type} [MetricSpace X] {S : Set X}
  (hS : compact_via_finite_subcover S) :
  SequentiallyCompact_def_9_2_b S := by
  by_contra h
  -- negate sequential compactness
  simp only [SequentiallyCompact_def_9_2_b] at h
  push_neg at h
  obtain ⟨u, huS, hbad⟩ := h
  -- hbad: ∀ p ∈ S, ∀ s strictly increasing, ∃ ε > 0, ∀ N, ∃ n ≥ N, dist (u (s n)) p ≥ ε

  -- use the identity subsequence s := id
  have hball_finite : ∀ x ∈ S, ∃ ε > 0, ∃ N, ∀ n ≥ N, u n ∉ ball x ε := by
    intro x hxS
    by_contra!

    -- construct a seq δ, s.t.
    -- 1. δ n → 0 as n → ∞
    -- 2. ∀ n, δ n > 0
    let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have δ_pos : ∀ n, δ n > 0 := by
      intro n
      simp [δ, Nat.cast_add_one_pos]
    have δ_tendsto : ∀ ε > 0, ∃ N, ∀ n ≥ N, δ n < ε := by
      intro ε hε
      let N := Nat.ceil (1 / ε)
      have hN : δ N < ε := by
        calc δ N
          _ = 1 / (N + 1) := rfl
          _ < ε := by
            rw [one_div_lt]
            linarith [Nat.le_ceil (1 / ε), Nat.lt_succ_self]
            . linarith
            . linarith
      use N
      intro n hn
      calc δ n
        _ ≤ δ N := by
          unfold δ
          apply one_div_le_one_div_of_le
          . linarith [Nat.le_ceil (1 / ε), Nat.lt_succ_self]
          . simp [hn]
        _ < ε := hN

    -- inductively define a subseq index s s.t. u (s n) → x as n → ∞
    choose n hn using this
    let s : ℕ → ℕ := Nat.rec
      (n (δ 0) (δ_pos 0) 1) -- s 0 := n (δ 0) (δ_pos 0) 1
      (fun k sk => n (δ (k + 1)) (δ_pos (k + 1)) (sk + 1)) -- s (k + 1) := n (δ (k + 1)) (δ_pos (k + 1)) ((s k) + 1)

    have s_increasing : StrictlyIncreasing s := by
      intro i j
      -- clear, we can reduce `∀ i < j, s i < s j` to `∀ j, s j < s (j + 1)`
      induction' j with j hj
      . intro; linarith
      intro hij
      rw [Nat.lt_succ_iff] at hij
      calc s i
        _ ≤ s j := by
          by_cases h : i = j
          . simp [h]
          exact (hj (lt_of_le_of_ne hij h)).le
        _ < s (j + 1) := ?_

      -- now, our goal is `s j < s (j + 1)`
      clear hj hij i
      have := ((hn (δ (j + 1)) (δ_pos (j + 1)) (s j + 1))).1
      rw [← Nat.succ_le_iff]
      exact this

    have s_tendsto : ∀ k, u (s k) ∈ ball x (δ k) := by
      intro k
      induction' k with k hk
      . exact (hn (δ 0) (δ_pos 0) 1).2
      . exact ((hn (δ (k + 1)) (δ_pos (k + 1)) (s k + 1))).2

    obtain ⟨ε, hε, h⟩ := hbad x hxS s s_increasing
    obtain ⟨N, hN⟩ := δ_tendsto ε hε
    obtain ⟨m, hm, h'⟩ := h N

    /-
    now, we have
      s_tendsto : ∀ (k : ℕ), u (s k) ∈ ball x (δ k)
      h' : ε ≤ dist ((u ∘ s) m) x
      hN : ∀ n ≥ N, δ n < ε
    this gives a contradiction
    -/

    have : ε < ε := by
      calc ε
        _ ≤ dist (u (s m)) x := h'
        _ < δ m := s_tendsto m
        _ < ε := hN m hm

    exact lt_irrefl _ this



  -- from each x pick ε(x)
  choose ε hε using hball_finite

  -- the union of these balls covers S
  have cover : S ⊆ ⋃ x : {y // y ∈ S}, ball (x : X) (ε x x.property) := by
    rintro x hx
    rw [mem_iUnion]
    use ⟨x, hx⟩
    exact mem_ball_self (hε x hx).1

  have open_cover : ∀ x : {y // y ∈ S}, IsOpen (ball (x : X) (ε x x.property)) :=
    fun _ ↦ isOpen_ball

  -- apply compactness (finite subcover)
  obtain ⟨t, hfinite⟩ := hS _ open_cover cover
  -- Step 6: pick N large enough so that u_n misses all balls in finite cover
  have exists_N : ∃ N, ∀ n ≥ N, ∀ x ∈ t, u n ∉ ball (x : X) (ε x x.property) := by
    choose N₀ hN₀ using fun x : {y // y ∈ S} => (hε x.val x.property).2
    use Finset.sup t N₀
    intro n hn x hx
    have hn' : n ≥ N₀ x := le_trans (Finset.le_sup hx) hn
    exact hN₀ x n hn'

  obtain ⟨N, hN⟩ := exists_N

  -- Step 7: contradiction
  have huN :  u N ∈ S := huS N
  have huN_in := hfinite huN
  rw [mem_iUnion₂] at huN_in
  obtain ⟨x, hx_in_t, huN_ball⟩ := huN_in
  have := hN N (by rfl) x hx_in_t
  contradiction
