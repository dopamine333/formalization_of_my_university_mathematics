
import Mathlib
open Metric Set Classical

theorem archimedean_zero :
  ∀ ε : ℝ, ε > 0 → ∃ n : ℕ, 0 < (1 : ℝ) / (n + 1) ∧ (1 : ℝ) / (n + 1)< ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  use n
  constructor
  · positivity
  · exact hn

#check StrictMono
-- strictly increasing function
def StrictlyIncreasing (v : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → v i < v j

#check StrictMono.le_iff_le
def StrictlyIncreasing.nondecreasing {v : ℕ → ℕ} (h : StrictlyIncreasing v) :
  ∀ i j, i ≤ j → v i ≤ v j := by
  intro i j hij
  by_cases heq : i = j
  · simp [heq]
  · exact (h i j (Nat.lt_of_le_of_ne hij heq)).le

#check StrictMono.le_apply
def StrictlyIncreasing.self_le {v : ℕ → ℕ} (h : StrictlyIncreasing v) :
  ∀ n, n ≤ v n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have : v n < v (n + 1) := h n (n + 1) (Nat.lt_succ_self n)
    linarith

-- sequential compactness (Def. 9.2(b))
def SequentiallyCompact_def_9_2_b {X : Type} [MetricSpace X] (S : Set X) : Prop :=
  ∀ (u : ℕ → X), (∀ n, u n ∈ S) →
    ∃ p ∈ S, ∃ s : ℕ → ℕ,
      StrictlyIncreasing s ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist ((u ∘ s) n) p < ε

/--
Lemma (Lebesgue number lemma via sequential compactness, by contradiction):
If S is sequentially compact and (G α) is an open cover of `S`,
then there exists r₀ > 0 such that for every `p ∈ S`, some α
satisfies `ball p r₀ ⊆ G α`.
--/
theorem exists_lebesgue_number_of_seq_compact
    {X : Type} [MetricSpace X]
    {S : Set X} (hS : SequentiallyCompact_def_9_2_b S)
    {ι : Type} (G : ι → Set X)
    (hGopen : ∀ α, IsOpen (G α))
    (hCover : S ⊆ ⋃ α, G α) :
    ∃ r₀ > 0, ∀ p ∈ S, ∃ α, ball p r₀ ⊆ G α := by
  -- Suppose NOT: there is no Lebesgue number
  by_contra hneg
  push_neg at hneg
  -- That means: ∀ r₀ > 0, ∃ p ∈ S, ∀ α, ball p r₀ ⊈ G α.
  -- Take r₀ = 1/n for each n
  have bad_seq : ∀ n : ℕ, ∃ x ∈ S, ∀ α, ¬ ball x (1 / (n + 1 : ℝ)) ⊆ G α := by
    intro n
    exact hneg (1 / (n + 1 : ℝ)) (by positivity)
  choose x hxS hbad using bad_seq
  -- Now (x n) is a sequence in S
  -- Apply sequential compactness (b)
  rcases hS x hxS with ⟨y, hyS, s, hs_mono, hs_conv⟩
  -- y ∈ ⋃ α, G α so pick α₀
  have hyU : y ∈ ⋃ α, G α := hCover hyS
  rcases mem_iUnion.mp hyU with ⟨α₀, hy_in_G⟩
  have ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp (hGopen α₀) y hy_in_G
  --have ⟨ε, hε_pos, hε_ball⟩ := hGopen α₀ y hy_in_G
  -- convergence: eventually dist((x ∘ s) n, y) < ε/2
  obtain ⟨N₁, hN₁⟩ := hs_conv (ε / 2) (by linarith)
  -- and 1/(s n + 1) < ε/2 for large n
  have hε2_pos : 0 < ε / 2 := by linarith
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hε2_pos
  obtain ⟨N₁, hN₁⟩ := hs_conv (ε / 2) (by linarith)

  let N := max N₁ N₂
  let xn := x (s N)

  -- Now consider x (s N)
  set xn := x (s N) with hxndef
  have hdist : dist xn y < ε / 2 := hN₁ N (le_max_left N₁ N₂)
  have hsmall : (1 : ℝ) / (s N + 1) < ε / 2 := by
    calc (1 : ℝ) / (s N + 1)
      _ ≤ (1 : ℝ) / (s N₂ + 1) := by
        apply one_div_le_one_div_of_le
        . linarith [Nat.succ_pos (s N₂)]
        . simp [hs_mono.nondecreasing N₂ N (le_max_right N₁ N₂)]
      _ ≤ (1 : ℝ) / (N₂ + 1) := by
        apply one_div_le_one_div_of_le
        . linarith [Nat.succ_pos N₂]
        . simp [hs_mono.self_le N₂]
      _ < ε / 2 := hN₂

  -- show that ball xn (1/(sN+1)) ⊆ ball y ε ⊆ G α₀
  have hball : ball xn (1 / (s N + 1 : ℝ)) ⊆ ball y ε := by
    intro z hz
    have := dist_triangle z xn y
    have : dist z y < (1 / (s N + 1 : ℝ)) + ε / 2 := by linarith [mem_ball.mp hz, hdist]
    have : dist z y < ε := by linarith
    exact mem_ball.mpr this
  have hsub : ball xn (1 / (s N + 1 : ℝ)) ⊆ G α₀ :=
    Subset.trans hball hε_ball
  -- Contradiction: by construction, for every α, the ball is not subset of G α
  exact (hbad (s N)) α₀ hsub
