import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

theorem archimedean : ∀ x : ℝ, ∃ n : ℕ, x < n := by
  intro x
  exact exists_nat_gt x
#check exists_nat_one_div_lt
#check exists_nat_gt
#check Nat.one_div_pos_of_nat
theorem archimedean_zero :
  ∀ ε : ℝ, ε > 0 → ∃ n : ℕ, 0 < (1 : ℝ) / (n + 1) ∧ (1 : ℝ) / (n + 1)< ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  use n
  constructor
  · positivity
  · exact hn

-- ∃ N, 1 ≤ N ≤ n ∧ ∀ k, N ≤ k ≤ n → k-th coin are head

-- P(X₁ = 0, X₂ = 0, ...)
-- = P(⋂ n, Xₙ⁻¹({0}))
-- let E m := ⋂ 1 ≤ n ≤ m, Xₙ⁻¹({0})
-- then E m ⊇ E (m + 1) and ⋂ n, Xₙ⁻¹({0}) = ⋂ m, E
-- thus
-- P(X₁ = 0, X₂ = 0, ...)
-- = lim m → ∞, P(E m)
-- = lim m → ∞, P(⋂ 1 ≤ n ≤ m, Xₙ⁻¹({0})) <- finite
-- = lim m → ∞, P(X₁ = 0, X₂ = 0, ..., X ₘ = 0) <- independence
-- = lim m → ∞, Π 1 ≤ n ≤ m, P(Xₙ = 0) <- identically
-- = lim m → ∞, (P(X₁ = 0))^m <- fair coin
-- = lim m → ∞, (1/2)^m
-- = 0

-- P(X₁ = 0, X₂ = 0, ...)
-- = (1/2)^∞
-- = 0

-- P(∃ N, ∀ k ≥ N, Xₖ = 0)
-- = P(⋃ N, ⋂ k ≥ N, Xₖ⁻¹({0}))
-- = lim n → ∞, P(⋃ N ≤ n, ⋂ k ≥ N, Xₖ⁻¹({0})) <- continuity from below
-- = lim n → ∞, Σ N ≤ n, P(⋂ k ≥ N, Xₖ⁻¹({0})) <- subadditivity (finite)

-- for each N,
-- P(⋂ k ≥ N, Xₖ⁻¹({0}))
-- = lim m → ∞, P(⋂ N ≤ k ≤ m, Xₖ⁻¹({0})) <- continuity from above
-- = lim m → ∞, P(X_N = 0, X_{N+1} = 0, ..., X_m = 0)
-- = lim m → ∞, Π N ≤ k ≤ m, P(Xₖ = 0) <- independence (finite)
-- = lim m → ∞, (P(X₁ = 0))^{m - N + 1} <- identically
-- = lim m → ∞, (1/2)^{m - N + 1} <- fair coin
-- = 0

-- P(∃ N, ∀ k ≥ N, Xₖ = 0)
-- = lim n → ∞, Σ N ≤ n, 0
-- = 0



-- P(∃ N, ∀ k ≥ N, Xₖ = 0)
-- ≤ ∑ N, P(∀ k ≥ N, Xₖ = 0)
-- ≤ ∑ N, lim m, P(∀ N ≤ k ≤ m, Xₖ = 0)
-- = ∑ N, lim m, Π N ≤ k ≤ m, P(Xₖ = 0)
-- = ∑ N, lim m, Π N ≤ k ≤ m, 1/2
-- = ∑ N, lim m, (1/2)^{m - N + 1}
-- = ∑ N, 0
-- = 0
-- → P(∃ N, ∀ k ≥ N, Xₖ = 0) = 0

-- P(∃ N, ∀ k ≥ N, Xₖ = 0)
-- ≤ ∑ N, P(∀ k ≥ N, Xₖ = 0)
-- ≤ ∑ N, Π k ≥ N, P(Xₖ = 0)
-- = ∑ N, Π k ≥ N, 1/2
-- = ∑ N, 0
-- = 0
-- → P(∃ N, ∀ k ≥ N, Xₖ = 0) = 0


-- if X₁,X₂,... are indep
-- then for all A₁,A₂,... borel set
-- P(X₁ ∈ A₁, X₂ ∈ A₂, ...)
-- = P(∩ n, Xₙ⁻¹(Aₙ))
-- let E m := ∩ 1 ≤ n ≤ m, Xₙ⁻¹(Aₙ)
-- then E m ⊇ E (m + 1) and ∩ n, Xₙ⁻¹(Aₙ) = ∩ m, E
-- thus
-- P(X₁ ∈ A₁, X₂ ∈ A₂, ...)
-- = lim m → ∞, P(E m)
-- = lim m → ∞, P(∩ 1 ≤ n ≤ m, Xₙ⁻¹(Aₙ)) <- finite
-- = lim m → ∞, P(X₁ ∈ A₁, X₂ ∈ A₂, ..., X ₘ ∈ A ₘ)
-- = lim m → ∞, Π 1 ≤ n ≤ m, P(Xₙ ∈ Aₙ) <- independence
-- = Π n, P(Xₙ ∈ Aₙ)

-- X : Ω₁ → ℝ, Y : Ω₂ → ℝ
-- define X' : Ω₁ × Ω₂ → ℝ by X' = X ∘ π₁
-- define Y' : Ω₁ × Ω₂ → ℝ by Y' = Y ∘ π₂
-- then X', Y' are indep
