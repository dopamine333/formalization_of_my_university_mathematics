import Mathlib.Topology.Order.LocalExtr -- gives `IsLocalMin`, `eventually_le`, …
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Extr

/-
Goal:  If  (x n) → a  and  f  has a local minimum at  a,
       then eventually   f (x n) ≥ f a.
-/

open Filter Topology

variable {x : ℕ → ℝ} {a : ℝ} {f : ℝ → ℝ}

/--
If `f` has a local minimum at `a` and the sequence `x` tends to `a`,
then for all sufficiently large `n` we have `f (x n) ≥ f a`.
-/
theorem eventually_ge_of_local_min
    (hmin : IsLocalMin f a)           -- local minimum hypothesis
    (hx   : Tendsto x atTop (𝓝 a)) :  -- convergence of the sequence
    ∀ᶠ n in atTop, f (x n) ≥ f a := by
  -- 1.  A local minimum yields an *eventual* inequality in the neighborhood filter of `a`.
  have h_near : ∀ᶠ y in 𝓝 a, f a ≤ f y := hmin
  -- 2.  Push that inequality forward along the convergence of the sequence `x`.
  have h_seq : ∀ᶠ n in atTop, f a ≤ f (x n) := hx.eventually h_near
  -- 3.  Re‑orient the inequality to match the desired `≥` form.
  simpa [ge_iff_le] using h_seq

theorem eventually_ge_of_local_min'
    (hmin : IsLocalMin f a)           -- local minimum hypothesis
    (hx   : Tendsto x atTop (𝓝 a)) :  -- convergence of the sequence
    ∀ᶠ n in atTop, f (x n) ≥ f a := hx hmin

theorem eventually_ge_of_local_min''
    (hmin : IsLocalMin f a)           -- local minimum hypothesis
    (hx   : Tendsto x atTop (𝓝 a)) :  -- convergence of the sequence
    ∀ᶠ n in atTop, f (x n) ≥ f a := by
  change {n | f (x n) ≥ f a} ∈ atTop
  change {x | f x ≥ f a} ∈ 𝓝 a at hmin
  -- change _ ≤ _ at hx
  have := hx.subset
  have := this hmin
  have : x ⁻¹' {x | f x ≥ f a} ∈ atTop := by
    apply mem_map.mp
    exact this
  dsimp at this
  exact this
