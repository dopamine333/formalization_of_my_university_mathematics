/-
This file demonstrates the equivalence between Mathlib's HasFDerivAt
and the Wikipedia definition of Fréchet derivative.

lean version : 4.22.0-rc3
date: 2025-07-31
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic

open scoped Topology -- for notation 𝓝
#eval Lean.versionString

-- https://en.wikipedia.org/wiki/Fr%C3%A9chet_derivative
variable
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (f : V → W) (A : V →L[ℝ] W) (x : V)

theorem wiki_def_HasFDerivAt : HasFDerivAt f A x ↔
  Filter.Tendsto (fun h ↦ ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  calc HasFDerivAt f A x
    _ ↔ HasFDerivAtFilter f A x (𝓝 x) := by rfl
    _ ↔ (fun x' => f x' - f x - A (x' - x)) =o[ℝ; 𝓝 x] (fun x' => x' - x) := by
      exact hasFDerivAtFilter_iff_isLittleOTVS f A x (𝓝 x)
    _ ↔  (fun x' => f x' - f x - A (x' - x)) =o[𝓝 x] (fun x' => x' - x) := by
      exact Asymptotics.isLittleOTVS_iff_isLittleO
    _ ↔ (fun x' => ‖f x' - f x - A (x' - x)‖) =o[𝓝 x] (fun x' => ‖x' - x‖) := by
      exact Iff.symm Asymptotics.isLittleO_norm_norm
    _ ↔ Filter.Tendsto (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (𝓝 x) (𝓝 0) := by
      rw [Asymptotics.isLittleO_iff_tendsto]
      intro x' hx'
      have : x' = x := by
        rw [norm_eq_zero] at hx'
        rw [sub_eq_zero.mp hx']
      simp [this]
    _ ↔ Filter.Tendsto (fun h ↦ ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
      convert @Filter.tendsto_map'_iff _ _ _ (fun x' ↦ ‖f x' - f x - A (x' - x)‖ / ‖x' - x‖) (fun h ↦ x + h) _ _ using 2
      . rw [map_add_left_nhds, add_zero]
      . ext h
        dsimp
        congr <;> simp


variable
  {U : Set V} (hU : IsOpen U) (hxU : x ∈ U)

example :
  HasFDerivAt f A x
  ↔
  HasFDerivWithinAt f A U x
  := by
  rw [HasFDerivAt, HasFDerivWithinAt]
  rw [IsOpen.nhdsWithin_eq]
  . exact hU
  . exact hxU
