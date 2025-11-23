import Mathlib

#check mul_lt_mul_of_pos_right

open Set in
example (A B y a u : ℝ) (f g : ℝ → ℝ)
  (hsubset : Ioo a u ⊆ (fun x ↦ (g x : EReal)) ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)))
  (x : ℝ)
  (hx : x ∈ Ioo a u) :
  x ∈ (fun x ↦ g x) ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)) := by
  have := hsubset hx
  simp [← EReal.coe_lt_coe_iff] at this ⊢
  convert this

#check Ioi_mem_nhds

open Set in
example (A B y a u : ℝ) (f g : ℝ → ℝ)
  (hsubset : Ioo a u ⊆ (fun x ↦ ↑(g x)) ⁻¹' Ioi (2 * (↑(f y) - ↑A * ↑(g y)) / (↑B - ↑A)))
  (x : ℝ)
  (hx : x ∈ Ioo a u) :
  x ∈ (fun x ↦ g x) ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)) := by
  exact hsubset hx

open Set in
example (A B y a u : ℝ) (f g : ℝ → ℝ)
  (hsubset : Ioo a u ⊆ g ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)))
  (x : ℝ)
  (hx : x ∈ Ioo a u) :
  x ∈ g ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)) := by
  exact hsubset hx
/-


hsubset : Ioo a u ⊆ (fun x ↦ ↑(g x)) ⁻¹' Ioi (2 * (↑(f y) - ↑A * ↑(g y)) / (↑B - ↑A))
x : ℝ
hx : x ∈ Ioo a u
⊢ x ∈ (fun x ↦ g x) ⁻¹' Ioi (2 * (f y - A * g y) / (B - A))
-/
open Set in
example (A B y a u : ℝ) (f g : ℝ → ℝ)
  (hsubset : Ioo a u ⊆ (fun x ↦ (g x : EReal)) ⁻¹' Ioi (2 * (↑(f y) - ↑A * ↑(g y)) / (↑B - ↑A)))
  (x : ℝ)
  (hx : x ∈ Ioo a u) :
  x ∈ (fun x ↦ (g x : EReal)) ⁻¹' Ioi (2 * (f y - A * g y) / (B - A)) := by
  exact hsubset hx
