/-

A dedekind
K = Frac(A)
L/K finite sep
B = intergal clousure of A in L


∃ α ∈ B, L = K(α)

∃ f ∈ A[X], f(α) = 0 and f'(α) ≠ 0

Prop 4.4
D(B/A)⁻¹ ⊆ f'(α)⁻¹A[α]

D(B/A)⁻¹ ⊆ f'(α)⁻¹A[α]
→ (f'(α)) ⊆ D(B/A) where (f'(α)) is princple ideal
↔ D(B/A) | (f'(α))

if B = A[α] then D(B/A) = (f'(α))

example
A = ℤ, K = ℚ, L = ℚ(√d), d ∈ ℤ, d ≠ 0, d squere free
→
B = ℤ[√d]       if d = 2,3 mod 4
B = ℤ[(1+√d)/2] if d = 1 mod 4
α = √d             if d = 2,3 mod 4
α = (1+√d)/2       if d = 1 mod 4
(L = ℚ(√d) = ℚ((1+√d)/2) = K(α))
f(x) = x² - d             if d = 2,3 mod 4
f(x) = x² - x + (1-d)/4   if d = 1 mod 4
since B = A[α]
D(B/A) = (f'(α)) = (2√d) if d = 2,3 mod 4
D(B/A) = (f'(α)) = (√d)  if d = 2,3 mod 4

example
A = ℤ, K = ℚ, L = ℚ(₃√2), α = ₃√2, f(x) = x³-2
→
A[α]ᵛ = f'(α)⁻¹A[α]
ℤ[₃√2]ᵛ = (3₃√4)⁻¹ Z[₃√2]
D(B/A) | (f'(α))
D(B/A) | (3₃√4)
in fact, O_L = ℤ[₃√2] (i.e. B = A[α])
so D(B/A) = (f'(α)) = (3₃√4)

(s ⊧ ¬¬P) ↔ (∀ u, Rsu → (∃ v, Ruv → v ⊧ A))
-/
/-

B₁(0) = { x ∈ ℝ² | |x| < 1 } ⊆ ℝ²
∂B₁(0) = { x ∈ ℝ² | |x| = 1 } ⊆ ℝ²
define f : B₁(0) × ∂B₁(0) → ℝ by f(x,y) = 1/|x-y|
is f smooth on B₁(0) × ∂B₁(0) ?

Since x ↦ K(x,y) is smooth for x ≠ y,

for all y ∈ ℝⁿ, (x ↦ K(x,y)) is smooth on {x ∈ ℝⁿ | x ≠ y}

f : ℝ × ℝ → ℝ
∀ y ∈ ℝ, f(., y) is smooth on ℝ
f is smooth on ℝ × ℝ

K(x,y) = ..., for x ∈ B_R, y ∈ ∂B_R

(X, τ), (Y, σ) 兩個拓樸空間
以為 (X × Y, τ × σ) product topo space 裡的開集
一定長 U × V for some U ∈ τ, V ∈ σ 的樣子

∂ₓᵢK

u is subharmonic → 0 ≤ Δu ≤ 0 → Δu = 0 → u is harmonic


a,b,c ∈ ℤ₃
a*c ≠ 0
→ det = a*c ≠ 0

[c 0]
[-b a]/a*c
[a 0]
[b c]
[a' 0]
[b' c']

[aa' 0]
[a'b+b'c cc']



1 0
b 1
b ∈ ℤ₃


[1 0]
[b+b' 1]


-/
