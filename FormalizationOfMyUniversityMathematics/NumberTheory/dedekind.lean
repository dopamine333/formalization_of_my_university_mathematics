import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.FractionalIdeal.Inverse


#check IsDedekindDomain

#check IsDedekindDomainInv

#check _root_.IsFractional.div_of_nonzero
#check IsFractional
#check nonZeroDivisors
/-
IsFractional.div_of_nonzero.{u_3, u_4} {R₁ : Type u_3} [CommRing R₁] {K : Type u_4} [Field K] [Algebra R₁ K]
  [IsFractionRing R₁ K] [IsDomain R₁] {I J : Submodule R₁ K} :
  IsFractional (nonZeroDivisors R₁) I →
    IsFractional (nonZeroDivisors R₁) J → J ≠ 0 → IsFractional (nonZeroDivisors R₁) (I / J)

IsFractional.{u_1, u_2} {R : Type u_1} [CommRing R] (S : Submonoid R) {P : Type u_2} [CommRing P] [Algebra R P]
  (I : Submodule R P) : Prop
  :=  ∃ a ∈ S, ∀ b ∈ I, IsInteger R (a • b)

in particular, S = R₁⁰
a ∈ S ↔ a ∈ R₁⁰ ↔ a ≠ 0 since R₁ is an integral domain

fix R₁, K
for I is submodule R₁ K, I is fractioal iff ∃ 0 ≠ a ∈ R₁, a * I ⊆ R₁
I / J is submodule R₁ K and for all x ∈ K, x ∈ I / J ↔ x * J ⊆ I

to show I / J is fractioal
need to find 0 ≠ c ∈ R₁, c * (I / J) ⊆ R₁

look c * (I / J) ⊆ R₁
↔ ∀ x ∈ K, x ∈ I / J → c * x ∈ R₁
↔ ∀ x ∈ K, x * J ⊆ I → c * x ∈ R₁

since I, J is fractional
∃ 0 ≠ a ∈ R₁, a * I ⊆ R₁
∃ 0 ≠ b ∈ R₁, b * J ⊆ R₁

J ≠ 0 → ∃ y ≠ 0, y ∈ J
b * y ∈ b * J ⊆ R₁

ideed a * b * y ≠ 0, a * b * y ∈ R₁ and
a * b * y * x
∈ a * b * J * x
⊆ a * b * I
⊆ b * R₁
⊆ R₁

a * (b * y) * x
∈ a * J * x (since y ∈ J, J is ideal)
⊆ a * I
⊆ R₁

indeed a * y ≠ 0, a ∈ R₁, y ∈ R₁?


-/

#check PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain
#check FractionalIdeal.mem_inv_iff

open scoped nonZeroDivisors in
theorem one_le_inv_of_le
  [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [h : IsDedekindDomain A]
  {I : FractionalIdeal A⁰ K}
  (h0I : 0 < I) (hI1 : I ≤ 1) : 1 ≤ I⁻¹ := by
  change ∀ x ∈ (1 : FractionalIdeal A⁰ K), x ∈ I⁻¹
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0I.ne']
  intro y hy
  have step₁ : x * y ∈ 1 * I := FractionalIdeal.mul_mem_mul hx hy
  have step₂ : 1 * I ≤ 1 * 1 := mul_le_mul_left' hI1 _
  have step₃ : (1 : FractionalIdeal A⁰ K) * 1 = 1 := mul_one _
  exact step₃ ▸ step₂ step₁

-- I ≤ J⁻¹ ↔ IJ ≤ 1

-- since J⁻¹ ≤ J⁻¹ → J J⁻¹ ≤ 1
-- I J⁻¹ ≤ J J⁻¹ ≤ 1 → J⁻¹ ≤ I⁻¹

-- x ∈ J⁻¹ ↔ ∀ y ∈ J, x * y ∈ 1

-- let x ∈ J⁻¹
-- let y ∈ I,
-- since y ∈ I ⊆ J
-- thus x * y ∈ 1
-- that is x ∈ I⁻¹

theorem le_iff_1 [CommRing A] (I J : Ideal A) :
    I ≤ J ↔ ∀ x ∈ I, x ∈ J := by rfl

theorem le_iff_2 [CommRing A] (I J : Ideal A) :
    I ≤ J ↔ ∃ K, J = I + K := by exact le_iff_exists_add

theorem le_iff_3 [CommRing A] [IsDedekindDomain A] (I J : Ideal A) :
    I ≤ J ↔ ∃ K, I = J * K  := by exact Ideal.dvd_iff_le.symm

theorem le_iff_4 [CommRing A] (I J : Ideal A) :
    I ≤ J ↔ ∃ K, J = I ⊔ K := by exact le_iff_exists_sup


-- let P be a property on X, x ∈ X
-- to prove "Acc x → P(x)"
-- by induction
-- we can assume "(∀ y < x, Acc y → P(y)) → P(x)"
-- theorem induction {C : α → Prop} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a :=

-- let P be a property on X,
-- by induction
-- to show

-- ∀ x ∈ X, x ∈ S → (∃ a ∈ S, ∀ b ∈ S, ¬(b < a))


-- P(x) := x ∈ S → (∃ a ∈ S, ∀ b ∈ S, ¬(b < a))
-- Goal : ∀ x, P(x)
-- by induction,
-- let x ∈ X, we can assume ∀ y < x, P(y)
-- case 1, "∃ y, y < x"
--   take y ∈ K s.t. y < x
--   by induction hypothesis, we have P(y)
--   so P(x) = P(y) holds
-- case 2, "¬(∃ y, y < x)"
--   that is ∀ b, ¬(b < x)
--   choose a = x, let b ∈ S
--   then ¬(b < a) holds

-- x ^ 2 = 1
-- → ab = ba

-- a⁻¹ = a
-- ab = a⁻¹ b⁻¹ = (ba)⁻¹ = ba
