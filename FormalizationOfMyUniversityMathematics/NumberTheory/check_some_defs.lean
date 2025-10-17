import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.DedekindDomain.AdicValuation


#check LSeries.term_def₀

#check legendreSym.quadratic_reciprocity

#check IsDedekindDomain.HeightOneSpectrum.intValuationDef
#check WithZero (Multiplicative ℤ)
#synth PartialOrder (WithZero (Multiplicative ℤ))
#synth MulZeroClass ((WithZero (Multiplicative ℤ)))
example (a b : WithZero (Multiplicative ℤ)) :
  a * b = b * a := by
  exact CommMonoid.mul_comm a b
example (a : WithZero (Multiplicative ℤ)) :
  a * 0 = 0 := by
  exact CommMonoidWithZero.mul_zero a
example (a b c : WithZero (Multiplicative ℤ))
  (h : a ≤ b) : a * c ≤ b * c := by
  exact mul_le_mul_right' h c
#check WithZero.instOrderBot
example : (⊥ : WithZero (Multiplicative ℤ)) = 0 := by
  exact rfl


#check Associates

set_option trace.Meta.synthInstance true in
example {R : Type u} [CommRing R] : CommSemiring (Ideal R) := by infer_instance
example {R : Type u} [CommRing R] : CompleteLattice (Ideal R) := by infer_instance

example {R : Type u} [CommRing R] : CanonicallyOrderedAdd (Ideal R) := by infer_instance
example {R : Type u} [CommRing R] : SetLike (Ideal R) R := by infer_instance

example {R : Type u} [CommRing R] (I J : Ideal R) :
  I ≤ J ↔ ∀ x ∈ I, x ∈ J := by exact SetLike.le_def

example {R : Type u} [CommRing R] (I J : Ideal R) :
  I ≤ J ↔ ∃ K : Ideal R, J = I + K := by exact le_iff_exists_sup

example {R : Type u} [CommRing R] (I J : Ideal R) :
  I ∣ J ↔ ∃ K : Ideal R, J = I * K := by exact dvd_iff_exists_eq_mul_right


#check Ideal.uniqueFactorizationMonoid
#check BoundedLatticeHom.instBoundedLatticeHomClass

example {R : Type u} [CommRing R] :
  (0 : Ideal R) = (⊥ : Ideal R) := rfl
example {R : Type u} [CommRing R] :
  (0 : Ideal R) = (⊥ : Ideal R) := by exact Ideal.zero_eq_bot

example {R : Type u} [CommRing R] :
  (1 : Ideal R) = (⊤ : Ideal R) := by exact Ideal.one_eq_top


example
  {R : Type u} [CommRing R] {S : Submonoid R}
  {P : Type v} [CommRing P] [Algebra R P] :
  CommSemiring (FractionalIdeal S P) := by infer_instance

example {R : Type u} [CommRing R] : CompleteLattice (Ideal R) := by infer_instance
