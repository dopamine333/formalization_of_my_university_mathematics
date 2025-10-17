-- some basis fact about ideal in commutative rings, in mathlib4, lean4
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Prod

example (R : Type*) [CommRing R] (I J : Ideal R) :
  I * J ≤ I ⊓ J :=
  Ideal.mul_le_inf

example (R : Type*) [CommRing R] [NoZeroDivisors R] (I J : Ideal R) :
  I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
  Ideal.mul_eq_bot

-- prime ideal

example (R : Type*) [CommRing R] (P : Ideal R) :
  P.IsPrime ↔ P ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
  Ideal.isPrime_iff

example (R : Type*) [CommRing R] [NoZeroDivisors R] [IsPrincipalIdealRing R] [Nontrivial R] (P : Ideal R) :
  P.IsPrime ↔ P = ⊥ ∨ ∃ p : R, Prime p ∧ P = Ideal.span {p} :=
  Ideal.isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors


-- cartesian product of ideals

example (R S : Type*) [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) :
  I.prod J = Ideal.comap (RingHom.fst R S) I ⊓ Ideal.comap (RingHom.snd R S) J :=
  rfl

example (R S : Type*) [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (x : R × S) :
  x ∈ I.prod J ↔ x.1 ∈ I ∧ x.2 ∈ J :=
  Ideal.mem_prod I J

example (R S : Type*) [CommRing R] [CommRing S] (I : Ideal (R × S)) :
  I = (Ideal.map (RingHom.fst R S) I).prod (Ideal.map (RingHom.snd R S) I) :=
  Ideal.ideal_prod_eq I



-- my theorem
-- 1. if I, J is ideal in A, B, respectively, then I.prod J is ideal in A × B
-- 2. if K is ideal in A × B, then exists I, J ideal in A, B, respectively, such that K = I.prod J
-- 3. if K is prime ideal in A × B,
--    then exists P prime ideal in A, such that K = P.prod ⊤
--    or exists Q prime ideal in B, such that K = ⊤.prod Q

def my_prod -- this also proves thm 1
  (R S : Type*) [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) :
  Ideal (R × S) where
    carrier := I ×ˢ J
    add_mem' := by
      -- let x, y ∈ I ×ˢ J
      -- show x + y ∈ I ×ˢ J

      -- let x, y ∈ I ×ˢ J
      intro x y hx hy
      -- x.1, y.1 ∈ I, x.2, y.2 ∈ J
      have := hx.1
      -- so x.1 + y.1 ∈ I, x.2 + y.2 ∈ J
      have := I.add_mem hx.1 hy.1
      -- that is x + y ∈ I ×ˢ J
      exact ⟨I.add_mem hx.1 hy.1, J.add_mem hx.2 hy.2⟩

    zero_mem' := by
      -- show 0 ∈ I ×ˢ J

      -- recall def of 0 in R × S is (0, 0)
      -- so we need to show (0, 0) ∈ I ×ˢ J
      -- that is 0 ∈ I and 0 ∈ J
      exact ⟨I.zero_mem, J.zero_mem⟩

    smul_mem' := by
      -- let c ∈ R × S, x ∈ I ×ˢ J
      -- show c • x ∈ I ×ˢ J

      -- have x.1 ∈ I
      -- since I is ideal, c.1 • x.1 ∈ I
      -- c.2 • x.2 ∈ J is similar
      -- recall the def of c • x is (c.1 • x.1, c.2 • x.2)

      intro c x hx
      exact ⟨I.smul_mem c.1 hx.1, J.smul_mem c.2 hx.2⟩

theorem remark_my_prod_eq_prod
  (R S : Type*) [CommRing R] [CommRing S]
  (I : Ideal R) (J : Ideal S) :
  my_prod R S I J = I.prod J :=
  rfl

theorem exists_eq_prod
  (R S : Type*) [CommRing R] [CommRing S]
  (K : Ideal (R × S)) :
  ∃ (I : Ideal R) (J : Ideal S), K = I.prod J := by
  -- let K be ideal in R × S
  -- show ∃ I ideal in R, J ideal in S s.t. K = I.prod J

  -- take I = π₁ '' K, J = π₂ '' K
  -- indeed image of surjective homo of a ideal is ideal
  -- notice the def of map a ideal by a homo in lean
  -- is span of image
  -- is the homo is surjective, then it equal to image
  let π₁ := RingHom.fst R S
  let π₂ := RingHom.snd R S
  let I := K.map π₁
  let J := K.map π₂
  have hI : ∀ x : R, x ∈ I ↔ ∃ y ∈ K, π₁ y = x :=
    fun x ↦ Ideal.mem_map_iff_of_surjective π₁ π₁.surjective
  have hJ : ∀ x : S, x ∈ J ↔ ∃ y ∈ K, π₂ y = x :=
    fun x ↦ Ideal.mem_map_iff_of_surjective π₂ π₂.surjective

  -- show K = I.prod J
  -- 1. K ⊆ I.prod J, 2. I.prod J ⊆ K
  use I, J
  ext x
  constructor
  -- 1. K ⊆ I.prod J
  -- let x ∈ K, show x ∈ I.prod J
  -- to show x.1 ∈ I = π₁ '' K
  -- choose x ∈ K then π₁ x = x.1
  -- so x.1 ∈ π₁ '' K
  -- notice this proof do not just the fact,
  -- K, I, J is ideal
  . intro hx
    have h1 : x.1 ∈ I := by
      rw [hI]
      exact ⟨x, hx, rfl⟩
    have h2 : x.2 ∈ J := by
      rw [hJ]
      exact ⟨x, hx, rfl⟩
    exact ⟨h1, h2⟩

  -- 2. I.prod J ⊆ K
  -- let x ∈ I.prod J , show x ∈ K
  -- have x.1 ∈ I = π₁ '' K
  -- ∃ y ∈ K s.t. π₁ y = x.1
  -- now (x.1, 0) = (1, 0) * y ∈ K since K is ideal
  -- similarly, (0, x.2) ∈ K
  -- so x = (x.1, 0) + (0, x.2) ∈ K
  . intro hx
    obtain ⟨y, hy, hxy⟩ := (hI x.1).mp hx.1
    obtain ⟨z, hz, hxz⟩ := (hJ x.2).mp hx.2
    have h1 : (x.1, 0) ∈ K := by
      have : (⟨1, 0⟩ : R × S) • y ∈ K := K.smul_mem ⟨1, 0⟩ hy
      convert this using 1
      ext
      . simp [← hxy, show π₁ y = y.1 from rfl]
      . simp
    have h2 : (0, x.2) ∈ K := by
      have : (⟨0, 1⟩ : R × S) • z ∈ K := K.smul_mem ⟨0, 1⟩ hz
      convert this using 1
      ext
      . simp
      . simp [← hxz, show π₂ z = z.2 from rfl]
    convert K.add_mem h1 h2
    simp

#check Ideal.ideal_prod_eq -- we just show


theorem prime_ideal_of_prod
  (R S : Type*) [CommRing R] [CommRing S]
  (K : Ideal (R × S)) [K.IsPrime] :
  (∃ (P : Ideal R) (_ : P.IsPrime), K = P.prod ⊤ )
  ∨ (∃ (Q : Ideal S) (_ : Q.IsPrime), K = (⊤ : Ideal R).prod Q) := by

  -- let K be prime ideal in R × S
  -- show ∃ P prime ideal in R, s.t. K = P.prod ⊤
  -- or ∃ Q prime ideal in S, s.t. K = ⊤.prod Q


  -- K = I.prod J is prime
  -- I.prod J ≠ ⊤
  -- x ∉ I.prod J
  -- so x.1 ∉ I or x.2 ∉ J
  -- wlog x.1 ∉ I
  -- I.prod J is prime
  -- (a, 0) * (0, b) = (0, 0) ∈ I.prod J for all a, b
  -- so (a, 0) ∈ I.prod J or (0, b) ∈ I.prod J for all a, b
  -- use (x.1, 0) * (0, b) = (0, 0) ∈ I.prod J
  -- but since x.1 ∈ I, (x.1, 0) ∉ I.prod J
  -- so (0, b) ∈ I.prod J for all b
  -- so J = ⊤
  -- next, show I is prime
  -- I ≠ ⊤ since x ∉ I
  -- let a, b ∈ R, ab ∈ I, show a ∈ I or b ∈ I
  -- consider (ab, 1) ∈ I.prod ⊤
  -- since I.prod ⊤ is prime, (a, 1) ∈ I.prod ⊤ or (b, 1) ∈ I.prod ⊤
  -- that is a ∈ I or b ∈ I

  obtain ⟨I, J, hK⟩ := exists_eq_prod R S K
  have h_prime : (I.prod J).IsPrime := hK ▸ ‹K.IsPrime›

  have step₁ : ∃ x, x ∉ I.prod J := by
    have := h_prime.ne_top
    contrapose! this
    rw [eq_top_iff]
    intro x _
    exact this x

  obtain ⟨x, hx⟩ := step₁
  obtain (hx : x.1 ∉ I) | (hx : x.2 ∉ J ):= not_and_or.1 hx
  . left
    -- 1. show J = ⊤
    have hJ : J = ⊤ := by
      rw [eq_top_iff]
      intro b _
      have : (⟨x.1, 0⟩ : R × S) * ⟨0, b⟩ ∈ I.prod J := by
        rw [Prod.mk_mul_mk, mul_zero, zero_mul]
        exact (I.prod J).zero_mem
      have h_mem := h_prime.mem_or_mem this
      have : (0, b) ∈ I.prod J := by
        contrapose! hx
        have := h_mem.resolve_right hx
        exact this.1
      exact this.2

    -- 2. show I is prime
    have hI_ne_top : I ≠ ⊤ := by
      contrapose! hx
      rw [hx]
      trivial

    have hI_prime : I.IsPrime := by
      refine ⟨hI_ne_top, ?_⟩
      intro a b hab
      have : (⟨a, 1⟩ : R × S) * (b, 1) ∈ I.prod J := by
        rw [hJ]
        exact ⟨hab, trivial⟩
      obtain h | h := h_prime.mem_or_mem this
      . left
        exact h.1
      . right
        exact h.1

    use I, hI_prime
    rw [hK, hJ]

  . right
    -- similar to the left case
    have hI : I = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have : (⟨0, x.2⟩ : R × S) * ⟨a, 0⟩ ∈ I.prod J := by
        rw [Prod.mk_mul_mk, zero_mul, mul_zero]
        exact (I.prod J).zero_mem
      have h_mem := h_prime.mem_or_mem this
      have : (a, 0) ∈ I.prod J := by
        contrapose! hx
        have := h_mem.resolve_right hx
        exact this.2
      exact this.1

    have hJ_ne_top : J ≠ ⊤ := by
      contrapose! hx
      rw [hx]
      trivial

    have hJ_prime : J.IsPrime := by
      refine ⟨hJ_ne_top, ?_⟩
      intro a b hab
      have : (⟨1, a⟩ : R × S) * (1, b) ∈ I.prod J := by
        rw [hI]
        exact ⟨trivial, hab⟩
      obtain h | h := h_prime.mem_or_mem this
      . left
        exact h.2
      . right
        exact h.2

    use J, hJ_prime
    rw [hK, hI]

#check Ideal.ideal_prod_prime
