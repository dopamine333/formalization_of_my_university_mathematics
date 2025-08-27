import Mathlib.GroupTheory.Schreier

open scoped Finset Pointwise

open Subgroup

#check card_dvd_exponent_pow_rank
#check Monoid.exponent
#check Group.rank
#check Group.FG
#synth WellFoundedLT (Finset ℕ)
#check IsComplement
#check IsComplement'
#check IsCompl
example [Group G] : CompleteLattice (Subgroup G) := inferInstance
set_option trace.Meta.synthInstance true in
example [Group G] : BoundedOrder (Subgroup G) := inferInstance
example [Group G] (H K : Subgroup G) (h : IsComplement' H K) : IsCompl H K :=
  IsComplement'.isCompl h
-- theorem my_card_dvd_exponent_pow_rank
--   (G : Type u_1) [CommGroup G] [Group.FG G]
--   : Nat.card G ∣ Monoid.exponent G ^ Group.rank G := by
--   sorry


#check transferFunction
#check quotientEquivSigmaZMod
#check MulAction.selfEquivSigmaOrbits
#check Equiv.sigmaCongrRight
#check MulAction.orbitZPowersEquiv
/-
orbitZPowersEquiv
↑(MulAction.orbit (↥(zpowers a)) b) ≃ ZMod (Function.minimalPeriod (fun x ↦ a • x) b)
⟨a⟩b ≃ ℤₙ where n is min s.t. a ^ n * b = b

selfEquivSigmaOrbits
α ≃ (ω : MulAction.orbitRel.Quotient G α) × ↑(MulAction.orbit G (Quotient.out ω))


/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod (g • ·) q.out) :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

⟨g⟩ act on G / H by left mul
→ parition G / H into orbits
i.e. G / H ≃ (ω : orbits) × ⟨g⟩ω.out
moreover ∀ b ∈ G,
⟨g⟩b ≃ ℤ_n(b), where n(b) is min n ∈ ℤ s.t. g ^ n * b = b
thus G / H ≃ (ω : orbits) × ℤ_n(ω.out)

notice g ^ |⟨g⟩| * b = e * b = b
→ n(b) ≤ |⟨g⟩|


/-- The transfer transversal as a function. Given a `⟨g⟩`-orbit `q₀, g • q₀, ..., g ^ (m - 1) • q₀`
  in `G ⧸ H`, an element `g ^ k • q₀` is mapped to `g ^ k • g₀` for a fixed choice of
  representative `g₀` of `q₀`. -/
noncomputable def transferFunction : G ⧸ H → G := fun q =>
  g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out.out


quotientEquivSigmaZMod H g : G / H ≃ (ω : orbits) × ℤ_n(ω.out)
quotientEquivSigmaZMod H g q : (ω : orbits) × ℤ_n(ω.out)
(quotientEquivSigmaZMod H g q).2 : ℤ_n((quotientEquivSigmaZMod H g q).1.out)


q : G / H
quotientEquivSigmaZMod H g q = ⟨ω(q) , k(q)) : (ω : orbits) × ℤ_n(ω.out)

q ↦ g ^ k(q) * ω(q).out.out

g ^ (cast (quotientEquivSigmaZMod H g q).2 : ℤ) * (quotientEquivSigmaZMod H g q).1.out.out

mk (g ^ k(q) * ω(q).out.out)
(mk g) ^ k(q) * (mk ω(q).out.out)



G = {g₁, g₂, ...}
H ≤ G
G / H = {g₁H, g₂H, ...} = {q₁, q₂, ...}
g ∈ G
⟨g⟩ act on G / H by left mul
ex. g • g₁H = (g * g₁)H
parition G / H into orbits
G / H
= {q₁, g • q₁, g ^ 2 • q₁, ...} ∪ {q₂, g • q₂, g ^ 2 • q₂, ...} ∪ ...
= ⟨g⟩q₁ ∪ ⟨g⟩q₂ ∪ ...
for any q ∈ G / H,
  q = g ^ k • q₀ for some k ∈ ℤ, q₀ ∈ G / H
let q₀ = g₀H
def map q ↦ g ^ k * g₀

q = g ^ k • g₀H = (g ^ k * g₀)H
-/
#check MulAction.mulLeftCosetsCompSubtypeVal
#check MulAction.quotient
#check MulAction.left_quotientAction


theorem my_transferFunction_apply
  {G : Type u} [Group G] {H : Subgroup G} (g : G) (q : G ⧸ H)
  : H.transferFunction g q =
    g ^ (((H.quotientEquivSigmaZMod g) q).snd.cast : ℤ) * Quotient.out (Quotient.out ((H.quotientEquivSigmaZMod g) q).fst) := by
    let orbit_of_g₀H_k := H.quotientEquivSigmaZMod g q
    rfl

#check quotientEquivSigmaZMod_symm_apply
theorem my_coe_transferFunction
  {G : Type u} [Group G] {H : Subgroup G} (g : G) (q : G ⧸ H)
  : ↑(H.transferFunction g q) = q := by

  set orbit_of_g₀H_uncast_k := H.quotientEquivSigmaZMod g q

  have h1 := Subgroup.transferFunction_apply g q
  have h2 := quotientEquivSigmaZMod_symm_apply H g orbit_of_g₀H_uncast_k.1 orbit_of_g₀H_uncast_k.2

  set orbit_of_g₀H := orbit_of_g₀H_uncast_k.fst
  set g₀H := Quotient.out orbit_of_g₀H_uncast_k.fst
  set g₀ := Quotient.out orbit_of_g₀H_uncast_k.fst.out
  set uncast_k := orbit_of_g₀H_uncast_k.snd
  set k := orbit_of_g₀H_uncast_k.snd.cast (R := ℤ)

  change H.transferFunction g q = g ^ k * g₀ at h1
  change (H.quotientEquivSigmaZMod g).symm ((H.quotientEquivSigmaZMod g) q) = g ^ k • g₀H at h2
  have h3 : (H.quotientEquivSigmaZMod g).symm ((H.quotientEquivSigmaZMod g) q) = q := by rw [Equiv.symm_apply_apply]

  calc ↑(H.transferFunction g q)
    _ = ↑(g ^ k * g₀) := by rw [h1]

    -- _ = QuotientGroup.mk (g ^ k * g₀) := rfl
    -- _ = QuotientGroup.mk (g ^ k • g₀) := rfl
    -- _ = g ^ k • QuotientGroup.mk (g₀) := rfl
    -- _ = g ^ k • g₀H := by congr; unfold g₀ g₀H; rw [QuotientGroup.out_eq']

    _ = ↑(g ^ k • g₀) := rfl
    _ = ↑(g ^ k • g₀H.out) := rfl
    _ = g ^ k • g₀H := by rw [MulAction.Quotient.coe_smul_out]

    _ = q := by rw [← h2, h3]

-- #check default
/-
diff φ T (g • T) = diff φ S (g • S)

diff φ T (g • T) = diff φ T S * diff φ S (g • S) * diff φ (g • S) (g • T)
diff φ T (g • T) = diff φ T S * diff φ (g • S) (g • T) * diff φ S (g • S)
diff φ T (g • T) = diff φ T S * diff φ S T * diff φ S (g • S)
diff φ T (g • T) = diff φ S (g • S)

diff φ T (g • T) = diff φ T S * diff φ S (g • T)
diff φ T (g • T) = diff φ (g • T) (g • S) * diff φ S (g • T)
diff φ T (g • T) = diff φ S (g • T) * diff φ (g • T) (g • S)
diff φ T (g • T) = diff φ S (g • S)
-/


open MulAction in
/-- Auxiliary lemma in order to state `transfer_eq_pow`. -/
theorem my_transfer_eq_pow_aux {G : Type u_1} [Group G] {H : Subgroup G} (g : G)
    (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
    g ^ H.index ∈ H := by
  by_cases hH : H.index = 0
  · rw [hH, pow_zero]
    exact H.one_mem
  letI := fintypeOfIndexNeZero hH
  classical
    replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H := fun k g₀ hk =>
      (congr_arg (· ∈ H) (key k g₀ hk)).mp hk
    replace key : ∀ q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q ∈ H := fun q =>
      key (Function.minimalPeriod (g • ·) q) q.out
        (QuotientGroup.out_conj_pow_minimalPeriod_mem H g q)
    let f : Quotient (orbitRel (zpowers g) (G ⧸ H)) → zpowers g := fun q =>
      (⟨g, mem_zpowers g⟩ : zpowers g) ^ Function.minimalPeriod (g • ·) q.out
    have hf : ∀ q, f q ∈ H.subgroupOf (zpowers g) := fun q => key q.out
    replace key :=
      Subgroup.prod_mem (H.subgroupOf (zpowers g)) fun q (_ : q ∈ Finset.univ) => hf q
    suffices ∏ q, f q = g ^ H.index by
      rw [← this]
      exact key
    calc ↑(∏ q, f q)
      _ = ↑(∏ q, (_ : zpowers g) ^ _) := rfl
      _ = ↑((_ : zpowers g) ^ ∑ q, _) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = g ^ ∑ q, _ := rfl
      _ = g ^ ∑ q, Fintype.card (orbit _ _) := by simp_rw [minimalPeriod_eq_card]; rfl
      _ = g ^ Fintype.card (Sigma _) := by rw [← Fintype.card_sigma]
      _ = g ^ Fintype.card (G ⧸ H) := by
        rw [Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H))]
      _ = g ^ H.index := by rw [index_eq_card, Nat.card_eq_fintype_card]

/-
g ^ H.index
g ^ | G / H |
g ^ | ∑ (ω : orbits), ω |
g ^ ∑ (ω : orbits) |ω|
∏ (ω : orbits), g ^ |ω|
∏ (ω : orbits), g ^ minimalPeriod (g • .) ω.out

if ∀ q : G ⧸ H, g ^ Function.minimalPeriod (g • ·) q ∈ H
then g ^ H.index ∈ H
-/

open MonoidHom MulAction in
theorem my_transfer_eq_pow {G : Type u_1} [Group G] {H : Subgroup G} {A : Type u_2} [CommGroup A]
  (ϕ : ↥H →* A) [H.FiniteIndex] (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k)
  : transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ := by
  classical
    let := H.fintypeQuotientOfFiniteIndex
    change ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key

    rw [
      -- ϕ.transfer g
      transfer_eq_prod_quotient_orbitRel_zpowers_quot,
      -- ∏ ⟦g₀H⟧ : orbits, ϕ (g₀⁻¹ * g ^ k * g₀), where k is min period of (g • .) on g₀H
      ← Finset.prod_map_toList,
      -- fix an order of product
      -- ∏ ⟦g₀H⟧ : orbits, ϕ (g₀⁻¹ * g ^ k * g₀)
      ← Function.comp_def ϕ, List.prod_map_hom
      --  ϕ ( ∏ ⟦g₀H⟧ : orbits, g₀⁻¹ * g ^ k * g₀ )
    ]

    -- ϕ ( ∏ ⟦g₀H⟧ : orbits, g₀⁻¹ * g ^ k * g₀ ) = ϕ (g ^ H.index)
    refine congrArg ϕ (Subtype.coe_injective ?_)
    dsimp only
    -- ∏ ⟦g₀H⟧ : orbits, g₀⁻¹ * g ^ k * g₀ = g ^ H.index

    rw [
      -- ∏ ⟦g₀H⟧ : orbits, g₀⁻¹ * g ^ k * g₀ = g ^ H.index
      ← (zpowers g).coe_mk g (mem_zpowers g), ← (zpowers g).coe_pow,
      -- some type coe, nothing change mathmatically
      -- = g ^ H.index
      index_eq_card, Nat.card_eq_fintype_card,
      -- = g ^ | G / H |
      Fintype.card_congr (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)),
      -- = g ^ | (ω : orbits) × ω |
      Fintype.card_sigma,
      -- = g ^ ∑ ω : orbits, | ω |
      ← Finset.prod_pow_eq_pow_sum,
      -- = ∏ ω : orbits, g ^ | ω |
      ← Finset.prod_map_toList
      -- fix an order of product
      -- = ∏ ω : orbits, g ^ | ω |
      ]

    simp only [Subgroup.val_list_prod, List.map_map] -- some type coe

    -- ∏ ⟦g₀H⟧ : orbits, g₀⁻¹ * g ^ k * g₀ = g ^ H.index
    -- = ∏ ω : orbits, g ^ |ω|
    -- where k is min period of (g • .) on g₀H
    simp only [← minimalPeriod_eq_card]
    -- but ∀ ω : orbits, |ω| = min period of (g • .) on ω.out thus k = |ω|
    -- ∏ ω : orbits, g₀⁻¹ * g ^ |ω| * g₀ = g ^ H.index
    -- = ∏ ω : orbits, g ^ |ω|

    congr
    funext q
    conv_rhs => dsimp
    -- g₀⁻¹ * g ^ |ω| * g₀ = g ^ |ω|
    apply key
    -- recall key : ∀ (k g₀) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H),
    --    g₀⁻¹ * g ^ k * g₀ = g ^ k
    -- magically, the proof hk aleady in the goal term
    -- true goal :
    -- ↑⟨g₀⁻¹ * g ^ |ω| * g₀, ...⟩ = g ^ H.index
    -- where ... is the proof of hk. (wow)

-- example [Group G] (H : Subgroup G) (g : G)
--   : ( ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H) ↔ (∀ n, n ∈ H → g * n * g⁻¹ ∈ H) := by
--   constructor
--   . intro h n hn
--     exact (h n).1 hn
--   . intro h n
--     constructor
--     . intro hn
--       exact h n hn
--     . intro hg
--       sorry

example [Group G] (H N : Subgroup G) (h1 : H ≤ N) [h2 : (H.subgroupOf N).Normal]
  : N ≤ H.normalizer := by
  intro g hg
  rw [mem_normalizer_iff]
  have := h2.conj_mem
  simp_rw [mem_subgroupOf] at this
  intro x
  constructor
  . intro hx
    have := this ⟨x, h1 hx⟩ hx ⟨g, hg⟩
    simp at this
    exact this
  . intro hx
    have := this ⟨_, h1 hx⟩ hx ⟨_, N.inv_mem hg⟩
    simp [mul_assoc] at this
    exact this

example [Group G] (H : Subgroup G) : centralizer H ≤ normalizer H := by
  intro y hy
  have hy1 : ∀ h ∈ H, y * h * y⁻¹ ∈ H := by
    intro h hh
    have := hy h hh
    convert hh
    rw [← this]
    group
  have hy2 : ∀ h ∈ H, y⁻¹ * h * y ∈ H := by
    intro h hh
    have := hy h hh
    convert hh
    rw [mul_assoc, this]
    group
  intro x
  constructor
  . intro hx
    exact hy1 _ hx
  . intro hx
    have := hy2 _ hx
    convert this
    group

/-
f : [a, b] → ℝ
∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - a| < δ → |(f(x)-f(x₀))/(x-x₀) - L| < ε
f : ℝ → ℝ
a : ℝ
L : ℝ
s : Set ℝ
∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, 0 < |x - a| < δ → |(f(x)-f(x₀))/(x-x₀) - L| < ε
(a, ∞)
(-∞, a)
⊆
(a - ε, b + ε)
ℝ²
ℝⁿ
-/




#check closure_empty -- rank G maybe = 0
#check Monoid.lcm_orderOf_eq_exponent
-- by def, it is easy to see, exp G = lcm {orderOf g | g ∈ G}
#check Monoid.exists_orderOf_eq_exponent
#check Monoid.exponent_eq_iSup_orderOf
#check Monoid.exponent_eq_max'_orderOf
-- more over in CommMonoid, ∃ g ∈ G, exp G = orderOf g, so exp G = max {orderOf g | g ∈ G}
#check card_dvd_exponent_pow_rank --origin thm
theorem my_card_dvd_exponent_pow_rank
  (G : Type u) [CommGroup G] [Group.FG G] :
  Nat.card G ∣ Monoid.exponent G ^ Group.rank G := by
  classical
  -- need for DecidableEq { x // x ∈ S } (why?)
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  -- S is finite subset of G, |S| = rank G, ⟨S⟩ = G
  rw [
    -- goal : |G| | exp G ^ rank G
    -- where exp G is min n > 0 s.t. ∀ g ∈ G, g ^ n = 1 if exists else 0
    --       rank G is min n s.t. ∃ S ⊆ G is finite s.t. G = ⟨S⟩ and |S| = n
    ← hS1,
    -- |G| | exp G ^ |S|
    ← Fintype.card_coe, ← Finset.card_univ,
    -- change @Finset.card G S to @Finset.card ↑S univ
    -- we write all of them as |S|
    ← Finset.prod_const
    -- |G| | ∏ x ∈ S, exp G
  ]

  let f : (∀ g : S, zpowers (g : G)) →* G := noncommPiCoprod fun s t _ x y _ _ => mul_comm x _
  /-
  say S = {g₁, g₂, ...}
  we have
  zpowers g₁ = ⟨g₁⟩ = {1, g₁, g₁ ^ 2, g₁ ^ 3, ...}
  zpowers g₂ = ⟨g₂⟩ = {1, g₂, g₂ ^ 2, g₂ ^ 3, ...}
  zpowers g₃ = ⟨g₃⟩ = {1, g₃, g₃ ^ 2, g₃ ^ 3, ...}
  choose n₁, n₂, n₃ ...
  def φ : S → G by gₖ ↦ gₖ ^ nₖ then φ ∈ (∀ g : S, zpowers (g : G))
  def f : (∀ g : S, zpowers (g : G)) → G by φ ↦ ∏ gₖ ∈ S, φ(gₖ)
  need to check the order of product in ∏ gₖ ∈ S, φ(gₖ) is well def.
  indeed G is CommGroup
  -/
  have hf : Function.Surjective f := by
    rw [
      -- goal : f is onto
      ← MonoidHom.range_eq_top,
      -- range f = G
      eq_top_iff,
      -- G ≤ range f
      ← hS2,
      -- ⟨S⟩ ≤ range f
      closure_le
      -- S ⊆ range f
    ]
    exact fun g hg
      => ⟨
        -- given gₖ ∈ S
        Pi.mulSingle ⟨g, hg⟩ ⟨g, mem_zpowers g⟩,
        -- use φ : gᵢ ↦ gₖ if i = k else gᵢ ↦ 1
        -- i.e. pick nₖ = 1, nᵢ = 0 for i ≠ k
        noncommPiCoprod_mulSingle _ _
        -- indeed, f(φ) = ∏ gᵢ ∈ S, φ(gᵢ) = 1 * ... * 1 * gₖ * 1 * ... * 1 = gₖ
      ⟩
  replace hf := card_dvd_of_surjective f hf
  -- since f : (∀ g : S, zpowers (g : G)) → G is onto, by first iso thm,
  -- G = range f ≃ (∀ g : S, zpowers (g : G)) ⧸ ker f
  -- → hf : |G| | |(∀ g : S, zpowers (g : G))|
  -- if G is not finite? don't worry, it is derived from the bijection
  rw [Nat.card_pi] at hf
  -- hf : |G| | ∏ g : S, |zpowers (g : G))|
  refine hf.trans (Finset.prod_dvd_prod_of_dvd _ _ fun g _ => ?_)
  -- if we have ∀ g : S, |zpowers (g : G))| | exp G
  -- → |G| | (∏ g : S, |zpowers (g : G))|) | (∏ g ∈ S, exp G), done. (use G is comm)
  -- to show ∀ g : S, |zpowers (g : G))| | exp G
  rw [Nat.card_zpowers]
  exact Monoid.order_dvd_exponent (g : G)
  -- it is easy, since |zpowers (g : G))| = orderof g | exp G
  -- (more detail, by def g ^ exp G = 1, thus orderof g | exp G)


#check card_dvd_exponent_pow_rank'
theorem my_card_dvd_exponent_pow_rank'
  (G : Type u) [CommGroup G] [Group.FG G] {n : ℕ} (hG : ∀ (g : G), g ^ n = 1) :
  Nat.card G ∣ n ^ Group.rank G :=
  (card_dvd_exponent_pow_rank G).trans
    (pow_dvd_pow_of_dvd (Monoid.exponent_dvd_of_forall_pow_eq_one hG) (Group.rank G))
  -- by def, exp G is min n > 0 s.t. ∀ (g : G), g ^ n = 1
  -- but in fact, exp G is also min in dvd order n>0 s.t. ∀ (g : G), g ^ n = 1
  -- i.e. exp G | n ↔ ∀ (g : G), g ^ n = 1, see `exponent_dvd_iff_forall_pow_eq_one`
  -- thus if ∀ (g : G), g ^ n = 1
  -- then |G| | exp G ^ rank G | n ^ rank G
#check closure_induction
#check closure_induction_right
#check closure_mul_image_mul_eq_top
theorem my_closure_mul_image_mul_eq_top
  {G : Type u} [Group G] {H : Subgroup G} {R S : Set G}
  (hR : IsComplement H R) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
  (closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹)) * R = ⊤ :=  by
  /-
  G = {Hr₁, Hr₂, ...}, 1 ∈ R = {r₁, r₂, ...}, ⟨S⟩ = G
  ∀ g ∈ G, ∃ r(g) ∈ R, g ∈ Hr(g) (i.e. r(g) = hR.toRightFun g)
  ⊢ ⟨{ (r * s) * (r(r * s))⁻¹  | r * s ∈ R * S}⟩ * R = G
  -/
  let f : G → R := hR.toRightFun
  let U : Set G := (R * S).image fun g => g * (f g : G)⁻¹
  change (closure U : Set G) * R = ⊤
  /-
  def f : G → R, g ↦ r(g)
  def U = { r * s * f(r * s)⁻¹ | r ∈ R, s ∈ S}
  goal : ⟨U⟩ * R = G
  -/
  refine top_le_iff.mp fun g _ => ?_
  -- ⟨U⟩ * R = G ↔ G ≤ ⟨U⟩ * R ↔ ∀ g ∈ G, g ∈ ⟨U⟩ * R
  refine closure_induction_right ?_ ?_ ?_ (eq_top_iff.mp hS (mem_top g))
  /-
  ∀ g ∈ ⟨S⟩, g = s₁ * s₂ * ... * sₙ for some s₁ ... sₙ ∈ S ∪ S⁻¹
  to show ∀ g ∈ ⟨S⟩, some property p(g) holds, only need to show
  1. one : p(1)
  2. mul_right : if p(s₁ * ... * sₙ) then ∀ s ∈ S, p(s₁ * ... * sₙ * s)
  3. mul_inv_cancel : if p(s₁ * ... * sₙ) then ∀ s ∈ S, p(s₁ * ... * sₙ * s⁻¹)
  now, to show ∀ g ∈ G = ⟨S⟩, g ∈ ⟨U⟩ * R, just induction on the property (. ∈ ⟨U⟩ * R)
  -/
  · exact ⟨1, (closure U).one_mem, 1, hR1, one_mul 1⟩
    -- 1. one
    -- 1 ∈ ⟨U⟩, 1 ∈ R
    -- → 1 = 1 * 1 ∈ ⟨U⟩ * R, done
  · rintro - - s hs ⟨u, hu, r, hr, rfl⟩
    -- 2. mul_right
    -- goal : ∀ x ∈ ⟨S⟩, ∀ y ∈ S, x ∈ ⟨U⟩ * R → x * y ∈ ⟨U⟩ * R
    -- notice x ∈ ⟨U⟩ * R → x = u * r for some u ∈ ⟨U⟩, r ∈ R, set y = s
    -- thus let s ∈ S, u ∈ ⟨U⟩, r ∈ R, show u * r * s ∈ ⟨U⟩ * R
    rw [show u * r * s = u * (r * s * (f (r * s) : G)⁻¹) * f (r * s) by group]
    -- notice u * r * s = u * (r * s * f(r * s)⁻¹) * f(r * s)
    refine Set.mul_mem_mul ((closure U).mul_mem hu ?_) (f (r * s)).coe_prop
    -- since u ∈ ⟨U⟩, f(r * s) ∈ R, to show u * (r * s * f(r * s)⁻¹) * f(r * s) ∈ ⟨U⟩ * R
    -- it is suffice to show r * s * f(r * s)⁻¹ ∈ ⟨U⟩
    exact subset_closure ⟨r * s, Set.mul_mem_mul hr hs, rfl⟩
    -- recall U = {r * s * f(r * s)⁻¹ | r ∈ R, s ∈ S}
    -- thus r * s * f(r * s)⁻¹ ∈ U ⊆ ⟨U⟩. done
  · rintro - - s hs ⟨u, hu, r, hr, rfl⟩
    -- 3. mul_inv_cancel
    -- goal : ∀ x ∈ ⟨S⟩, ∀ y ∈ S, x ∈ ⟨U⟩ * R → x * y⁻¹ ∈ ⟨U⟩ * R
    -- notice x ∈ ⟨U⟩ * R → x = u * r for some u ∈ ⟨U⟩, r ∈ R, set y = s
    -- thus let s ∈ S, u ∈ ⟨U⟩, r ∈ R, show u * r * s⁻¹ ∈ ⟨U⟩ * R
    rw [show u * r * s⁻¹ = u * (f (r * s⁻¹) * s * r⁻¹)⁻¹ * f (r * s⁻¹) by group]
    /-
    notice u * r * s⁻¹
      = u * (r * s⁻¹ * f(r * s⁻¹)⁻¹) * f(r * s⁻¹)
      = u * (f(r * s⁻¹) * s * r⁻¹)⁻¹ * f(r * s⁻¹)
    -/
    refine Set.mul_mem_mul ((closure U).mul_mem hu ((closure U).inv_mem ?_)) (f (r * s⁻¹)).2
    /-
    since u ∈ ⟨U⟩, f(r * s⁻¹) ∈ R
    to show u * (f(r * s⁻¹) * s * r⁻¹)⁻¹ * f(r * s⁻¹) ∈ ⟨U⟩ * R
    suffice show f(r * s⁻¹) * s * r⁻¹ ∈ ⟨U⟩
    -/
    refine subset_closure ⟨f (r * s⁻¹) * s, Set.mul_mem_mul (f (r * s⁻¹)).2 hs, ?_⟩
    -- recall U = {r * s * f(r * s)⁻¹ | r ∈ R, s ∈ S}
    -- notice f(r * s⁻¹) ∈ R, s ∈ S
    -- we have f(r * s⁻¹) * s * f(f(r * s⁻¹) * s)⁻¹ ∈ U ⊆ ⟨U⟩
    -- claim : f(r * s⁻¹) * s * f(f(r * s⁻¹) * s)⁻¹ = f(r * s⁻¹) * s * r⁻¹  (wow)
    rw [
      -- f(r * s⁻¹) * s * f(f(r * s⁻¹) * s)⁻¹ = f(r * s⁻¹) * s * r⁻¹
      mul_right_inj,
      -- f(f(r * s⁻¹) * s)⁻¹ = r⁻¹
      inv_inj,
      -- f(f(r * s⁻¹) * s) = r
      ← Subtype.coe_mk r hr, ← Subtype.ext_iff, Subtype.coe_mk
      -- coe to ↑R
      ]
    apply (isComplement_iff_existsUnique_mul_inv_mem.mp hR (f (r * s⁻¹) * s)).unique
      (hR.mul_inv_toRightFun_mem (f (r * s⁻¹) * s))
    -- right coset of H form a parition of G
    -- → coset are disjoint
    -- → if g ∈ Hr₁, g ∈ Hr₂ then r₁ = r₂
    -- ↔ if gr₁⁻¹ ∈ H, gr₂⁻¹ ∈ H then r₁ = r₂
    -- apply to g := f(r * s⁻¹) * s, r₁ := f(f(r * s⁻¹) * s), r₂ := r
    -- by def of f, we have g ∈ Hf(g) ↔ g⁻¹f(g) ∈ H → f(r * s⁻¹) * s * f(f(r * s⁻¹) * s)⁻¹ ∈ H
    -- suffice to show, gr₂⁻¹ =  f(r * s⁻¹) * s * r⁻¹ ∈ H
    rw [mul_assoc, ← inv_inv s, ← mul_inv_rev, inv_inv]
    exact hR.toRightFun_mul_inv_mem (r * s⁻¹)
    -- by def of f
    -- r * s⁻¹ ∈ Hf(r * s⁻¹)
    -- → r * s⁻¹ * f(r * s⁻¹)⁻¹ ∈ H
    -- ↔ f(r * s⁻¹) * s * r⁻¹ ∈ H, done

-- similar, R * S⁻¹ ⊆ U * R should hold,
-- thus R * ⟨S⟩ ⊆ ⟨U⟩ * R ?
-- R * (S ∪ S⁻¹) ⊆ U * R
-- R * (S ∪ S⁻¹) * (S ∪ S⁻¹) * ... (S ∪ S⁻¹)
-- ⊆ U * R * (S ∪ S⁻¹) * ... (S ∪ S⁻¹)
-- ⊆ U * U * R * ... * (S ∪ S⁻¹)
-- ⊆ U * U * ... * U * R
-- ⊆ ⟨U⟩ * R
-- wow, DirectedSystem?
-- ⟨S⟩ = lim n → ∞, (S ∪ S⁻¹)^n
-- if R * (S ∪ S⁻¹) ⊆ U * R ⊆ (U ∪ U⁻¹) * R
-- then R * (S ∪ S⁻¹) ^ n ⊆ (U ∪ U⁻¹) ^ n * R
-- then R * lim n → ∞, (S ∪ S⁻¹) ^ n ⊆ lim n → ∞, (U ∪ U⁻¹) ^ n * R
-- then R * ⟨S⟩ ⊆ ⟨U⟩ * R
theorem my_closure_mul_image_mul_eq_top_what_does_U_mean
  {G : Type u} [Group G] {H : Subgroup G} {R S : Set G}
  (hR : IsComplement H R) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
  R * S ⊆ ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) * R := by
  let f : G → R := hR.toRightFun
  let U : Set G := (R * S).image fun g => g * (f g : G)⁻¹
  change R * S ⊆ U * R
  rintro - ⟨r, hr, s, hs, rfl⟩
  change r * s ∈ U * R
  rw [show r * s = (r * s * (f (r * s) : G)⁻¹) * f (r * s) by group]
  refine Set.mul_mem_mul ⟨r * s,Set.mul_mem_mul hr hs , rfl⟩ (f (r * s)).2

theorem my_closure_mul_image_eq
  {G : Type u} [Group G] {H : Subgroup G} {R S : Set G}
  (hR : IsComplement H R) (hR1 : (1 : G) ∈ R) (hS : closure S = ⊤) :
  closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) = H := by
  -- indeed, H * R = G, thus may be ⟨U⟩ * R = G can imply ⟨U⟩ = H
  have hU : closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹) ≤ H := by
    -- ⟨U⟩ ≤ H
    rw [closure_le]
    -- U ≤ H
    rintro - ⟨g, -, rfl⟩
    -- recall U = { r * s * f(r * s)⁻¹ | r ∈ R, s ∈ S} = { g * f(g)⁻¹ | g ∈ R * S}
    -- show ∀ g ∈ R * S, g * f(g)⁻¹ ∈ H
    exact hR.mul_inv_toRightFun_mem g
    -- by def g ∈ Hf(g) → g * f(g)⁻¹ ∈ H
  -- ⟨U⟩ = H
  refine le_antisymm hU fun h hh => ?_
  -- we have ⟨U⟩ ≤ H, now show H ≤ ⟨U⟩ i.e. ∀ h ∈ H, h ∈ ⟨U⟩
  obtain ⟨g, hg, r, hr, rfl⟩ :=
    show h ∈ _ from eq_top_iff.mp (closure_mul_image_mul_eq_top hR hR1 hS) (mem_top h)
  -- previous thm, we show ⟨U⟩ * R = G
  -- thus h ∈ H ⊆ G = ⟨U⟩ * R
  -- → h = g * r for some g ∈ ⟨G⟩, r ∈ R
  -- show g * r ∈ ⟨U⟩
  suffices (⟨r, hr⟩ : R) = (⟨1, hR1⟩ : R) by
    -- claim r = 1, if claim hold then g * r = g * 1 = g ∈ ⟨U⟩
    simpa only [show r = 1 from Subtype.ext_iff.mp this, mul_one]
  /-
  right coset of H form a parition of G
  → coset are disjoint
  → ∀ g ∈ G, if g ∈ Hr₁, g ∈ Hr₂ then r₁ = r₂
  apply to g := r, r₁ := 1, r₂ := r
  show
  1. r ∈ Hr i.e. r * r⁻¹ ∈ H
  2. r ∈ H1 i.e. r * 1⁻¹ ∈ H
  -/
  apply (isComplement_iff_existsUnique_mul_inv_mem.mp hR r).unique
  · -- r * r⁻¹ = 1 ∈ H
    rw [Subtype.coe_mk, mul_inv_cancel]
    exact H.one_mem
  · -- r * 1⁻¹ = r = g⁻¹ * g * r
    -- recall h = g * r ∈ H, and g ∈ ⟨U⟩ ⊆ H
    -- this g⁻¹ * g * r ∈ H
    rw [Subtype.coe_mk, inv_one, mul_one]
    exact (H.mul_mem_cancel_left (hU hg)).mp hh

#check map_subtype_le_map_subtype -- map (↑) K₁ ≤ map (↑) K₂ in Subgroup H ↔ K₁ ≤ K₂ in Subgroup G
#check (subtype_injective _).eq_iff -- map (↑) K₁ = map (↑) K₂ in Subgroup H ↔ K₁ = K₂ in Subgroup G
example {G : Type u} [Group G] (H : Subgroup G) : map H.subtype ⊤ = H := by ext x; simp
example {G : Type u} [Group G] (H : Subgroup G) : map H.subtype ⊤ = H := by
  ext x
  calc x ∈ map H.subtype ⊤
    _ ↔ ∃ y ∈ (⊤ : Subgroup H), ↑y = x := Iff.rfl
    _ ↔ ∃ y : H, y ∈ ⊤ ∧ ↑y = x := Iff.rfl
    _ ↔ ∃ y : H, True ∧ ↑y = x := Iff.rfl
    _ ↔ ∃ y : H, ↑y = x := by simp_rw [true_and]
    _ ↔ x ∈ H := by
      constructor
      . rintro ⟨y, rfl⟩
        exact y.2
      . intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
example {G : Type u} [Group G] (H : Subgroup G) : map H.subtype ⊤ = H := by
  rw [← MonoidHom.range_eq_map, H.range_subtype]

#check closure_mul_image_eq_top
theorem my_closure_mul_image_eq_top
  {G : Type u} [Group G] {H : Subgroup G} {R S : Set G}
  (hR : IsComplement H R) (hR1 : (1 : G) ∈ R)
  (hS : closure S = ⊤) : closure ((R * S).image fun g =>
    ⟨g * (hR.toRightFun g : G)⁻¹, hR.mul_inv_toRightFun_mem g⟩ : Set H) = ⊤ := by
  rw [
    -- goal : ⟨U⟩ = H but in H
    -- true goal : ⟨U'⟩ = ⊤
    -- where map (↑) (U' : Set H) = (U : Set G), map (↑) (⊤ : Subgroup H) = (H : Subgroup G)
    eq_top_iff,
    -- ⊤ ≤ ⟨U'⟩ in Subgroup H
    ← map_subtype_le_map_subtype,
    -- map (↑) ⊤ ≤ map (↑) ⟨U'⟩ in Subgroup G
    MonoidHom.map_closure,
    -- map (↑) ⊤ ≤ ⟨(↑) '' U'⟩ in Subgroup G
    Set.image_image
    -- definitial equal to
    -- map (↑) ⊤ ≤ ⟨U⟩ in Subgroup G
  ]
  -- change map (H.subtype : ↥H →* G) ⊤
  --   ≤ closure ((R * S).image fun g => g * (hR.toRightFun g : G)⁻¹)

  -- we have map (↑) ⊤ ≤ H and H = ⟨U⟩
  -- thus map (↑) ⊤ ≤ ⟨U⟩ done
  exact (map_subtype_le ⊤).trans (ge_of_eq (closure_mul_image_eq hR hR1 hS))

#check closure_mul_image_eq_top'
theorem my_closure_mul_image_eq_top'
    {G : Type u} [Group G] {H : Subgroup G} [DecidableEq G] {R S : Finset G}
    (hR : IsComplement (H : Set G) R) (hR1 : (1 : G) ∈ R)
    (hS : closure (S : Set G) = ⊤) :
    closure (((R * S).image fun g => ⟨_, hR.mul_inv_toRightFun_mem g⟩ : Finset H) : Set H) = ⊤ := by
  rw [Finset.coe_image, Finset.coe_mul] -- R S are finset version
  -- R is finite mean H is finite index, S is finite mean G is FG
  exact closure_mul_image_eq_top hR hR1 hS


#check exists_finset_card_le_mul
-- #print axioms exists_finset_card_le_mul
theorem my_exists_finset_card_le_mul
  {G : Type u} [Group G] (H : Subgroup G)
  [FiniteIndex H] {S : Finset G} (hS : closure (S : Set G) = ⊤) :
    ∃ T : Finset H, #T ≤ H.index * #S ∧ closure (T : Set H) = ⊤ := by
  letI := H.fintypeQuotientOfFiniteIndex
  -- by def, H is finite index → G / H is finite type
  haveI : DecidableEq G := Classical.decEq G
  -- need for closure_mul_image_eq_top'
  obtain ⟨R₀, hR, hR1⟩ := H.exists_isComplement_right 1
  -- for any g ∈ G, we can pick a representatives R of right cosets of H, s.t. g ∈ R
  -- so let R₀ be a representation of right cosets of H
  -- and 1 ∈ R₀
  -- set_option trace.Meta.synthInstance true in
  haveI : Fintype R₀ := Fintype.ofEquiv _ hR.rightQuotientEquiv
  -- we know set of right cosets equiv to representatives i.e. right cosets ≃ R₀
  -- since G / H is finite, lean auto infer that right cosets is finite
  -- so R₀ is finite
  let R : Finset G := Set.toFinset R₀
  -- R = ⟨R₀, R₀ is finite⟩ is a finset
  replace hR : IsComplement (H : Set G) R := by rwa [Set.coe_toFinset]
  replace hR1 : (1 : G) ∈ R := by rwa [Set.mem_toFinset]
  -- of cuz, 1 ∈ R, ↑R is a representatives of right cosets of H
  refine ⟨_, ?_, closure_mul_image_eq_top' hR hR1 hS⟩
  -- use T := U, prove 1. #T ≤ H.index * #S, 2. closure ↑T = ⊤
  -- 2. just closure_mul_image_eq_top', we aleady proved
  -- notice we write T := _, since it can be inferred by prove 2.
  -- show #T ≤ H.index * #S
  calc
    _ ≤ #(R * S) := Finset.card_image_le
    -- #T = #((fun g ↦ g * f(g)⁻¹) '' R * S) ≤ #(R * S)
    _ ≤ #R * #S := Finset.card_mul_le
    -- #T ≤ #(R * S) ≤ #R * #S
    _ = H.index * S.card := congr_arg (· * S.card) ?_
    -- #T ≤ #R * #S = H.index * S.card
    -- since #S is def eq to S.card
    -- suffiecs to show #R = H.index
  calc
    #R = Fintype.card R := (Fintype.card_coe R).symm
    -- R is finset coe to a type ↥R with fintype
    -- #R = |↥R|
    _ = _ := (Fintype.card_congr hR.rightQuotientEquiv).symm
    -- again right cosets ≃ R thus
    -- #R = |↥R| = |right cosets|
    _ = Fintype.card (G ⧸ H) := QuotientGroup.card_quotient_rightRel H
    -- right cosets of H ≃ left cosets of H = G / H
    -- #R = |G / H|
    _ = H.index := by rw [index_eq_card, Nat.card_eq_fintype_card]
    -- by def, #R = |G / H| = H.index. done



#check fg_of_index_ne_zero
theorem my_fg_of_index_ne_zero
  {G : Type u} [Group G] (H : Subgroup G)
  [hG : Group.FG G] [FiniteIndex H] : Group.FG H := by
  obtain ⟨S, hS⟩ := hG.1
  -- G is FG → ∃ S finset G s.t. G = ⟨S⟩
  obtain ⟨T, -, hT⟩ := exists_finset_card_le_mul H hS
  -- we showed ∃ T finset, s.t. 1. #T ≤ H.index * #S, 2. closure ↑T = ⊤
  exact ⟨⟨T, hT⟩⟩
  -- just use 2.

-- set_option trace.Meta.synthInstance true in
theorem my_rank_le_index_mul_rank
  {G : Type u} [Group G] (H : Subgroup G)
  [hG : Group.FG G] [FiniteIndex H] :
    Group.rank H ≤ H.index * Group.rank G := by
  -- Group.rank H appear in goal, lean auto infer Group.FG H instance
  haveI := H.fg_of_index_ne_zero -- no need
  obtain ⟨S, hS₀, hS⟩ := Group.rank_spec G
  -- pick S : finset G s.t. #S = rank G, G = ⟨S⟩
  obtain ⟨T, hT₀, hT⟩ := exists_finset_card_le_mul H hS
  -- ∃ T finset, s.t. 1. #T ≤ H.index * #S, 2. closure ↑T = ⊤
  calc
    Group.rank H ≤ #T := Group.rank_le hT
    -- T is a generators of H → rank H ≤ #T
    _ ≤ H.index * #S := hT₀
    -- #T ≤ H.index * #S
    _ = H.index * Group.rank G := congr_arg (H.index * ·) hS₀
    -- #S = rank G


#check card_commutator_dvd_index_center_pow
/-- If `G` has `n` commutators `[g₁, g₂]`, then `|G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n + 1)`,
where `G'` denotes the commutator of `G`. -/
theorem my_card_commutator_dvd_index_center_pow
  (G : Type u) [Group G] [Finite (commutatorSet G)] :
    Nat.card (_root_.commutator G) ∣
      (center G).index ^ ((center G).index * Nat.card (commutatorSet G) + 1) := by
  -- First handle the case when `Z(G)` has infinite index and `[G : Z(G)]` is defined to be `0`
  by_cases hG : (center G).index = 0
  · simp_rw [hG, zero_mul, zero_add, pow_one, dvd_zero] -- # key : ∀ n : ℕ, n | 0
  haveI : FiniteIndex (center G) := ⟨hG⟩
  -- Rewrite as `|Z(G) ∩ G'| * [G' : Z(G) ∩ G'] ∣ [G : Z(G)] ^ ([G : Z(G)] * n) * [G : Z(G)]`
  rw [
    --# goal : |G'| | [G : Z(G)] ^ ([G : Z(G)] * n + 1)
    --# let Z(G) ∩ G' as a subgroup of G'
    --# we have |G'| = |Z(G) ∩ G'| * [G' : Z(G) ∩ G']
    ← ((center G).subgroupOf (_root_.commutator G)).card_mul_index,
    --#  |Z(G) ∩ G'| * [G' : Z(G) ∩ G'] | [G : Z(G)] ^ ([G : Z(G)] * n + 1)
    pow_succ
    --#  |Z(G) ∩ G'| * [G' : Z(G) ∩ G'] | [G : Z(G)] ^ ([G : Z(G)] * n) * [G : Z(G)]
  ]
  -- We have `h1 : [G' : Z(G) ∩ G'] ∣ [G : Z(G)]`
  /-
  #      G
  #      |
  #     GZ(G)
  #    /   \
  #  G'    Z(G)
  #    \   /
  #   G' ∩ Z(G)
  #
  # recall 2-iso thm : given two subgroups H and N of a group G, where N is normal
  # defines an isomorphism between H/(H ∩ N) and (HN)/N.
  # since Z(G) is normal, by 2-iso thm
  #    G' / (G' ∩ Z(G)) ≃ G'Z(G) / Z(G)
  # → [G' : G' ∩ Z(G)] = [G'Z(G) / Z(G)] | [G : Z(G)]
  -/
  have h1 := relindex_dvd_index_of_normal (center G) (_root_.commutator G)
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n)`
  refine mul_dvd_mul ?_ h1
  --# h1 : [G' : Z(G) ∩ G'] ∣ [G : Z(G)], hG : [G : Z(G)] is finite
  -- We know that `[G' : Z(G) ∩ G'] < ∞` by `h1` and `hG`
  haveI : FiniteIndex ((center G).subgroupOf (_root_.commutator G)) :=
    ⟨ne_zero_of_dvd_ne_zero hG h1⟩
  --# G' is generated by commutatorSet G, and by assumption commutatorSet G is finite
  --# so G' is FG
  --# now Z(G) ∩ G' is a finite index subgroup of G'
  --# by Schreier's lemma, we have :
  -- We have `h2 : rank (Z(G) ∩ G') ≤ [G' : Z(G) ∩ G'] * rank G'` by Schreier's lemma
  have h2 := rank_le_index_mul_rank ((center G).subgroupOf (_root_.commutator G))
  --# h1 : [G' : Z(G) ∩ G'] ∣ [G : Z(G)] thus [G' : Z(G) ∩ G'] ≤ [G : Z(G)] use [G : Z(G)] ≠ 0
  --# by def, G' = ⟨commutatorSet G⟩ thus rank G' ≤ |commutatorSet G| = n
  -- We have `h3 : [G' : Z(G) ∩ G'] * rank G' ≤ [G : Z(G)] * n` by `h1` and `rank G' ≤ n`
  have h3 := Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hG) h1) (rank_commutator_le_card G)
  --# old goal : |Z(G) ∩ G'| ∣ [G : Z(G)] ^ ([G : Z(G)] * n)
  --# h2 + h3 → rank (Z(G) ∩ G') ≤ [G' : Z(G) ∩ G'] * rank G' ≤ [G : Z(G)] * n
  --# by pow_dvd_pow,
  -- So we can reduce to proving `|Z(G) ∩ G'| ∣ [G : Z(G)] ^ rank (Z(G) ∩ G')`
  refine dvd_trans ?_ (pow_dvd_pow (center G).index (h2.trans h3))
  --# notice Z(G) ∩ G' is a FG abelian group
  -- `Z(G) ∩ G'` is abelian, so it enough to prove that `g ^ [G : Z(G)] = 1` for `g ∈ Z(G) ∩ G'`
  apply card_dvd_exponent_pow_rank'
  intro g
  --# by transfer construction, we have a homo from G to abelian group, transfer : G →* Z(G)
  --# for g ∈ Z(G) ∩ G' ≤ G', g is a product of commutators, thus transfer(g) = 1
  -- `Z(G)` is abelian, so `g ∈ Z(G) ∩ G' ≤ G' ≤ ker (transfer : G → Z(G))`
  have := Abelianization.commutator_subset_ker (MonoidHom.transferCenterPow G) g.1.2
  -- `transfer g` is defeq to `g ^ [G : Z(G)]`, so we are done
  simpa only [MonoidHom.mem_ker, Subtype.ext_iff] using this

/-
key :
Z(G) ∩ G' is FG
Z(G) ∩ G' is abelian
Z(G) ∩ G' ≤ G' ≤ ker (transfer : G → Z(G))
exp (Z(G) ∩ G') ≤ [G : Z(G)]
rank (Z(G) ∩ G') ≤ [G' : Z(G) ∩ G'] * rank G'
|Z(G) ∩ G'| ≤ exp (Z(G) ∩ G') ^ rank (Z(G) ∩ G')

|G'|
= |Z(G) ∩ G'| * [G' : Z(G) ∩ G']
≤ exp (Z(G) ∩ G') ^ rank (Z(G) ∩ G') * [G' : Z(G) ∩ G']
≤ [G : Z(G)] ^ ([G' : Z(G) ∩ G'] * rank G') * [G' : Z(G) ∩ G']
≤ [G : Z(G)] ^ ([G' : Z(G) ∩ G'] * n) * [G' : Z(G) ∩ G']
≤ [G : Z(G)] ^ ([G : Z(G)] * n) * [G : Z(G)]
≤ [G : Z(G)] ^ ([G : Z(G)] * n + 1)
-/



/-- A bound for the size of the commutator subgroup in terms of the number of commutators. -/
def my_cardCommutatorBound (n : ℕ) :=
  (n ^ (2 * n)) ^ (n ^ (2 * n + 1) + 1)



#check card_commutator_le_of_finite_commutatorSet
/-- A theorem of Schur: The size of the commutator subgroup is bounded in terms of the number of
  commutators. -/
theorem my_card_commutator_le_of_finite_commutatorSet
  (G : Type u) [Group G] [Finite (commutatorSet G)] :
    Nat.card (_root_.commutator G) ≤ cardCommutatorBound (Nat.card (commutatorSet G)) := by
  -- goal : |G'| ≤ (n ^ (2 * n)) ^ (n ^ (2 * n + 1) + 1), where n = |commutatorSet G|
  have h1 := index_center_le_pow (closureCommutatorRepresentatives G)
  /-
  recall commutatorSet G := {⟦g₁, g₂⟧ | g₁, g₂ ∈ G}
  def choose : commutatorSet G → G × G := fun ⟦g₁, g₂⟧ ↦ (g₁, g₂)
  def commutatorRepresentatives : Set (G × G) := choose '' commutatorSet G
  def closureCommutatorRepresentatives G  : Subgroup G
    := ⟨π₁ '' commutatorRepresentatives ∪ π₂ '' commutatorRepresentatives⟩
  let H := closureCommutatorRepresentatives G
  lean infer [Finite ↑(commutatorSet H)] [Group.FG H]
  see `instFiniteElemSubtypeMemSubgroupClosureCommutatorRepresentativesCommutatorSet`
  and `closureCommutatorRepresentatives_fg`
  ok i don't know what is index_center_le_pow
  and quotientCenterEmbedding seen cool
  anyway, h1 : [H : Z(H)] ≤ m ^ rank H, where m = |commutatorSet H|
  and by auto infer, commutatorSet H is finite, H is FG
  -/
  have h2 := card_commutator_dvd_index_center_pow (closureCommutatorRepresentatives G)
  /-
  by previous thm, since commutatorSet H is finite, we have
    h2 : |H'| | [H : Z(H)] ^ ([H : Z(H)] * m + 1)
  -/
  rw [card_commutatorSet_closureCommutatorRepresentatives] at h1 h2
  rw [card_commutator_closureCommutatorRepresentatives] at h2
  -- magically, m = n, and |H'| = |G'|, so
  -- h1 : [H : Z(H)] ≤ n ^ rank H
  -- h2 : |G'| | [H : Z(H)] ^ ([H : Z(H)] * n + 1)
  replace h1 :=
    h1.trans
      (Nat.pow_le_pow_right Finite.card_pos (rank_closureCommutatorRepresentatives_le G))
  -- again, magically, rank H ≤ 2 * n, so
  -- h1 : [H : Z(H)] ≤ n ^ rank H ≤ n ^ (2 * n)
  -- → h1 : [H : Z(H)] ≤ n ^ (2 * n)
  -- notice indeed n > 0, since n = |commutatorSet G| and commutatorSet G is nonempty
  replace h2 := h2.trans (pow_dvd_pow _ (add_le_add_right (mul_le_mul_right' h1 _) 1))
  -- h2 : |G'| | [H : Z(H)] ^ ([H : Z(H)] * n + 1) | [H : Z(H)] ^ (n ^ (2 * n) * n + 1)
  -- → h2 : |G'| | [H : Z(H)] ^ (n ^ (2 * n) * n + 1)
  rw [← pow_succ] at h2
  -- h2 : |G'| | [H : Z(H)] ^ (n ^ (2 * n) * n + 1) = [H : Z(H)] ^ (n ^ (2 * n + 1) + 1)
  -- → h2 : |G'| | [H : Z(H)] ^ (n ^ (2 * n + 1) + 1)
  refine (Nat.le_of_dvd ?_ h2).trans (Nat.pow_le_pow_left h1 _)
  -- h2 : |G'| | [H : Z(H)] ^ (n ^ (2 * n + 1) + 1)
  -- → |G'| ≤ [H : Z(H)] ^ (n ^ (2 * n + 1) + 1) ≤ (n ^ (2 * n)) ^ (n ^ (2 * n + 1) + 1)
  -- a | b imply a ≤ b need b > 0
  -- to check [H : Z(H)] ^ (n ^ (2 * n + 1) + 1) > 0
  exact pow_pos (Nat.pos_of_ne_zero FiniteIndex.index_ne_zero) _
  -- since Z(H) has finite index, thus [H : Z(H)] > 0
  -- and so [H : Z(H)] ^ _ > 0, done

#check rank_closureCommutatorRepresentatives_le
#check commutatorRepresentatives
#check closureCommutatorRepresentatives
/-
rank (closureCommutatorRepresentatives)
= rank ⟨π₁ '' commutatorRepresentatives ∪ π₂ '' commutatorRepresentatives⟩
≤ |π₁ '' commutatorRepresentatives ∪ π₂ '' commutatorRepresentatives|
≤ |π₁ '' commutatorRepresentatives| + |π₂ '' commutatorRepresentatives|
≤ |commutatorRepresentatives| + |commutatorRepresentatives|
= |choose '' commutatorSet| + |choose '' commutatorSet|
= |commutatorSet| + |commutatorSet|
= 2 * |commutatorSet|
-/


#check index_center_le_pow
/-
key :
[G : Z(G)] ≤ n ^ rank G
[H : Z(H)] ≤ m ^ rank H
H := closureCommutatorRepresentatives G
rank H ≤ 2 * n
|H'| = |G'|
n = m, where m = |commutatorSet H|


|G'|
= |H'|
≤ [H : Z(H)] ^ ([H : Z(H)] * m + 1)
≤ (m ^ rank H) ^ (m ^ rank H * m + 1)
≤ (n ^ rank H) ^ (n ^ rank H * n + 1)
≤ (n ^ 2 * n) ^ (n ^ 2 * n * n + 1)
≤ (n ^ 2 * n) ^ (n ^ (2 * n + 1) + 1)
-/
