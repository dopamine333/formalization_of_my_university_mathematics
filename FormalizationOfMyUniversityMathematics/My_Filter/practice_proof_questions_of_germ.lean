import Mathlib.Order.Filter.Germ.Basic

open Filter

variable {α β γ : Type*} {l : Filter α}

/-! ### 1. Germ as a quotient -/

/-- **Ex 1.1**
Show that two functions represent the same germ *iff* they are eventually equal. -/
example (f g : α → β) :
    ((f : Germ l β) = g) ↔ (f =ᶠ[l] g) := by
  -- Hint: `Filter.Germ.coe_eq`
  exact @Quotient.eq (α → β) (germSetoid l β) f g
  -- exact Quotient.eq

/-! ### 2. Coercions & constants -/

/-- **Ex 2.1**
Prove that the germ of a constant function equals the constant germ. -/
example (b : β) : (fun _ : α ↦ b : Germ l β) = (↑b : Germ l β) := by
  -- `rfl` after unfolding is enough
  rfl

/-! ### 3. Constant germs -/

/-- **Ex 3.1**
Show that if a germ is constant then mapping any function over it is still constant. -/
example {f : Germ l β} (h : f.IsConstant) (G : β → γ) :
    (f.map G).IsConstant := by
  -- Use `Filter.Germ.isConstant_comp`
  revert f
  apply Quotient.ind
  intro f h
  change ∃ b, f =ᶠ[l] fun x ↦ b at h
  obtain ⟨b, hb⟩ := h
  change ∃ b, (G ∘ f) =ᶠ[l] fun x ↦ b
  use G b
  change {x | f x = b} ∈ l at hb
  have : {x | f x = b} ⊆ {x | (G ∘ f) x = G b} := by
    intro x hx
    simp at hx ⊢
    rw [hx]
  change {x | (G ∘ f) x = G b} ∈ l
  exact mem_of_superset hb this

example {f : Germ l β} (h : f.IsConstant) (G : β → γ) :
    (f.map G).IsConstant := by
  -- Use `Filter.Germ.isConstant_comp`
  induction' f using Quotient.ind with f
  obtain ⟨b, hb⟩ : ∃ b : β, {x | f x = b} ∈ l  := h
  have : {x | f x = b} ⊆ {x | (G ∘ f) x = G b} := by
    intro x hx; simp at hx ⊢; rw [hx]
  have := l.mem_of_superset hb this
  exact ⟨G b, this⟩

example {f : Germ l β} (h : f.IsConstant) (G : β → γ) :
    (f.map G).IsConstant := by
  -- Use `Filter.Germ.isConstant_comp`
    induction' f using Germ.inductionOn with f
    apply Germ.isConstant_comp h


/-! ### 4. Functoriality (`map`, `map₂`) -/

/-- **Ex 4.1**
Verify that `map id` is the identity on germs. -/
example : (Filter.Germ.map (@id β)) = (id : Germ l β → Germ l β) := by
  simp

example : (Filter.Germ.map (@id β)) = (id : Germ l β → Germ l β) := by
  ext f
  induction' f using Germ.inductionOn with f
  rfl

example : (Filter.Germ.map (@id β)) = (id : Germ l β → Germ l β) := by
  ext f
  induction' f using Germ.inductionOn with f
  change ((id ∘ f) : Germ l β) = f
  rfl

/-! ### 5. Convergence and composition -/

/-- **Ex 5.1**
If `g : γ → α` tends to `l` and `f` is a constant germ, show that `f ∘ g` is still that constant germ. -/
example (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    ((↑b : Germ l β).compTendsto g hg) = (↑b) := by
  simp [Filter.Germ.const_compTendsto]  -- then `rfl`

example (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    ((↑b : Germ l β).compTendsto g hg) = (↑b) := by
  change ((fun _ ↦ b) ∘ g : Germ lc β) = b
  rfl

example (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    ((↑b : Germ l β).compTendsto g hg) = (↑b) := by
  -- change ((fun _ ↦ b) ∘ g : Germ lc β) = b
  rfl

/-! ### 6. LiftPred / LiftRel -/

/-- **Ex 6.1**
Suppose `p` is true of a value `x`.  Show it holds of the constant germ `↑x`. -/
example (p : β → Prop) {x : β} (hx : p x) :
    Filter.Germ.LiftPred p (↑x : Germ l β) := by
  -- `Filter.Germ.liftPred_const`
  change {y | p x} ∈ l
  simp_rw [hx]
  exact l.univ_mem

/-! ### 7. Order on germs -/

variable [LE β] [OrderBot β]
/-- **Ex 7.1**
With a preorder on `β`, prove `bot ≤ f` for any germ `f`. -/
example (f : Germ l β) : (⊥ : Germ l β) ≤ f := by
  -- Use the instance `Filter.Germ.instOrderBot`
  induction' f using Germ.inductionOn with f
  change {x | ⊥ ≤ f x} ∈ l
  simp_rw [bot_le]
  exact l.univ_mem

/-! ### 8. Algebraic structure transfer -/

-- open scoped BigOperators
variable [AddCommMonoid β]
/-- **Ex 8.1**
(Commutative addition)
Assume `β` is an additive commutative monoid.
Show that addition of germs is commutative. -/
example (f g : Germ l β) : f + g = g + f := by
  -- Lean already knows this (`instAddCommMonoid`).  Just use `simp`
  rw [add_comm]
