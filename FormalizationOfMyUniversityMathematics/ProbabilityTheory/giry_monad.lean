import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory
open scoped ENNReal

#check Measure.bind_apply
#check Measure.dirac_apply

/-
let P X := the set of all probability measures on X
dice : P (Fin 6) := do
  let x ← (Fin 6).rand
  return x + 1
#eval dice {1,2,3,4,5,6}
-/

/-
define a monad on Measure
-/

noncomputable def dice : Measure ℕ := ∑ i ∈ Finset.range 6, (1 / (6 : ENNReal)) • Measure.dirac (i + 1)
example : dice {1,2,3,4,5,6} = 1 := by
  simp [dice, Finset.sum_range_succ]
  ring
  apply ENNReal.inv_mul_cancel <;> simp

example : dice {2} = 1 / 6 := by
  simp [dice, Finset.sum_range_succ]

example : ∀ i ∈ Finset.range 6, dice {i + 1} = 1 / 6 := by
  intro x hx
  simp [dice, Finset.sum_range_succ]
  fin_cases hx <;> simp

example : ∀ i ∉ Finset.range 6, dice {i + 1} = 0 := by
  intro x hx
  simp [dice]
  simp at hx
  intros
  linarith

noncomputable def roll_two_dices : Measure ℕ :=
  dice.bind (fun x =>
  dice.bind (fun y =>
    Measure.dirac (x + y)
  )
  )

theorem lintegral_dice {f : ℕ → ENNReal} :
  ∫⁻ a, f a ∂ dice = (1 / 6 : ENNReal) * ∑ i ∈ Finset.range 6, f (i + 1) := by
  simp [dice, lintegral_finset_sum_measure, lintegral_smul_measure, Finset.mul_sum]

example : roll_two_dices {2} = 1 / 36 := by
  unfold roll_two_dices
  rw [Measure.bind_apply,
      lintegral_congr fun x ↦ Measure.bind_apply _ _]
  simp_rw [lintegral_dice, Measure.dirac_apply]
  simp [Finset.sum_range_succ]
  rw [← ENNReal.mul_inv]
  norm_num

  all_goals try simp

  intro x
  apply Measurable.aemeasurable
  exact fun ⦃t⦄ a ↦ trivial

  apply Measurable.aemeasurable
  exact fun ⦃t⦄ a ↦ trivial

  -- since Nat.instMeasurableSpace is defined as ⊤
  -- so every function from Nat to ENNReal is measurable

example : roll_two_dices {7} = 6 / 36 := by
  unfold roll_two_dices
  rw [Measure.bind_apply,
      lintegral_congr fun x ↦ Measure.bind_apply _ _]
  simp_rw [lintegral_dice, Measure.dirac_apply]
  simp [Finset.sum_range_succ]
  ring
  rw [← ENNReal.inv_pow, mul_comm, div_eq_mul_inv]
  norm_num

  all_goals try simp

  intro x
  apply Measurable.aemeasurable
  exact fun ⦃t⦄ a ↦ trivial

  apply Measurable.aemeasurable
  exact fun ⦃t⦄ a ↦ trivial


/-

let P X := the set of all probability measures on X
pure : X → P X := fun x ↦ dirac x
bind : P X → (X → P Y) → P Y :=
  fun μ f ↦ (fun A ↦ ∫ x ∈ X, f x A ∂μ)
(notice f : X → P Y, f x ∈ P Y, f x A ∈ ℝ≥0∞,
 dirac x := A ↦ if x ∈ A then 1 else 0)

dice : P ℕ := ∑ i ∈ {1,2,..,6}, 1/6 * dirac i
(notice, for f : ℕ → ℝ,
  ∫ i ∈ ℕ, f i ∂dice = 1/6 * ∑ i ∈ {1,2,..,6}, f i)
  ∫ i ∈ ℕ, f i ∂(dirac j) = f j
roll_two_dices : P ℕ := do
  x ← dice
  y ← dice
  return x + y

expand do notation

roll_two_dices : P ℕ :=
  bind dice (fun x ↦
  bind dice (fun y ↦
  pure (x + y)))

let A be a measurable set of ℕ, then
roll_two_dices A
= bind dice (fun x ↦
  bind dice (fun y ↦
  pure (x + y))) A
= ∫ x ∈ ℕ, (bind dice (fun y ↦ pure (x + y))) A ∂dice
= ∫ x ∈ ℕ, (∫ y ∈ ℕ, pure (x + y) A ∂dice) ∂dice
= ∫ x ∈ ℕ, (∫ y ∈ ℕ, dirac (x + y) A ∂dice) ∂dice
= ∑ x ∈ {1,2,..,6}, 1/6 * (∑ y ∈ {1,2,..,6}, 1/6 * (dirac (x + y) A))
= ∑ x ∈ {1,2,..,6}, ∑ y ∈ {1,2,..,6}, 1/36 * (dirac (x + y) A)
= ∑ x ∈ {1,2,..,6}, ∑ y ∈ {1,2,..,6}, 1/36 * (if x + y ∈ A then 1 else 0)

-/

/-
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg


StateT σ m α = σ → m (α × σ)

instance : Monad (StateT σ m) where
  pure (x : α) := fun s => pure (x, s)
  bind (n : StateT σ m α) (f : α → StateT σ m β) := fun s =>
    bind (n s) (fun (a, s') => f a s')

instance : Monad (StateT σ m) where
  pure (x : α) := fun s => pure (x, s)
  bind (n : StateT σ m α) (f : α → StateT σ m β) := fun s => do
    let (a, s') ← n s
    f a s'

State σ α = σ → α × σ
instance : Monad (State σ) where
  pure x := fun s => (x, s)
  bind n f := fun s =>
    let (a, s') := n s
    f a s'

-/

def shuffle (balls box : List ℕ) : List (List ℕ) :=

  let rec aux : StateT (List ℕ × List ℕ) List Unit := do
    let (balls, _) ← get
    for _ in balls do
      let (balls, box) ← get
      let ball ← balls
      set (balls.erase ball, box.concat ball)

  (aux (balls, box)).map (fun (_, _, box) ↦ box)

#eval shuffle [1,2,3] []
#print shuffle
#print shuffle.aux

def perm (n : ℕ) : List (List ℕ) :=
  let rec aux : StateT (List ℕ) List Unit := do
    Nat.forM n (fun _ _ ↦ do
      let box ← get
      let ball ← (List.range n).diff box
      set (box.concat ball))
  (aux []).map (fun (_, box) ↦ box)

#eval perm 4
#print perm
#print perm.aux

def perm' (n : ℕ) : List (List ℕ) :=
  let rec aux : StateT (List ℕ) List Unit :=
    Nat.forM n fun _ _ ↦
      bind get fun box ↦
      bind (liftM ((List.range n).diff box)) fun ball ↦
      set (box.concat ball)
  (aux []).map (fun (_, box) ↦ box)

#eval perm' 4
#print perm'.aux

def perm'' (n : ℕ) : List (List ℕ) := do
  let mut box := []
  for _ in [:n] do
    let ball ← (List.range n).diff box
    box := box.concat ball
  return box

#eval perm'' 2
#print perm''
#check ForInStep

def filp_coin (n : ℕ) : List (List ℕ) :=
  let coin := [0, 1]
  let aux : StateT (List ℕ) List (List ℕ) := do
    for _ in [:n] do
      let toss ← coin
      modify (fun tosses ↦ tosses.concat toss)
    return ← get
  aux.eval []

#eval filp_coin 3
-- [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1],
--  [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]


def filp_coin' (n : ℕ) : List (List ℕ) := do
  let mut tosses := []
  let coin := [0,1]
  for _ in [:n] do
    let toss ← coin
    tosses := tosses.concat toss
  return tosses

#eval filp_coin' 3
#print filp_coin'
#check Lean.Loop

-- theorem filp_coin_self_similarity :
--   let f : List ℕ → List ℕ := fun tosses ↦ tosses.concat 0;
--   Set.InjOn f filp_coin.toFinset.toSet := by sorry

#check liftM
#check MonadLiftT
#synth MonadLiftT List (StateT _ List)
#check instMonadLiftTOfMonadLift
#check MonadLift
#check StateT.instMonadLift

example {σ : Type} (as : List ℕ) :
  (liftM as : StateT σ List ℕ) = fun s ↦ bind as (fun a ↦ pure (a, s)):= rfl

-- α : Type, m : MeasurableSpace α, (α, m)
