import Mathlib.Tactic

namespace Hidden

@[match_pattern]
def foo (a : ℕ) : Nat := a + 2


def double : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | a + 2 => 2 * a + 4

def double' : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | foo a => 2 * a + 4


example : double = double' := rfl


def exists_apply {α : Type} (p : α → Prop) (q : Prop)
  : (∃ x, p x) → (∀ x, p x → q) → q
  | ⟨x, hx⟩ ,h => h x hx


#check exists_or
def exists_or {α : Type} (p q : α → Prop)
  : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | ⟨x, .inl h⟩ => .inl ⟨x, h⟩
  | ⟨x, .inr h⟩ => .inr ⟨x, h⟩

#check SizeOf.sizeOf

inductive Tree
  | leaf : Tree
  | child : Tree → Tree → Tree

#synth SizeOf Tree
#check SizeOf.sizeOf (Tree.child .leaf .leaf)
example : SizeOf.sizeOf (Tree.child .leaf .leaf) = 3 := by decide

notation "o" => Tree.leaf
notation "<" a:arg "," b:arg ">" => Tree.child a b

#check <o,o>
#check <o,<o,o> >
#check <o,< <o,o>,o> >
example : SizeOf.sizeOf <o, o> = 3 := by decide
example : SizeOf.sizeOf o = 1 := by decide
example : SizeOf.sizeOf (fun x ↦ <o, x>) = 0 := by decide
example : SizeOf.sizeOf <o,<o,o> > = 5 := by decide
example : SizeOf.sizeOf <o,< <o,o>,o> > = 7 := by decide

def add' : ℕ → ℕ → ℕ
  | n, 0 => n
  | n, Nat.succ m => add' (Nat.succ n) m

example : add' 3 4 = 7 := rfl

notation a:arg " +' " b:arg => add' a b

theorem add'_zero (n : ℕ) : n +' 0 = n := rfl
theorem add'_succ (n m : ℕ) : n  +' (m.succ) = n.succ +' m := rfl
theorem add'_succ_out (n m : ℕ) : n +' m.succ = (n +' m).succ := by
  induction' m with m hm generalizing n
  . calc n +' (.succ 0)
      _ = n.succ +' 0 := rfl
      _ = n.succ := rfl
      _ = (n +' 0).succ := rfl
  . calc n +' (m + 1).succ
      _ = n.succ +' (m + 1) := rfl
      _ = n.succ +' m.succ := rfl
      _ = (n.succ +' m).succ := hm (n.succ)
      _ = (n +' m.succ).succ := rfl
      _ = (n +' (m + 1)).succ := rfl


theorem add'_succ_out₂ (n m : ℕ) : n +' m.succ = (n +' m).succ := by
  induction' m with m hm generalizing n
  . rfl
  . exact hm (n + 1)

theorem add'_succ_out₃ : ∀ (n m : ℕ), n +' m.succ = (n +' m).succ
  | _, 0 => rfl
  | n, m + 1 => add'_succ_out₃ (n + 1) m

theorem zero_add' : ∀ n : ℕ, 0 +' n = n
  | 0 => rfl
  | n + 1 => by
    calc 0 +' (n + 1)
      _ = (0 + 1) +' n := rfl
      _ = (0 +' n) +' 1 := add'_succ_out _ _
      _ = n +' 1 := by rw [zero_add' n]

theorem zero_add'₂ : ∀ n : ℕ, 0 +' n = n
  | 0 => rfl
  | .succ n => by
    calc 0 +' n.succ
      -- _ = (.succ 0) +' n := rfl
      _ = (0 +' n).succ:= add'_succ_out _ _
      _ = n.succ := congrArg _ (zero_add'₂ n)


def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100

def fibFast_loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := fibFast_loop n; (p.2, p.1 + p.2)

#eval (fibFast_loop 100).2


def fibFast₂ (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2

#eval fibFast₂ 100
#eval (fibFast₂.loop 100).2


variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)
-- example : @Nat.below C = C := rfl
#reduce @Nat.below C (3 : Nat)
#reduce (@Nat.below C (3 : Nat))

-- #eval @Nat.below C (3 : Nat)
#reduce (2 + 1) + (1 + 1)
#eval (2 + 1) + (1 + 1)
#check (@Nat.brecOn C : (m : Nat) → ((n : Nat) → @Nat.below C n → C n) → C m)


def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- Slow:
-- #eval fib 28
-- Fast:
#reduce fib 28
#print fib
#print add'


def my_repeat {α : Type} : ℕ → α → List α
  | n, a =>
    let rec loop : ℕ → List α → List α
      | 0, as => as
      | m + 1, as => loop m (a::as)
    loop n []

#reduce my_repeat 3 5
#reduce my_repeat.loop 3 5 [1,2,3]

#print my_repeat
#print my_repeat.loop

theorem my_repeat_length {α : Type} :
  ∀ n : ℕ, ∀ a : α, (my_repeat n a).length = n := by
  let rec loop : ∀ m : ℕ, ∀ b : α, ∀ bs : List α,
    (my_repeat.loop b m bs).length = (my_repeat.loop b 0 bs).length + m
    | 0, b, bs => rfl
    | m + 1, b, bs => by
      calc (my_repeat.loop b (m + 1) bs).length
        _ = (my_repeat.loop b m (b::bs)).length := rfl
        _ = (my_repeat.loop b 0 (b::bs)).length + m := loop m b (b::bs)
        _ = (b::bs).length + m := rfl
        _ = (bs).length + 1 + m:= rfl
        _ = (my_repeat.loop b 0 bs).length + 1 + m := rfl
        _ = (my_repeat.loop b 0 bs).length + (m + 1) := by ring
  intro n a
  calc (my_repeat n a).length
    _ = (my_repeat.loop a n []).length := rfl
    _ = (my_repeat.loop a 0 []).length + n := loop _ _ _
    _ = 0 + n := rfl
    _ = n := by ring

theorem my_repeat_length₂ {α : Type} (n : ℕ) (a : α)
  : (my_repeat n a).length = n := by
  have loop (m : ℕ) (b : α) (bs : List α)
    : (my_repeat.loop b m bs).length = m + bs.length := by
    induction' m with m hm generalizing bs
    .  symm; apply zero_add
    .  calc (my_repeat.loop b (m + 1) bs).length
        _ = (my_repeat.loop b m (b::bs)).length := rfl
        _ = m + (b::bs).length := hm (b::bs)
        _ = m + (bs.length + 1) := rfl
        _ = (m + 1) + bs.length := by ring
  exact loop n a []
  -- sorry


#check Acc

#check WellFounded ( (. < .) : ℕ → ℕ → Prop)
#check WellFoundedRelation ℕ
#synth WellFoundedRelation ℕ
#check Nat.lt_wfRel
#check WellFounded ( (. ≤ .) : ℕ → ℕ → Prop)
example : ¬ WellFounded ( (. ≤ .) : ℕ → ℕ → Prop) := by
  intro h
  have asymm := WellFounded.asymmetric h
  exact asymm 0 0 .refl .refl


theorem not_refl_of_WellFounded {α : Type} (r : α → α → Prop) (wf : WellFounded r)
  : ∀ a : α, ¬ r a a := by
  intro a
  induction' a using wf.induction with a h'
  intro ha
  exact h' a ha ha

/-
let a : α, to show a ≮ a
assume toward contradiction, let ha : a < a
since < is well founded
we can assume h : ∀ b < a, b ≮ b
apply h to ha, we get a ≮ a, which contradiciton to ha. qed.
-/


theorem my_asymmetric_of_WellFounded {α : Type} (r : α → α → Prop) (wf : WellFounded r)
  : ∀ a b : α, r a b → ¬ r b a := by
  intro a b
  induction' a using wf.induction with a ha generalizing b
  intro hab hba
  exact ha b hba a hba hab

#check Acc.rec
theorem my_asymmetric_of_WellFounded' {α : Type} (r : α → α → Prop) (wf : WellFounded r)
  : ∀ a b : α, r a b → ¬ r b a := by
  intro a
  have acc_a : Acc r a := wf.apply a
  refine Acc.rec ?_ acc_a
  intro a _ h
  intro b hab hba
  exact h b hba a hba hab

theorem my_asymmetric_of_WellFounded''
  {α : Type} (r : α → α → Prop) (wf : WellFounded r)
  : ∀ a b : α, r a b → ¬ r b a
  := fun a ↦ Acc.rec (fun a _ h b hab hba ↦ h b hba a hba hab) (wf.apply a)


/-
let a : α
show ∀ b : α, if a < b then b ≮ a
since < is well founded
we can assume "for all c < a,
  ∀ b : α, if c < b then b ≮ c"
it is equivalent to "for all c < a,
  ∀ d : α, if c < d then d ≮ c" --(*)
now, let b : α with a < b -- (**)
and assume toward contradiction, let b < a
since b < a, by (*), we have
  ∀ d : α, if b < d then d ≮ b
in particular, for a, we have "if b < a then a ≮ b" holds
and since b < a, we get a ≮ b
which contradiction to (**)
qed.
-/

-- noncomputable
-- def f {α : Sort u}
--     (r : α → α → Prop)
--     (h : WellFounded r)
--     (C : α → Sort v)
--     (F : (x : α) → ((y : α) → r y x → C y) → C x) :
--     (x : α) → C x :=
-- WellFounded.fix h F

#check WellFounded.fix
#check WellFounded.prod_lex


theorem my_WellFounded_prod_lex
  {α : Type u} {β : Type v}
  {ra : α → α → Prop} {rb : β → β → Prop}
  (ha : WellFounded ra) (hb : WellFounded rb)
  : WellFounded (Prod.Lex ra rb) := by
  apply WellFounded.intro
  intro (a,b)
  revert b
  induction' a using ha.induction with a iha
  intro b
  induction' b using hb.induction with b ihb
  apply Acc.intro
  intro (c,d) hcd
  match hcd with
  | .left _ _ hca => exact iha c hca d
  | .right _ hdb  => exact ihb d hdb

theorem my_WellFounded_prod_lex'
  {α : Type u} {β : Type v}
  {ra : α → α → Prop} {rb : β → β → Prop}
  (ha : WellFounded ra) (hb : WellFounded rb)
  : WellFounded (Prod.Lex ra rb) := by
  apply WellFounded.intro
  intro (a,b)
  induction' a using ha.induction with a iha generalizing b
  induction' b using hb.induction with b ihb
  apply Acc.intro
  intro (c,d) hcd
  match hcd with
  | .left _ _ hca => exact iha c hca d
  | .right _ hdb  => exact ihb d hdb


-- ∀ (a,b) , Acc r (a,b)
-- ∀ a, (∀ b, Acc r (a,b))
-- ∀ a, (∀ c < a, (∀ b, Acc r (c,b))) → (∀ b, Acc r (a,b))


-- Acc r (a,b)
-- ∀ (a',b') < (a,b), Acc r (a',b')
-- ∀ (a',b'), a' < a → Acc r (a',b')
-- ∀ b', b' < b → Acc r (a,b')

#check measure

inductive WrapNat
  | wrap : ℕ → WrapNat

def my_div : (x y : WrapNat) → Nat
  | .wrap x, .wrap y =>
  if h : 0 < y ∧ y ≤ x then
    -- have := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    my_div (.wrap (x - y)) (.wrap y) + 1
  else
    0

#print my_div
#print my_div._unary
#print my_div._unary._proof_1

example : 1 = 1 := by
  decreasing_tactic

def div (x y : Nat) : Nat :=
 if h : 0 < y ∧ y ≤ x then
   div (x - y) y + 1
 else
   0

example (x y : Nat) :
    div x y =
    if 0 < y ∧ y ≤ x then
      div (x - y) y + 1
    else 0 := by
   -- unfold occurrence in the left-hand-side of the equation:
  conv => lhs; unfold div
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) :
    div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]


def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    -- have : ((n + 2) / 2) < (n + 2) := by exact Nat.div_lt_self' (n + 1) 0
    natToBin ((n + 2) / 2) ++ [n % 2]

set_option pp.proofs true in
#print natToBin
#print natToBin._proof_2
#eval! natToBin 1234567


def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)


#eval ack 1 0
#eval ack 2 0
#eval ack 3 0
-- #eval ack 4 1
-- #eval ack 5 0

example : ack 5 0 = 65533 := by
  conv => lhs; pattern ack 5 0; unfold ack
  conv => lhs; pattern ack 4 1; unfold ack
  conv => lhs; pattern ack (3 + 1) 0; unfold ack
  conv => lhs; pattern ack 3 1; unfold ack
  conv => lhs; pattern ack (2 + 1) 0; unfold ack
  conv => lhs; pattern ack 2 1; unfold ack
  conv => lhs; pattern ack (1 + 1) 0; unfold ack
  conv => lhs; pattern ack 1 1; unfold ack
  conv => lhs; pattern ack (0 + 1) 0; unfold ack

  conv => lhs; pattern ack 0 1; unfold ack
  conv => lhs; pattern ack 0 2; unfold ack
  -- norm_num
  sorry



def ack' : Nat → Nat → Nat
  | y,   0   => y+1
  | 0,   x+1   => ack' 1 x
  | y+1, x+1 => ack' (ack' y (x+1)) x
termination_by x y => (y, x)

#check sizeOfWFRel

#eval SizeOf.sizeOf (0, 0)
#eval SizeOf.sizeOf (0, 1)
#eval SizeOf.sizeOf (0, 2)
#eval SizeOf.sizeOf (0, 3)
#eval SizeOf.sizeOf (0, 4)
#eval SizeOf.sizeOf (1, 1)
#eval SizeOf.sizeOf (1, 2)
#eval SizeOf.sizeOf (1, 3)
#eval SizeOf.sizeOf (1, 4)
#eval SizeOf.sizeOf (300, 20)

theorem sizeOf_prod_of_nat (a b : ℕ)
  : SizeOf.sizeOf (a, b) = 1 + a + b := rfl


theorem div_lemma' {x y : Nat} : (0 < y) ∧ (y ≤ x) → ((x - y) < x) :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div' (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div' (x - y) y + 1
  else
    0
decreasing_by exact div_lemma' h


def ack₂ : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack₂ x 1
  | x+1, y+1 => ack₂ x (ack₂ (x+1) y)
termination_by x y => (x, y)
decreasing_by
  . apply Prod.Lex.left
    simp
  . apply Prod.Lex.right
    simp
  . apply Prod.Lex.left
    simp


def ack₃ : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack₃ x 1
  | x+1, y+1 => ack₃ x (ack₃ (x+1) y)
termination_by x y => (x, y)
decreasing_by all_goals sorry

def ack₄ : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack₄ x 1
  | x+1, y+1 => ack₄ x (ack₄ (x+1) y)
termination_by x y => (x, y)
decreasing_by all_goals decreasing_tactic

def collatz (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

def print_collatz_sequence (n : ℕ) : IO Unit := do
  IO.println n
  if n == 1 then
    IO.println "stop!"
  else
    print_collatz_sequence (collatz n)
decreasing_by sorry

#eval! print_collatz_sequence 100


def collatz_sequence : ℕ → List ℕ → List ℕ
  | 1, as => 1 :: as
  | n, as => collatz_sequence (collatz n) (n :: as)
decreasing_by sorry

#eval! collatz_sequence 100 []



-- def ack : Nat → Nat → Nat
--   | 0,   y   => y+1
--   | x+1, 0   => ack x 1
--   | x+1, y+1 => ack x (ack (x+1) y)

#check ack.induct_unfolding
theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack with
  | case1 y =>
    simp
  | case2 x ih =>
    exact ih
  | case3 x y ih1 ih2 =>
    exact ih2
theorem ack_gt_zero' (n m : ℕ) : ack n m > 0 := by
  match n, m with
  | 0, y =>
    unfold ack
    simp
  | x+1, 0 =>
    unfold ack
    exact ack_gt_zero' x 1
  | x+1, y+1 =>
    unfold ack
    exact ack_gt_zero' x _


-- def f : Bool → Bool → Bool → Bool → Bool → Bool
--   | true, _, _, _ , _ => true
--   | _, true, _, _ , _ => true
--   | _, _, true, _ , _ => true
--   | _, _, _, true, _  => true
--   | _, _, _, _, x  => x
-- theorem f_or : f b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
--   fun_cases f
--   all_goals simp_all

inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

#check Vect.casesOn

def tail (v : Vect α n) : Vect α (n-1) := by
  refine' Vect.casesOn v _ _
  . exact Vect.nil
  . intro a n v
    exact v

#eval tail (@Vect.nil ℕ)
#eval tail ((@Vect.nil ℕ).cons 2)
#eval tail (((@Vect.nil ℕ).cons 2).cons 3)
#eval tail ((((@Vect.nil ℕ).cons 2).cons 3).cons 4)
#eval tail (.cons 1 (.cons 2 (.cons 4 .nil)))

#check Nat.noConfusion
#check Nat.noConfusionType
def tailAux (v : Vect α m) : m = n + 1 → Vect α n :=
  Vect.casesOn (motive := fun x _ ↦ x = n + 1 → Vect α n) v
  (fun h ↦ Nat.noConfusion h)
  (fun a m as h ↦ (Nat.succ_inj.1 h) ▸ as)

def tailAux' (v : Vect α m) : m = n + 1 → Vect α n := by
  refine' Vect.casesOn (motive := fun x _ ↦ x = n + 1 → Vect α n) v ?_ ?_
  . intro h
    contradiction
  . intro a m as h
    have : m = n := by linarith
    exact this ▸ as

def head : Vect α (n + 1) → α
  | .cons a as => a

def head' : Vect α n → Option α
  | .nil => none
  | .cons a as => some a


theorem eta : ∀ (v : Vect α (n+1)), .cons (head v) (tail v) = v
  | .cons a as => rfl

#eval head (.cons 1 .nil)


-- def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
--   | 0,   .nil,       .nil       => .nil
--   | n+1, .cons a as, .cons b bs => .cons (f a b) (map f as bs)


def mapAux (f : α → β → γ) : (n₁ n₂ : ℕ) → Vect α n₁ → Vect β n₂ → n₁ = n → n₂ = n → Vect γ n := by
  refine' Nat.recOn n _ _
  . intros; exact .nil
  intro n ih n₁ n₂ va vb; dsimp at *
  refine' Vect.casesOn va _ _
  . intros; contradiction
  clear n₁ va; intro a n₁ as
  refine' Vect.casesOn vb _ _
  . intros; contradiction
  clear n₂ vb; intro b n₂ bs
  intro hn₁ hn₂
  let map_as_bs := ih n₁ n₂ as bs (by linarith) (by linarith)
  exact .cons (f a b) map_as_bs
  -- refine

def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n :=
  @fun n va vb => mapAux f n n va vb rfl rfl

def toVect : (l : List α) → Vect α l.length
  | .nil => .nil
  | .cons a as => .cons a (toVect as)
def toList : Vect α n → List α
  | .nil => .nil
  | .cons a as => .cons a (toList as)

#eval (toVect [1,2,3,4])
#eval toList (map ((. + .)) (toVect [1,2,3,4]) (toVect [10,20,30,40]))
#eval toList (map ((. + .)) (toVect [1,2,3,5]) (toVect [10,20,30,40]))

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

-- open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), .imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, .imf a => a
