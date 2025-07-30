import Mathlib.Tactic

namespace Exercise2

inductive List (α : Type u)
  | nil : List α
  | cons : α → List α → List α

open List

def reverse : List α → List α
  | l => aux l nil
where aux : List α → List α → List α
  | nil,       l => l
  | cons a as, l => aux as (cons a l)

#eval reverse (cons 1 <| cons 2 <| cons 3 nil)

theorem reverse_reverse : ∀ l : List α, reverse (reverse l) = l
  | l => aux l nil
where aux : ∀ l₁ l₂ : List α, reverse.aux (reverse.aux l₁ l₂) nil = reverse.aux l₂ l₁
  | nil       , _ => rfl
  | cons a as , l₂ =>
    calc reverse.aux (reverse.aux (cons a as) l₂) nil
      _ = reverse.aux (reverse.aux as (cons a l₂)) nil := rfl
      _ = reverse.aux (cons a l₂) as := aux as _
      _ = reverse.aux l₂ (cons a as) := rfl

end Exercise2

namespace Exercise3

#check Nat.below
#check Nat.brecOn

inductive Below {C : ℕ → Sort u} : ℕ → Sort (max 1 u)
  | nil : Below 0
  | intro (n : ℕ) (hn : C n) (b : @Below C n) : Below (n + 1)

def Below.left : @Below C (n + 1) → C n
  | .intro _ hn _ => hn
def Below.right : @Below C (n + 1) → @Below C n
  | .intro _ _ b => b

#check Below.rec

def BrecOn  {motive : ℕ → Sort u} (n : ℕ) (h : (m : ℕ) → @Below motive m → motive m) : motive n := by
  apply h
  induction' n with n ih
  . exact .nil
  . apply Below.intro
    . exact h n ih
    . exact ih

def fib : ℕ → ℕ := by
  intro x
  apply BrecOn x
  intro m bm
  match m with
    | 0 => exact 1
    | 1 => exact 1
    | m + 2 => exact bm.left + bm.right.left

#eval fib 150


#check Acc
#check WellFounded
#check WellFounded.fix

noncomputable
def WellFounded_fix {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : WellFounded r)
  (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) : C x := by
    have acc_x := hwf.apply x
    refine' Acc.recOn (motive := fun a _ => C a) acc_x _
    dsimp
    intro x _ h
    apply F x h


end Exercise3


namespace Exercise4

inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)

open Vect
def append : {n m : ℕ} → Vect α n → Vect α m → Vect α (n + m)
  | 0,      m, nil,       vb => (by simp +arith : m = 0 + m) ▸ vb
  | n + 1,  m, cons a as, vb => (by simp +arith : n + 1 + m = n + m + 1) ▸ cons a (append as vb)

#eval append (cons 1 <| cons 3 <| cons 5 .nil) (cons 2 <| cons 4 .nil)

def map (f : α → β) : {n : ℕ} → Vect α n → Vect β n
  | _, nil => nil
  | _, cons a as => cons (f a) (map f as)

#eval map (fun x => x + 1) (cons 1 <| cons 3 <| cons 5 .nil)

def append' : {n m : ℕ} → Vect α n → Vect β m → Vect (α ⊕ β) (n + m)
  | 0,      m, nil,       vb => (by simp +arith : m = 0 + m) ▸ map Sum.inr vb
  | n + 1,  m, cons a as, vb => (by simp +arith : n + 1 + m = n + m + 1) ▸ cons (Sum.inl a) (append' as vb)

#eval append' (cons 1 <| cons 3 <| cons 5 .nil) (cons (-1) <| cons 4 .nil)


end Exercise4


namespace Exercise5

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

open Expr


def Expr.repr : Expr → Nat → Std.Format
  | const n, _ => toString n
  | var n, _ => "x" ++ Nat.toSubscriptString n
  | plus e₁ e₂, _ => "(" ++ Expr.repr e₁ 0 ++ " + " ++ Expr.repr e₂ 0 ++ ")"
  | times e₁ e₂, _ => "(" ++ Expr.repr e₁ 0 ++ " ⬝ " ++ Expr.repr e₂ 0 ++ ")"

instance : Repr Expr where
  reprPrec := Expr.repr



def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

#eval sampleExpr

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

#eval simpConst (plus (plus (const 1) (const 2)) (const 3))
#eval simpConst (plus (const 1) (plus (const 2) (const 3)))
#eval simpConst (plus (const 1) (const 2))

def fuse : Expr → Expr
  | plus e₁ e₂                  => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂                 => simpConst (times (fuse e₁) (fuse e₂))
  | e                           => e

#eval fuse (plus (plus (const 1) (const 2)) (const 3))
#eval fuse (plus (const 1) (plus (const 2) (const 3)))
#eval fuse (plus (const 1) (const 2))

example : fuse (plus (plus (const 1) (const 2)) (const 3)) = const 6 := by
  conv =>
    unfold fuse
    unfold fuse
    unfold fuse
    unfold simpConst
    dsimp

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  fun_cases simpConst e <;> rfl

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
  intro e
  fun_induction fuse e with
  | case1 e₁ e₂ ih1 ih2 =>
    rw [simpConst_eq]
    unfold eval
    rw [ih1, ih2]
  | case2 e₁ e₂ ih1 ih2 =>
    rw [simpConst_eq]
    unfold eval
    rw [ih1, ih2]
  | case3 e     => rfl

end Exercise5
