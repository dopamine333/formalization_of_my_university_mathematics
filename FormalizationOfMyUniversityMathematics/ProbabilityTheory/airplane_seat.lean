import Mathlib.Data.List.Monad
import Mathlib.Data.Rat.Init



/-
在寫機率功課 頭好痛
機率難在看不懂題目
或是說題目沒用一種限定的語言說

感覺之前看到的 list monad 可以立點功
從新定義一下
let A, B be set.
List A := { [a₁,...,aₙ] | n ∈ ℕ, ∀ 1 ≤ i ≤ n, aᵢ ∈ A}
pure : A → List A := fun a ↦ [a]
bind : List A → (A → List B) → List B :=
  fun [a₁,...,aₙ] f ↦ (f a₁) ++ ... ++ (f aₙ)

考慮五個人的排列

let S := {1,2,...,5}
define perm ∈ List S⁵ by
perm := do
  x₁ ← S
  x₂ ← S\{x₁}
  x₃ ← S\{x₁,x₂}
  x₄ ← S\{x₁,x₂,x₃}
  x₅ ← S\{x₁,x₂,x₃,x₄}
  return (x₁,x₂,x₃,x₄,x₅)

編譯成
perm :=
  bind S (fun x₁ ↦
  bind S\{x₁} (fun x₂ ↦
  bind S\{x₁,x₂} (fun x₃ ↦
  bind S\{x₁,x₂,x₃} (fun x₄ ↦
  bind  S\{x₁,x₂,x₃,x₄} (fun x₅ ↦
  pure (x₁,x₂,x₃,x₄,x₅)
  ))))))

如此定義 perm 真的是
一個 list 裡面裝著所有排列方式
集合論喜

而且用 do notation 也很直觀
排列組合喜

而且最重要的 算 perm 大小的時候
只要我對 bind, pure 的大小有研究
說不定就能很好推出來了
我喜

小 lemma
let A, B be a set, a ∈ A, as ∈ List A, f : A → List B then
|bind as f| = ∑ a ∈ as, |f a|
|pure a| = 1
相當合理 pure 是 singleton set 大小是 1
bind 是串接好幾格 list ，所以大小就是相加
list 不用考慮 disjoint 的問題

而且注意到空和定成 0 的話 式子也會成立

也注意到
如果 f 是常數函數 f = fun _ ↦ c, for some c ∈ List B
|bind as f| = ∑ a ∈ as, |c| = |as| * |c|
bind 的大小就變成乘法了


來算 perm 的大小

|perm|
=|do
  x₁ ← S
  x₂ ← S\{x₁}
  x₃ ← S\{x₁,x₂}
  x₄ ← S\{x₁,x₂,x₃}
  x₅ ← S\{x₁,x₂,x₃,x₄}
  return (x₁,x₂,x₃,x₄,x₅)|

= ∑ x₁ ∈ S, |do
  x₂ ← S\{x₁}
  x₃ ← S\{x₁,x₂}
  x₄ ← S\{x₁,x₂,x₃}
  x₅ ← S\{x₁,x₂,x₃,x₄}
  return (x₁,x₂,x₃,x₄,x₅)|

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},|do
  x₃ ← S\{x₁,x₂}
  x₄ ← S\{x₁,x₂,x₃}
  x₅ ← S\{x₁,x₂,x₃,x₄}
  return (x₁,x₂,x₃,x₄,x₅)|

...

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂},
  ∑ x₄ ∈ S\{x₁,x₂,x₃},
  ∑ x₅ ∈ S\{x₁,x₂,x₃,x₄},|do
  return (x₁,x₂,x₃,x₄,x₅)|

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂},
  ∑ x₄ ∈ S\{x₁,x₂,x₃},
  ∑ x₅ ∈ S\{x₁,x₂,x₃,x₄}, 1

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂},
  ∑ x₄ ∈ S\{x₁,x₂,x₃}, |S\{x₁,x₂,x₃,x₄}| * 1

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂},
  ∑ x₄ ∈ S\{x₁,x₂,x₃}, 1 * 1

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂}, |S\{x₁,x₂,x₃}| * 1 * 1

= ∑ x₁ ∈ S,
  ∑ x₂ ∈ S\{x₁},
  ∑ x₃ ∈ S\{x₁,x₂}, 2 * 1 * 1

...

= ∑ x₁ ∈ S, 4 * 3 * 2 * 1 * 1

= |S| * 4 * 3 * 2 * 1 * 1

= 5 * 4 * 3 * 2 * 1 * 1

= 5!




-/


/-
let S := {1,2,...,5}
define perm ∈ List S⁵ by
perm := do
  x₁ ← S
  x₂ ← S\{x₁}
  x₃ ← S\{x₁,x₂}
  x₄ ← S\{x₁,x₂,x₃}
  x₅ ← S\{x₁,x₂,x₃,x₄}
  return (x₁,x₂,x₃,x₄,x₅)
-/
#check List.instMonad

def S : List Nat := [1,2,3,4,5]
def perm : List (Nat × Nat × Nat × Nat × Nat) := do
  let x₁ ← S
  let x₂ ← (S.filter (fun x ↦ x ≠ x₁))
  let x₃ ← (S.filter (fun x ↦ x ≠ x₁ ∧ x ≠ x₂))
  let x₄ ← (S.filter (fun x ↦ x ≠ x₁ ∧ x ≠ x₂ ∧ x ≠ x₃))
  let x₅ ← (S.filter (fun x ↦ x ≠ x₁ ∧ x ≠ x₂ ∧ x ≠ x₃ ∧ x ≠ x₄))
  return (x₁,x₂,x₃,x₄,x₅)

#eval perm
#print perm

def perm_n (n : Nat) : List (List Nat) := do
  let S := List.range' 1 n
  let mut passenger : List Nat := []
  for _ in List.range' 1 n do
    let xᵢ ← (S.filter (fun x ↦ x ∉ passenger))
    passenger := passenger.concat xᵢ
  return passenger
#reduce perm_n 3
#reduce perm_n

/-

airplane seat problem

let S := [1,2,3]
let airplane : List seat³ := do

  p₁ ← S

  if 2 ∈ S\{p₁} then
    p₂ := 2
  else
    p₂ ← S\{p₁}

  if 3 ∈ S\{p₁,p₂} then
    p₃ := 3
  else
    p₃ ← S\{p₁,p₂}

  return (p₁,p₂,p₃)

let airplane' : List seat³ := do
  p₁ ← S
  p₂ ← if 2 ∈ S\{p₁} then [2] else S\{p₁}
  p₃ ← if 3 ∈ S\{p₁,p₂} then [3] else S\{p₁,p₂}
  return (p₁,p₂,p₃)
-/

def seat : List Nat := [1,2,3]
def airplane : List (Nat × Nat × Nat) := do
  let p₁ ← seat
  let p₂ ← if 2 ∈ seat.filter (fun x ↦ x ≠ p₁) then [2] else seat.filter (fun x ↦ x ≠ p₁)
  let p₃ ← if 3 ∈ seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂) then [3] else seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂)
  return (p₁,p₂,p₃)

def airplane' : List (Nat × Nat × Nat) :=
  bind seat (fun p₁ ↦
  bind (if 2 ∈ seat.filter (fun x ↦ x ≠ p₁) then [2] else seat.filter (fun x ↦ x ≠ p₁)) (fun p₂ ↦
  bind (if 3 ∈ seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂) then [3] else seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂)) (fun p₃ ↦
  pure (p₁,p₂,p₃)
  )))

def airplane'' : List (Nat × Nat × Nat) := do
  let p₁ ← seat
  let mut p₂ := 0
  let mut p₃ := 0
  if 2 ∈ seat.filter (fun x ↦ x ≠ p₁) then
    p₂ := 2
  else
    p₂ ← seat.filter (fun x ↦ x ≠ p₁)
  if 3 ∈ seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂) then
    p₃ := 3
  else
    p₃ ← seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂)
  return (p₁,p₂,p₃)


#eval airplane
#eval airplane'
#eval airplane''
#print airplane
#print airplane'
#print airplane''


def airplane''_p₃_has_correct_seat : List (Nat × Nat × Nat) := do
  let p₁ ← seat
  let mut p₂ := 0
  let mut p₃ := 0
  if 2 ∈ seat.filter (fun x ↦ x ≠ p₁) then
    p₂ := 2
  else
    p₂ ← seat.filter (fun x ↦ x ≠ p₁)
  if 3 ∈ seat.filter (fun x ↦ x ≠ p₁ ∧ x ≠ p₂) then
    p₃ := 3
  else
    []
  return (p₁,p₂,p₃)

#eval airplane''_p₃_has_correct_seat
#eval airplane''.filter (fun ⟨_,_,p₃⟩ ↦ p₃ = 3)


/-

for n people

airplane (n : ℕ) : List (List ℕ):= do
  let seat := [1:n]
  let mul passenger := []
  let p₁ ← seat
  passenger := passenger ++ [p₁]
  for i in [2:n] do
    let mul pᵢ := 0
    let empty_seat := seat.filter (fun x ↦ x ∉ passenger)
    if i ∈ empty_seat then
      pᵢ := i
    else
      pᵢ ← empty_seat
    passenger := passenger ++ [pᵢ]
  return passenger

-/


def airplane_n (n : Nat) : List (List Nat) := do
  let seat := List.range' 1 n
  let mut passenger : List Nat := []
  let p₁ ← seat
  passenger := passenger.concat p₁

  for i in List.range' 2 (n - 1) do
    let mut pᵢ := 0
    let empty_seat := seat.filter (fun x ↦ x ∉ passenger)
    if i ∈ empty_seat then
      pᵢ := i
    else
      pᵢ ← empty_seat
    passenger := passenger.concat pᵢ

  return passenger

#eval airplane_n 5
#eval (airplane_n 5).filter (fun l ↦ l[4]! = 5)
#eval ((airplane_n 5).filter (fun l ↦ l[4]! = 5)).length / ((airplane_n 5).length : Rat)
#print airplane_n

#check ForInStep
