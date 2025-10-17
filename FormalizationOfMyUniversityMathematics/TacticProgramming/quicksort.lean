import Mathlib.Data.List.Monad
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Enumerative.Catalan

#check StateT

def quicksort : List ℕ → List ℕ
  | [] => []
  | a::as =>
    let left := as.filter (. ≤ a)
    let right := as.filter (. > a)

    have decreasing (p : ℕ → Bool) : (as.filter p).length < (a::as).length :=
      (List.length_filter_le _ _).trans_lt (Nat.lt_succ_self _)
    have : left.length < (a::as).length := decreasing (. ≤ a)
    have : right.length < (a::as).length := decreasing (. > a)

    quicksort left ++ [a] ++ quicksort right
termination_by array => array.length

#eval quicksort [3,1,4,1,5,9,2,6]

def quicksort_List : List ℕ → List (List ℕ)
  | [] => do return []
  | array => do
    let ⟨pivot, hmem⟩ ← array.attach -- wow, attach is amazing, it holds hmem!
    let left := (array.erase pivot).filter (. ≤ pivot)
    let right := (array.erase pivot).filter (. > pivot)

    have decreasing (p : ℕ → Bool) :
      ((array.erase pivot).filter p).length < array.length := by
      calc ((array.erase pivot).filter p).length
        _ ≤ (array.erase pivot).length := List.length_filter_le _ _
        _ = array.length - 1 := List.length_erase_of_mem hmem
        _ < array.length := by
          apply Nat.sub_one_lt
          linarith [List.length_pos_of_mem hmem]
    have : left.length < array.length := decreasing (. ≤ pivot)
    have : right.length < array.length := decreasing (. > pivot)

    let sorted_left ← quicksort_List left
    let sorted_right ← quicksort_List right
    return sorted_left ++ [pivot] ++ sorted_right
termination_by array => array.length

#eval quicksort_List [3,1,4,1,5]
#eval (quicksort_List [3,1,4,1,5]).length

#eval (quicksort_List [1]).length
#eval (quicksort_List [1,1]).length
#eval (quicksort_List [1,1,1]).length
#eval (quicksort_List [1,1,1,1]).length
#eval (quicksort_List [1,1,1,1,1]).length
#eval (quicksort_List [1,1,1,1,1,1]).length
-- 1, 2, 6, 24, 120, 720
-- is n!

#eval (quicksort_List [1]).length
#eval (quicksort_List [1,2]).length
#eval (quicksort_List [1,2,3]).length
#eval (quicksort_List [1,2,3,4]).length
#eval (quicksort_List [1,2,3,4,5]).length
#eval (quicksort_List [1,2,3,4,5,6]).length
#eval (quicksort_List [1,2,3,4,5,6,7]).length
-- 1, 2, 5, 14, 42, 132, 429
-- is Catalan numbers (why)

/-


def quicksort_List : List ℕ → List (List ℕ)
  | [] => do return []
  | array => do
    let pivot ← array
    let left := (array.erase pivot).filter (. ≤ pivot)
    let right := (array.erase pivot).filter (. > pivot)
    let sorted_left ← quicksort_List left
    let sorted_right ← quicksort_List right
    return sorted_left ++ [pivot] ++ sorted_right
termination_by array => array.length

|array| = n, n ≥ 1
pivot ∈ array
|array.erase pivot| = n - 1
left ∪ [pivot] ∪ right ≃ array
|left| + 1 + |right| = |array|

assume all element in array are distinct
sort(n)
= ∑ i ∈ [1:n], sort(#l(i, [1:n])) * sort(#r(i, [1:n]))
= ∑ i ∈ [1:n], sort(i - 1) * sort(n - i)
sort(0) = 1
it exacty is Catalan numbers !


in general
sort(as)
= ∑ p ∈ as, sort(l(p, as)) * sort(r(p, as))
sort([]) = 1
l(p, as) ∪ [p] ∪ r(p, as) = as (disjoint union)


if as are all the same element
l(p, as) = (as.erase p).filter (. ≤ p) = as.erase p
r(p, as) = (as.erase p).filter (. > p) = []
sort(as)
= ∑ p ∈ as, sort(l(p, as)) * sort(r(p, as))
= ∑ p ∈ as, sort(as.erase p) * sort([])
= ∑ p ∈ as, sort(as.erase p) * 1
= as * sort(as.erase as[0])
-> sort(n) = n * sort(n - 1)
is n!


if as ~ bs, where ~ mean ∃ f : as → bs is bijection.
f '' l(p, as) = l(f(p), bs) ?
f '' l(p, as)
= f '' ((as.erase p).filter (. ≤ p))
= (f '' (as.erase p)).filter (. ≤ f(p)))
= ((f '' as).erase f(p))).filter (. ≤ f(p)))
= (bs.erase f(p))).filter (. ≤ f(p)))
= (bs.erase f(p))).filter (. ≤ f(p)))
= l(f(p), bs)

simiarly, f '' r(p, as) = r(f(p), bs), so
sort(as)
= ∑ p ∈ as, sort(l(p, as)) * sort(r(p, as))
= ∑ p ∈ as, sort(l(f(p), bs)) * sort(r(f(p), bs))
= ∑ q ∈ bs, sort(l(b, bs)) * sort(r(b, bs))
= sort(bs)
-/
#check List.sorted_mergeSort
theorem quicksort_List_all_the_same
  (array : List ℕ) (n : ℕ) (hn : array.length = n)
  (h : List.Pairwise (. = .) array) :
  (quicksort_List array).length = n.factorial := by sorry

theorem quicksort_List_distinct
  (array : List ℕ) (n : ℕ) (hn : array.length = n)
  (h : List.Pairwise (. ≠ .) array) :
  (quicksort_List array).length = catalan n := by sorry


-- CounterT monad
#check Option
#check OptionT

def Counter (α : Type u) := ℕ → (α × ℕ)
namespace Counter
instance : Monad Counter where
  pure a := fun n ↦ (a, n)
  bind ma f := fun n ↦
    let (a, n') := ma n
    f a (n' + 1)
end Counter

namespace Counter.Test
def foo : Counter ℕ := do
  let x ← pure 3
  let y ← pure 4
  return x + y
#eval foo 0
def bar : Counter ℕ := do
  let mut sum := 0
  for i in [1:10] do
    sum := sum + i
  return sum
#eval bar 0
def bar' : StateT ℕ Counter ℕ := do
  set 0
  for i in [1:10] do
    modify (. + i)
  return (← get)
#eval bar' 0 0

def foo2 (n : ℕ) : ExceptT String Counter ℕ := do
  let mut sum := 0
  for i in [1:n] do
    sum := sum + i
    if sum ≥ 50 then throw "too high"
  return sum
#eval (foo2 15).run 0
#eval (foo2 10).run 0
#eval (foo2 5).run 0


end Counter.Test

def CounterLog (α : Type u) := (ℕ × Std.Format) → (α × ℕ × Std.Format)
namespace CounterLog
instance : Monad CounterLog where
  pure a := fun (n, s) ↦ (a, n, s ++ s!"pure {n} \n ")
  bind ma f := fun (n, s) ↦
    let (a, n', s') := ma (n, s);
    f a ((n' + 1), (s' ++ s!"bind {n' + 1} \n"))

end CounterLog

namespace CounterLog.Test
def foo : CounterLog ℕ := do
  let x ← pure 3
  let y ← pure 4
  return x + y
#eval foo (0, "")
def bar : CounterLog ℕ := do
  let mut sum := 0
  for i in [1:1] do
    sum := sum + i
  return sum
#eval bar (0, "")
#print "1\n2\n3"
#print bar

end CounterLog.Test

#check IO
#check StateT
#check MonadLift

def CounterT (m : Type u → Type v) (α : Type u) := ℕ → m (α × ℕ)

namespace CounterT

variable {m : Type u → Type v} [Monad m]

def pure (a : α) : CounterT m α :=
  fun n ↦ do
  return (a, n)

def bind (ma : CounterT m α) (f : α → CounterT m β) : CounterT m β :=
  fun n ↦ do
  let (a, n') ← ma n
  f a (n' + 1)

instance : Monad (CounterT m) where
  pure := CounterT.pure
  bind := CounterT.bind

def lift (ma : m α) : CounterT m α :=
  fun n ↦ do
  let a ← ma
  return (a, n)

instance : MonadLift m (CounterT m) := ⟨CounterT.lift⟩

end CounterT



-- def filterAuxM_with_property
--   {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) :
--   List α → List α → m ((bs : List α) × ∀ b ∈ bs, f b)
--   | [],     acc => pure acc
--   | h :: t, acc => do
--     let b ← f h
--     filterAuxM_with_property f t (cond b (h :: acc) acc)

-- def filterM_with_property
--   {m : Type → Type v} [Monad m] {α : Type}
--   (p : α → m Bool) (as : List α) : m (List α) := do
--   let as ← filterAuxM_with_property p as []
--   pure as.reverse

namespace filterM_test
def powerset' : List ℕ → List (List ℕ)
  | [] => [[]]
  | a::as => do
    let b ← [true, false]
    let bs ← powerset' as
    return if b then a :: bs else bs
#eval powerset' [1, 2, 3]
def powerset (as : List ℕ) : List (List ℕ) := as.filterM (fun _ ↦ [true, false])
#eval powerset [1, 2, 3]
-- [[1, 2, 3], [1, 2], [1, 3], [1], [2, 3], [2], [3], []]

def all (as : List ℕ) (p : ℕ → Bool) : Option (List ℕ) :=
  as.filterM (fun a ↦ if p a then pure True else none)
#eval all [1,2,3,4] (. ≤ 4)   -- some [1, 2, 3, 4]
#eval all [1,2,3,4,5] (. ≤ 4) -- none

def smaller_then (as : List ℕ) : StateM ℕ (List ℕ) :=
  as.filterM (fun a ↦ do
    let b ← get
    return a ≤ b
  )
#eval smaller_then [1,2,3] 5
#eval smaller_then [1,2,3] 2

def countdown (as : List ℕ) : StateM ℕ (List ℕ) :=
  as.filterM (fun _ ↦ do
    modify (. - 1)
    return 0 == (← get)
  )
#eval countdown [1,2,3,4,5,6,7,8] 5
#eval countdown [1,2,3,4,5,6,7,8] 2

def increasing_subseq (as : List ℕ) : StateM ℕ (List ℕ) :=
  as.filterM (fun a ↦ do
    let maximal ← get
    if a ≥ maximal then
      set a
      return true
    else
      return false
  )
#eval increasing_subseq [3,1,4,1,5,9,2,6] 0
-- ([3, 4, 5, 9], 9)
end filterM_test

namespace CounterT.Test

def roll_two_dice : CounterT List ℕ := do
  let dice : List ℕ := [1,2,3,4,5,6]
  let x ← dice
  let y ← dice
  return x + y
#print roll_two_dice
#eval roll_two_dice 0

def helloworld : CounterT IO Unit := do
  IO.println "Hello World!"
  for i in [1:10] do
    IO.println s!"i = {i}"
#print helloworld
#eval helloworld 0

-- lemma List.filterM_with_property [Monad m] (as : List α) (p : α → m Bool) :
--   m ((bs : List α) × (bs = as.filter p))

def quicksort : List ℕ → CounterT List (List ℕ)
  | [] => do return []
  | a::as => do
    let left := as.filter (. ≤ a)
    let right := as.filter (. > a)
    have : left.length < (a::as).length :=
      (List.length_filter_le _ _).trans_lt (Nat.lt_add_one _)
    have : right.length < (a::as).length :=
      (List.length_filter_le _ _).trans_lt (Nat.lt_add_one _)
    return (← quicksort left) ++ [a] ++ (← quicksort right)
termination_by array => array.length

#print quicksort
#eval quicksort [3, 1, 4, 1, 5, 1, 2] 0
#eval quicksort [1, 1] 0
#eval quicksort [1] 0
#eval quicksort [] 0
#eval quicksort [4, 5] 0
#eval quicksort [] 0
#eval quicksort [5] 0


end CounterT.Test

def tick : StateT ℕ List Unit := modify (. + 1)
def average (m : StateT ℕ List α) : ℚ :=
  let l := m 0
  (l.map (fun (_, t) ↦ t)).sum / (l.length : ℚ)
namespace CounterList

partial def quicksort : List ℕ → StateT ℕ List (List ℕ)
  | [] => do
    tick
    return []
  | a::as => do
    let mut left := []
    let mut right := []
    for a' in as do
      if a' ≤ a then
        left := left.concat a'
        tick
      else
        right := right.concat a'
        tick
    -- have : left.length < (a::as).length := sorry
    -- have : right.length < (a::as).length := sorry
    tick
    return (← quicksort left) ++ [a] ++ (← quicksort right)
-- termination_by array => array.length
#eval quicksort [3,1,4,1,5,9,2,6] 0
#eval quicksort [] 0
#eval quicksort [1] 0
#eval quicksort [1,2] 0
#eval quicksort [1,2,3] 0
#eval quicksort [1,2,3,4] 0
#eval quicksort [1,2,3,4,5] 0
#eval quicksort [1,1,1,1] 0
#eval average (quicksort [1,2,3,4,5])

partial def quicksort_random_pivot : List ℕ → StateT ℕ List (List ℕ)
  | [] => do
    return []
  | array => do
    let pivot ← array

    let mut left := []
    let mut right := []
    for a in array.erase pivot do
      tick
      if a ≤ pivot then
        left := left.concat a
      else
        right := right.concat a

    let sorted_left ← quicksort_random_pivot left
    let sorted_right ← quicksort_random_pivot right
    return sorted_left ++ [pivot] ++ sorted_right

#eval quicksort_random_pivot [1,2,3,4] 0
/-
[([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 5),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 4),
 ([1, 2, 3, 4], 4),
 ([1, 2, 3, 4], 4),
 ([1, 2, 3, 4], 4),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 5),
 ([1, 2, 3, 4], 6),
 ([1, 2, 3, 4], 6)]
-/
#eval average (quicksort_random_pivot [1,2,3,4])
-- (37 : Rat)/7

#eval (quicksort_random_pivot [] 0).length -- 1
#eval (quicksort_random_pivot [1] 0).length -- 1
#eval (quicksort_random_pivot [1,2] 0).length -- 2
#eval (quicksort_random_pivot [1,2,3] 0).length -- 5
#eval (quicksort_random_pivot [1,2,3,4] 0).length -- 14
#eval (quicksort_random_pivot [1,2,3,4,5] 0).length -- 42
#eval (quicksort_random_pivot [1,2,3,4,5,6] 0).length -- 132
#eval (quicksort_random_pivot [1,2,3,4,5,6,7] 0).length -- 429

#eval (quicksort_random_pivot [] 0).length -- 1
#eval (quicksort_random_pivot [1] 0).length -- 1
#eval (quicksort_random_pivot [1,1] 0).length -- 2
#eval (quicksort_random_pivot [1,1,1] 0).length -- 6
#eval (quicksort_random_pivot [1,1,1,1] 0).length -- 24
#eval (quicksort_random_pivot [1,1,1,1,1] 0).length -- 120
#eval (quicksort_random_pivot [1,1,1,1,1,1] 0).length -- 720
#eval (quicksort_random_pivot [1,1,1,1,1,1,1] 0).length -- 5040


end CounterList


def bind_on_list (l : List α) (f : (a : α) → (a ∈ l) → List β) : List β :=
  bind l.attach (fun ⟨a, h⟩ ↦ f a h)

theorem bind_on_list_eq_bind (l : List α) (f : α → List β) :
  bind_on_list l (fun a _ ↦ f a) = bind l f := by simp [bind_on_list]
