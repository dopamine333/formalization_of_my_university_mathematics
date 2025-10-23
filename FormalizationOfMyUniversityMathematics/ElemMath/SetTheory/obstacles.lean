import Mathlib.Tactic

/-
定義 zfc 到 lean 時發生了一些問題
-/

-- version 1
class Version_1.SetTheory (set : Type u) where
  mem : set → set → Prop

  -- two sets are equal if and only if they have the same elements
  -- that is, for any x, one has x ∈ A ↔ x ∈ B.
  extensionality A B : A = B ↔ ∀ x, mem x A ↔ mem x B

  -- there exists a set S such that for all x, the statement x ∈ S is false
  emptyset : ∃ S, ∀ x, ¬ mem x S

  -- f P(x,y) is a predicate in two variables such that
  -- for each x, there is a unique y such that P(x,y) holds,
  -- then for every set U, {y | there exists x ∈ U such that P(x,y) holds} is a set
  replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
    ∀ U, ∃ S, ∀ y, mem y S ↔ ∃ x, mem x U ∧ P x y

  -- if S is a set, then the collection of all subsets of S is also a set, that is,
  -- if S is a set, then the set {T | T ⊆ S} is a set.
  powerset (S : set) : ∃ PS, ∀ T, mem T PS ↔ (∀ x, mem x T → mem x S)

  -- if S is a set, then the union of all sets that are elements in S is also a set, that is,
  -- if S is a set then the set ⋃ A ∈ S, A = {x ∈ A | A ∈ S} is a set.
  union (S : set) : ∃ U, ∀ x, mem x U ↔ ∃ A, mem A S ∧ mem x A

  -- there exists a set S such that ∅ ∈ S and if x ∈ S then x ∪ {x} ∈ S.
  infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

  -- every nonempty set S has an element which has empty intersection with S, that is,
  -- if S ≠ ∅, then there exists A ∈ S such that A ∩ S = ∅.
  regularity S (hS : S ≠ ∅) : ∃ A, mem A S ∧ A ∩ S = ∅

  -- if S is a nonempty set and P(S) denotes the power set of S,
  -- then there exists a function f ∶ P(S) → S such that f(T) ∈ T for any nonempty set T ∈ P(S).
  choice S (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T, mem T (P S) → T ≠ ∅ → mem f(T) T

/-
infinity 中的 ∅ 報錯了！
這裡有兩層問題
問題 1. 符號 ∅ 所指代的背後的 term 是什麼
問題 2. 符號 ∅ 是怎麼綁定到這個 term 上面的

對於問題 1.
雖然 emptyset 公理寫了 ∃ S, ∀ x, ¬ mem x S
但是這個 S 只活在 ∃ S, ∀ x, ¬ mem x S 在其他地方訪問不到
這裡有兩個辦法
方法 1.1.
  將 infinity 改寫成 ∃ S', (∀ x, ¬ mem x S') ∧ (∃ S, mem S' S ∧ ∀ x, mem x S → mem (x ∪ {x}) S)
  也就是在 infinity 裡當場在宣告一個集合 S' 還代表 emptyset 的存在性
  再把後面用到 emptyset 的地方改成 S'
  優點：簡單暴力有效
  缺點：真的太暴力了，尤其你看 infinity 後面還用到聯集和 singleton set，全部要再宣告一次會變超長

-/

-- 方法 1.1. 示範
class Method_1_1.SetTheory (set : Type u) where
  mem : set → set → Prop
  emptyset : ∃ S, ∀ x, ¬ mem x S
  -- infinity 前面多了 ∃ S', (∀ x, ¬ mem x S')
  infinity : ∃ S', (∀ x, ¬ mem x S') ∧ (∃ S, mem S' S ∧ ∀ x, mem x S → mem (x ∪ {x}) S)

/-
方法 1.2.
  將 emptyset 視作一個新的常數，直接和 set, mem 放在一起
  再把 emptyset 公理改成 ∀ x, ¬ mem emptyset
  優點：後續使用簡潔
  缺點：好像和講義原文感覺不太一樣，存在 emptyset 和直接令 emptyset 為一個常數，微妙
-/

-- 方法 1.2. 示範
class Method_1_2.SetTheory (set : Type u) where
  mem : set → set → Prop
  -- 新的常數!
  emptyset : set
  not_mem_emptyset : ∀ x, ¬ mem x emptyset
  infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

/-
這裡我選擇了 1.2. 的解決方式
實際上這也是 mathlib 裡 Group 定義的精神 （matlhib 會更在複雜點）
參見：`#check mul_one`
-/
#check mul_one

-- version 2
class Version_2.SetTheory (set : Type u) where
  mem : set → set → Prop
  emptyset : set
  extensionality A B : A = B ↔ ∀ x, mem x A ↔ mem x B
  not_mem_emptyset : ∀ x, ¬ mem x emptyset
  replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
    ∀ U, ∃ S, ∀ y, mem y S ↔ ∃ x, mem x U ∧ P x y
  powerset (S : set) : ∃ PS, ∀ T, mem T PS ↔ (∀ x, mem x T → mem x S)
  union (S : set) : ∃ U, ∀ x, mem x U ↔ ∃ A, mem A S ∧ mem x A
  infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S
  regularity S (hS : S ≠ emptyset) : ∃ A, mem A S ∧ A ∩ S = emptyset
  choice S (hS : S ≠ emptyset) : ∃ f : P S → S, ∀ T, mem T (P S) → T ≠ emptyset → mem f(T) T

/-
很好！快解決了一半紅線了 快成功了（並沒有）
我們還是比較喜歡寫 ∅ 而不是 emptyset 的
對於問題 2. 我們也有兩個解法
方法 2.1
  lean 有提供 notation 的語法
  但很可惜要定義完整個 class 才能定 notation
  優點：簡單，只要一行 notation "∅" => emptyset 就好
  缺點：在寫公理時還是不能用 ∅, 後續的定理才能使用
-/

-- 方法 2.1 範例
namespace Method_2_1

class SetTheory (set : Type u) where
  mem : set → set → Prop
  emptyset : set
  -- 不能用 ∅ 符號
  infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

open SetTheory

#check infinity
-- Method_2_1.SetTheory.infinity.{u} {set : Type u} [self : SetTheory set] :
-- ∃ S, mem emptyset S ∧ ∀ (x : set), mem x S → mem sorry S

notation "∅" => emptyset -- 這行後才有 ∅ 符號

#check infinity
-- Method_2_1.SetTheory.infinity.{u} {set : Type u} [self : SetTheory set] :
-- ∃ S, mem ∅ S ∧ ∀ (x : set), mem x S → mem sorry S

end Method_2_1

/-
方法 2.2
  我們可以定一個純符號的 class 再讓 SetTheory 去 extends 他
  如此，在寫 SetTheory 的公理前，∅ 符號就被設立好了
-/

namespace Method_2_2

-- 方法 2.2 範例
class HasEmptyset (set : Type u) where
  emptyset : set

notation "∅" => HasEmptyset.emptyset

class SetTheory (set : Type u) extends HasEmptyset set where
  mem : set → set → Prop
  -- extends HasEmptyset set 後 就能用 ∅ 符號了
  infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

end Method_2_2

/-
實際上，mathlib 裡也很常做這種事情
常做到已經有個 class 叫 EmptyCollection 就是專門管理 ∅ 符號的
可以把 notation "∅" => HasEmptyset.emptyset 這行
改成用 instance 註冊 EmptyCollection 例如
-/

namespace Method_2_2'

-- 方法 2.2' 範例
class HasEmptyset (set : Type u) where
  emptyset : set

-- 這表示一個 set : Type u 上 如果有 HasEmptyset 的結構
-- 他能自動推導出 set 上的 EmptyCollection 結構
instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
  emptyCollection := HasEmptyset.emptyset

class SetTheory (set : Type u) extends HasEmptyset set where
  mem : set → set → Prop
  -- EmptyCollection 中就有定義 ∅ 符號，而且用 mathlib 內建的還有其他優點
  -- 符號優先級預設好了和 ∀ x ∈ A, x ∈ B 是 ∀ x, x ∈ A → x ∈ B 的簡寫
  infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

end Method_2_2'

/-
我選擇方法 2.2
他揭露了用一層層 class 互相 extends 來打造整個數學層級的可能性
而且這確實也是 mathlib 裡面常用的做法
參見：`#check One`
-/
#check One
/-
用類似的方法 我也把 mem 改成了 ∈ 符號
注意到有些變數從 S 變成了 (S : set)
使用符號的一個缺點也是會讓 lean 的型別推斷變困難
-/


-- version 3
namespace Version_3

class HasMem (set : Type u) where
  mem : set → set → Prop

instance (set : Type u) [HasMem set] : Membership set set where
  mem := HasMem.mem

class HasEmptyset (set : Type u) where
  emptyset : set

instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
  emptyCollection := HasEmptyset.emptyset

class SetTheory (set : Type u) extends HasMem set, HasEmptyset set where
  extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
  not_mem_emptyset : ∀ x, ¬ x ∈ emptyset
  replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
    ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y --  ∃ x, x ∈ U ∧ P x y 簡寫成 ∃ x ∈ U, P x y 了！
  powerset (S : set) : ∃ PS : set, ∀ T : set, T ∈ PS ↔ (∀ x ∈ T, x ∈ S) -- ∀ x, x ∈ T → x ∈ S 簡寫成 ∀ x ∈ T, x ∈ S 了！
  union (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A
  infinity : ∃ S : set, (∅ : set) ∈ S ∧ ∀ x ∈ S, (x ∪ {x}) ∈ S
  regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = (∅ : set)
  choice (S : set) (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T : set, T ∈ (P S) → T ≠ ∅ → f(T) ∈ T

end Version_3
