-- import Mathlib.Tactic

-- /-
-- 定義 zfc 到 lean 時發生了一些問題
-- -/

-- -- version 1
-- class Version_1.SetTheory (set : Type u) where
--   mem : set → set → Prop

--   -- two sets are equal if and only if they have the same elements
--   -- that is, for any x, one has x ∈ A ↔ x ∈ B.
--   extensionality A B : A = B ↔ ∀ x, mem x A ↔ mem x B

--   -- there exists a set S such that for all x, the statement x ∈ S is false
--   emptyset : ∃ S, ∀ x, ¬ mem x S

--   -- f P(x,y) is a predicate in two variables such that
--   -- for each x, there is a unique y such that P(x,y) holds,
--   -- then for every set U, {y | there exists x ∈ U such that P(x,y) holds} is a set
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U, ∃ S, ∀ y, mem y S ↔ ∃ x, mem x U ∧ P x y

--   -- if S is a set, then the collection of all subsets of S is also a set, that is,
--   -- if S is a set, then the set {T | T ⊆ S} is a set.
--   powerset (S : set) : ∃ PS, ∀ T, mem T PS ↔ (∀ x, mem x T → mem x S)

--   -- if S is a set, then the union of all sets that are elements in S is also a set, that is,
--   -- if S is a set then the set ⋃ A ∈ S, A = {x ∈ A | A ∈ S} is a set.
--   union (S : set) : ∃ U, ∀ x, mem x U ↔ ∃ A, mem A S ∧ mem x A

--   -- there exists a set S such that ∅ ∈ S and if x ∈ S then x ∪ {x} ∈ S.
--   infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

--   -- every nonempty set S has an element which has empty intersection with S, that is,
--   -- if S ≠ ∅, then there exists A ∈ S such that A ∩ S = ∅.
--   regularity S (hS : S ≠ ∅) : ∃ A, mem A S ∧ A ∩ S = ∅

--   -- if S is a nonempty set and P(S) denotes the power set of S,
--   -- then there exists a function f ∶ P(S) → S such that f(T) ∈ T for any nonempty set T ∈ P(S).
--   choice S (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T, mem T (P S) → T ≠ ∅ → mem f(T) T

-- /-
-- infinity 中的 ∅ 報錯了！
-- 這裡有兩層問題
-- # 問題 1. 符號 ∅ 所指代的背後的 term 是什麼
-- # 問題 2. 符號 ∅ 是怎麼綁定到這個 term 上面的

-- 對於問題 1.
-- 雖然 emptyset 公理寫了 ∃ S, ∀ x, ¬ mem x S
-- 但是這個 S 只活在 ∃ S, ∀ x, ¬ mem x S 在其他地方訪問不到
-- 這裡有兩個辦法
-- 方法 1.1.
--   將 infinity 改寫成 ∃ S', (∀ x, ¬ mem x S') ∧ (∃ S, mem S' S ∧ ∀ x, mem x S → mem (x ∪ {x}) S)
--   也就是在 infinity 裡當場在宣告一個集合 S' 還代表 emptyset 的存在性
--   再把後面用到 emptyset 的地方改成 S'
--   優點：簡單暴力有效
--   缺點：真的太暴力了，尤其你看 infinity 後面還用到聯集和 singleton set，全部要再宣告一次會變超長

-- -/

-- -- 方法 1.1. 示範
-- class Method_1_1.SetTheory (set : Type u) where
--   mem : set → set → Prop
--   emptyset : ∃ S, ∀ x, ¬ mem x S
--   -- infinity 前面多了 ∃ S', (∀ x, ¬ mem x S')
--   infinity : ∃ S', (∀ x, ¬ mem x S') ∧ (∃ S, mem S' S ∧ ∀ x, mem x S → mem (x ∪ {x}) S)

-- /-
-- 方法 1.2.
--   將 emptyset 視作一個新的常數，直接和 set, mem 放在一起
--   再把 emptyset 公理改成 ∀ x, ¬ mem emptyset
--   優點：後續使用簡潔
--   缺點：好像和講義原文感覺不太一樣，存在 emptyset 和直接令 emptyset 為一個常數，微妙
-- -/

-- -- 方法 1.2. 示範
-- class Method_1_2.SetTheory (set : Type u) where
--   mem : set → set → Prop
--   -- 新的常數!
--   emptyset : set
--   not_mem_emptyset : ∀ x, ¬ mem x emptyset
--   infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

-- /-
-- 這裡我選擇了 1.2. 的解決方式
-- 實際上這也是 mathlib 裡 Group 定義的精神 （matlhib 會更在複雜點）
-- 參見：`#check mul_one`
-- -/
-- #check mul_one

-- -- version 2
-- class Version_2.SetTheory (set : Type u) where
--   mem : set → set → Prop
--   emptyset : set
--   extensionality A B : A = B ↔ ∀ x, mem x A ↔ mem x B
--   not_mem_emptyset : ∀ x, ¬ mem x emptyset
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U, ∃ S, ∀ y, mem y S ↔ ∃ x, mem x U ∧ P x y
--   powerset (S : set) : ∃ PS, ∀ T, mem T PS ↔ (∀ x, mem x T → mem x S)
--   union (S : set) : ∃ U, ∀ x, mem x U ↔ ∃ A, mem A S ∧ mem x A
--   infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S
--   regularity S (hS : S ≠ emptyset) : ∃ A, mem A S ∧ A ∩ S = emptyset
--   choice S (hS : S ≠ emptyset) : ∃ f : P S → S, ∀ T, mem T (P S) → T ≠ emptyset → mem f(T) T

-- /-
-- 很好！快解決了一半紅線了 快成功了（並沒有）
-- 我們還是比較喜歡寫 ∅ 而不是 emptyset 的
-- 對於問題 2. 我們也有兩個解法
-- 方法 2.1
--   lean 有提供 notation 的語法
--   但很可惜要定義完整個 class 才能定 notation
--   優點：簡單，只要一行 notation "∅" => emptyset 就好
--   缺點：在寫公理時還是不能用 ∅, 後續的定理才能使用
-- -/

-- -- 方法 2.1 範例
-- namespace Method_2_1

-- class SetTheory (set : Type u) where
--   mem : set → set → Prop
--   emptyset : set
--   -- 不能用 ∅ 符號
--   infinity : ∃ S, mem emptyset S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

-- open SetTheory

-- #check infinity
-- -- Method_2_1.SetTheory.infinity.{u} {set : Type u} [self : SetTheory set] :
-- -- ∃ S, mem emptyset S ∧ ∀ (x : set), mem x S → mem sorry S

-- notation "∅" => emptyset -- 這行後才有 ∅ 符號

-- #check infinity
-- -- Method_2_1.SetTheory.infinity.{u} {set : Type u} [self : SetTheory set] :
-- -- ∃ S, mem ∅ S ∧ ∀ (x : set), mem x S → mem sorry S

-- end Method_2_1

-- /-
-- 方法 2.2
--   我們可以定一個純符號的 class 再讓 SetTheory 去 extends 他
--   如此，在寫 SetTheory 的公理前，∅ 符號就被設立好了
-- -/

-- namespace Method_2_2

-- -- 方法 2.2 範例
-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- notation "∅" => HasEmptyset.emptyset

-- class SetTheory (set : Type u) extends HasEmptyset set where
--   mem : set → set → Prop
--   -- extends HasEmptyset set 後 就能用 ∅ 符號了
--   infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

-- end Method_2_2

-- /-
-- 實際上，mathlib 裡也很常做這種事情
-- 常做到已經有個 class 叫 EmptyCollection 就是專門管理 ∅ 符號的
-- 可以把 notation "∅" => HasEmptyset.emptyset 這行
-- 改成用 instance 註冊 EmptyCollection 例如
-- -/

-- namespace Method_2_2'

-- -- 方法 2.2' 範例
-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- -- 這表示一個 set : Type u 上 如果有 HasEmptyset 的結構
-- -- 他能自動推導出 set 上的 EmptyCollection 結構
-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class SetTheory (set : Type u) extends HasEmptyset set where
--   mem : set → set → Prop
--   -- EmptyCollection 中就有定義 ∅ 符號，而且用 mathlib 內建的還有其他優點
--   -- 符號優先級預設好了和 ∀ x ∈ A, x ∈ B 是 ∀ x, x ∈ A → x ∈ B 的簡寫
--   infinity : ∃ S, mem ∅ S ∧ ∀ x, mem x S → mem (x ∪ {x}) S

-- end Method_2_2'

-- /-
-- 我選擇方法 2.2
-- 他揭露了用一層層 class 互相 extends 來打造整個數學層級的可能性
-- 而且這確實也是 mathlib 裡面常用的做法
-- 參見：`#check One`
-- -/
-- #check One
-- /-
-- 用類似的方法 我也把 mem 改成了 ∈ 符號
-- 注意到有些變數從 S 變成了 (S : set)
-- 使用符號的一個缺點也是會讓 lean 的型別推斷變困難
-- -/


-- -- version 3
-- namespace Version_3

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class SetTheory (set : Type u) extends HasMem set, HasEmptyset set where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y --  ∃ x, x ∈ U ∧ P x y 簡寫成 ∃ x ∈ U, P x y 了！
--   powerset (S : set) : ∃ PS : set, ∀ T : set, T ∈ PS ↔ (∀ x ∈ T, x ∈ S) -- ∀ x, x ∈ T → x ∈ S 簡寫成 ∀ x ∈ T, x ∈ S 了！
--   union (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A
--   infinity : ∃ S : set, (∅ : set) ∈ S ∧ ∀ x ∈ S, (x ∪ {x}) ∈ S
--   regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = (∅ : set)
--   choice (S : set) (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T : set, T ∈ (P S) → T ≠ ∅ → f(T) ∈ T

-- end Version_3

-- /-
-- 下一個問題是 infinity 中的 x ∪ {x}
-- 他用到了二元運算的聯集 A ∪ B := union A B
-- 和把一個元素裝成一個集合的 {x} := singleton x
-- 這裡和 問題 2. 一樣，符號怎麼綁定的問題 但更嚴重的是
-- # 問題 3. 無法陳述 infinity 公理，因為原本的公理中並沒有二元運算聯集 和 singleton 的概念
-- 要先用 extensionality, replacement, emptyset, powerset 推導出 pairing {A, B} 的概念
-- 再 pairing 加上聯集公理的的集合聯集 ∪ {A, B} = A ∪ B 才有二元運算聯集
-- 而用 pairing 也能得到 {x, x} = {x} singleton
-- 也就是說光要陳述 infinity 這公理先推倒一些小 lemma 了
-- 這裡也有兩個解決方式
-- 方法 3.1
--   加上 redundant 的公理
--   反正我們知道 二元運算 union, singleton 可以被其他公理推出來
--   為了方便我們就直接加入這些公理 無傷大雅
--   (以下我們叫集合聯集 ⋃ A ∈ S, A := sUnion S，叫二元運算聯集 A ⋃ B := union A B)
--   優點：方便，數學上等價
--   缺點：看不到最乾淨的公理是哪些
-- -/

-- -- 方法 3.1 範例
-- namespace Method_3_1

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class HasUnion (set : Type u) where
--   union : set → set → set

-- instance (set : Type u) [HasUnion set] : Union set where
--   union := HasUnion.union

-- class HasSingleton (set : Type u) where
--   singleton : set → set

-- instance (set : Type u) [HasSingleton set] : Singleton set set where
--   singleton := HasSingleton.singleton

-- class SetTheory (set : Type u) extends
--   HasMem set, HasEmptyset set, HasUnion set, HasSingleton set  where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y
--   powerset (S : set) : ∃ PS : set, ∀ T : set, T ∈ PS ↔ (∀ x ∈ T, x ∈ S)
--   sUnion (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A

--   -- section redundant axioms
--   mem_union_iff (A B : set) : ∀ x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
--   mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x
--   -- end redundant axioms

--   infinity : ∃ S : set, (∅ : set) ∈ S ∧ ∀ x ∈ S, (x ∪ {x}) ∈ S -- x ∪ {x} 沒紅線了
--   regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = (∅ : set)
--   choice (S : set) (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T : set, T ∈ (P S) → T ≠ ∅ → f(T) ∈ T

-- end Method_3_1

-- /-
-- 方法 3.2
--   把公理拆成 part1, part2
--   從 part1 內推出一些 lemma 後
--   定義 part2 要求 set 上已經有 part1 結構 （和 extends 不一樣）
--   最後再讓 SetTheory extends part1, part2
--   優點：強烈區分了哪些是 axiom 哪些是 lemma
--   缺點：要維護 class 之間 extends 關係，到後面會很辛苦
--     而且不能一開始看到所有公理，喪失大局感
-- -/


-- -- 方法 3.1 範例
-- namespace Method_3_2

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class SetTheory_Part1 (set : Type u) extends HasMem set, HasEmptyset set where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y
--   powerset (S : set) : ∃ PS : set, ∀ T : set, T ∈ PS ↔ (∀ x ∈ T, x ∈ S)
--   sUnion (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A

-- namespace SetTheory_Part1

-- variable {set : Type u} [SetTheory_Part1 set]

-- def pairing [SetTheory_Part1 set] (A B : set) : set := sorry

-- theorem mem_pairing_iff (A B : set) : ∀ x, x ∈ pairing A B ↔ x = A ∨ x = B := sorry

-- def union [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : Union set where union := union

-- theorem mem_union_iff (A B : set) : ∀ x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := sorry

-- def singleton [SetTheory_Part1 set] (x : set) : set := sorry

-- instance : Singleton set set where singleton := singleton

-- theorem mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x := sorry

-- end SetTheory_Part1

-- class SetTheory_Part2 (set : Type u) [SetTheory_Part1 set] where
--   infinity : ∃ S : set, (∅ : set) ∈ S ∧ ∀ x ∈ S, (x ∪ {x}) ∈ S -- x ∪ {x} 沒紅線了

--   -- 先把 regularity, choice 註解掉，這樣最後的 SetTheory 才能正確 extends
--   -- regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = (∅ : set)
--   -- choice (S : set) (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T : set, T ∈ (P S) → T ≠ ∅ → f(T) ∈ T

-- class SetTheory (set : Type u) extends SetTheory_Part1 set, SetTheory_Part2 set

-- open SetTheory_Part1 in -- let you can write `mem_union_iff` instead of `SetTheory_Part1.mem_union_iff`
-- example (set : Type u) [SetTheory set] (A B C : set) :
--   ∀ x, x ∈ A ∪ B ∪ C ↔ x ∈ A ∨ x ∈ B ∨ x ∈ C := by
--   intro x
--   rw [mem_union_iff, mem_union_iff, or_assoc]

-- end Method_3_2


-- /-
-- 我選擇了 方法 3.2
-- 這種拆成 part1, part2 的方式還能更近一步
-- 每個公理都是自己一個 class
-- 想要怎樣的集合論就 extends 什麼公理 很有模塊化的味道
-- 而且這也比較符合真正數學的架構
-- 比如 Galos extension 的概念背後需要

-- set
--  └→ operation
--      └→ group → ring → field
--                      └→ K[x]
--                          └→ field extension
--                              ├→ algebraic element
--                              │    └→ minimal polynomial
--                              │         └→ separable / splitting field
--                              ├→ normal extension
--                              ├→ separable extension
--                              ├→ automorphism
--                              │    └→ fixed field
--                              └→ Galois group
--                                   └→ Galois extension


-- 本來就不應該就把 Galois extension 和最基礎的 field 定義在一起

-- 這裡應該可以接一個讀者練習時間
-- 試著把 regularity 裡面交集 A ∩ S 也用方法 3.2 的方式把 lemma 框架寫出來
-- (Hint : 可以先寫 specification)
-- -/




-- -- version 4
-- namespace Version_4

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class SetTheory_Part1 (set : Type u) extends HasMem set, HasEmptyset set where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y
--   powerset (S : set) : ∃ PS : set, ∀ T : set, T ∈ PS ↔ (∀ x ∈ T, x ∈ S)
--   sUnion (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A

-- namespace SetTheory_Part1

-- variable {set : Type u} [h : SetTheory_Part1 set]

-- def pairing [SetTheory_Part1 set] (A B : set) : set := sorry

-- theorem mem_pairing_iff (A B : set) : ∀ x, x ∈ pairing A B ↔ x = A ∨ x = B := sorry

-- def union [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : Union set where union := union

-- theorem mem_union_iff (A B : set) : ∀ x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := sorry

-- def singleton [SetTheory_Part1 set] (x : set) : set := sorry

-- instance : Singleton set set where singleton := singleton

-- theorem mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x := sorry

--  -- 講義裡面是用 ∀ P : set → Prop, ∀ U : set, ∃ S : set, ∀ x, x ∈ S ↔ x ∈ U ∧ x ∈ S
--  -- 我也把這句裡面的 ∃ S 改成個函數叫 specification，輸入 P, U 輸出 S
--  -- 精神類似 方法 1.2.
-- def specification [SetTheory_Part1 set] (P : set  → Prop) (U : set) : set := sorry

-- theorem mem_specification_iff (P : set → Prop) (U : set) : ∀ x, x ∈ specification P U ↔ x ∈ U ∧ P x := sorry

-- def inter [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : Inter set where inter := inter

-- theorem mem_inter_iff (A B : set) : ∀ x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := sorry

-- end SetTheory_Part1

-- class SetTheory_Part2 (set : Type u) [SetTheory_Part1 set] where
--   infinity : ∃ S : set, (∅ : set) ∈ S ∧ ∀ x ∈ S, (x ∪ {x}) ∈ S
--   regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = (∅ : set)  -- A ∩ S 沒紅線了
--   choice (S : set) (hS : S ≠ ∅) : ∃ f : P S → S, ∀ T : set, T ∈ (P S) → T ≠ ∅ → f(T) ∈ T

-- class SetTheory (set : Type u) extends SetTheory_Part1 set, SetTheory_Part2 set

-- end Version_4

-- /-
-- 呼 剩下最後一個 choice 了
-- 首先 P S 代表 powerset of S 和問題1,2一樣 我們會處理
-- 再來函數 f 是什麼 我們回顧一下講義的定義

-- Definition 8.1.
-- Let A and B be two sets.
-- 1. For a ∈ A and b ∈ B, we define (a,b) = {{a},{a,b}} and call it an ordered pair.
--   Clearly, (a,b) = (x,y) if and only if a = x and b = y.
-- 2. The set-theoretic product of A and B is defined to be
--   the set A × B = {(a,b) | a ∈ A and b ∈ B}.

-- Definition 9.1.
-- Let A and B be two sets.
-- 1. Any subset ∼ of A × B is called a relation from A to B

-- Definition 11.1.
-- Let A and B be two sets.
-- 1. A function f ∶ A → B is defined to be a relation, denoted by f, from A to B
--   such that for any x ∈ A there exists a unique y ∈ B such that (x,y) ∈ f.
--   In this case, for x ∈ A, we denote such a unique y ∈ B by f(x),

-- 對於集合 A B f, 我們會定義一個謂詞叫做 is_function A B f 表示
--   f ⊆ A ×ˢ B ∧ ∀ x ∈ A, ∃! y ∈ B, (x, y)ˢ ∈ f
-- 其中 A ×ˢ B 是 A, B 的 set-theoretic product (or just call product)
-- 而 (x, y)ˢ 是 x, y 的 ordered pair
-- （上標 ˢ 為了和 lean 的 Prod 做區分，其實不區分也行，就要手動給更多型別提示給lean，才不會有歧義）
-- 所以要陳述 choice 也必須先有 product, ordered pair 的概念和問題3.一樣 我們也會處理
-- （Hint: Definition 8.1.1 最後的 Clearly, (a,b) = (x,y) iff a = x and b = y 很不 Clearly，實際寫時分case討論很辛苦）
-- 最嚴重的是講義最後一句話
-- `In this case, for x ∈ A, we denote such a unique y ∈ B by f(x)`
-- 和問題1.類似 不能因為 ∀ x ∈ A, ∃! y ∈ B, (x, y) ∈ f 中有 ∃! y 就直接把 y 取出來
-- （和有沒有unique無關，原本 y 就是只活在 ∃! y ∈ B, (x, y) ∈ f 這命題裡）
-- 也和問題2.類似 f(x) 這種符號怎麼綁定到 y 上
-- 單看 f(x) 其實很奇怪 f, x 都是一個集合
-- 就如同對於集合 A, B 寫下 A(B) 就不知道什麼意思
-- 我們要用某種方式把 is_funciton A B f 這件事情隱含的告訴 lean
-- 或許可以參考 mathlib 裡面 homomorphisms, coe 的設計 但這又要解釋太複雜的 lean 語法設計了

-- 所以最後 我也給出兩個解決方式
-- 方法 4.1.
--   放棄 f(x)，要寫 f(T) ∈ T 就乖乖寫 ∃ x ∈ T, (T, x) ∈ f
--   優點：簡單而且正確
--   缺點：本質上沒解決問題 雖然 choice 公理可以陳述了 但後續函數的使用都會卡卡的
-- -/
-- -- 方法 4.1. 範例
-- namespace Method_4_1

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- def HasMem.subset {set : Type u} [HasMem set] (S T : set) : Prop := ∀ x ∈ S, x ∈ T

-- instance (set : Type u) [HasMem set] : HasSubset set where -- 加入 ⊆ 符號 為了讓 powerset 更簡單
--   Subset := HasMem.subset

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class HasPowerset (set : Type u) where
--   powerset : set → set

-- -- lean 裡面沒有專門定義 powerset notation 的 class, 我們就自己定義符號了
-- -- prefix 表示前綴 :100 表示優先級
-- prefix:100 "𝒫 " => HasPowerset.powerset

-- class SetTheory_Part1 (set : Type u) extends HasMem set, HasEmptyset set, HasPowerset set where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y
--   mem_powerset_iff (S : set): ∀ T : set, T ∈ 𝒫 S ↔ T ⊆ S -- powerset 公理也做了相應改動
--   sUnion (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A

-- namespace SetTheory_Part1

-- variable {set : Type u} [SetTheory_Part1 set]

-- def ordered_pair [SetTheory_Part1 set] (x y : set) : set := sorry

-- notation:150 "(" a:150 ", " b:150 ")ˢ" => ordered_pair a b

-- theorem ordered_pair_inj (a b x y : set) : (a, b)ˢ = (x, y)ˢ ↔ a = x ∧ b = y := sorry

-- def product [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : SProd set set set -- for notation ×ˢ
--   where sprod := product

-- theorem mem_product_iff (A B : set) : ∀ x, x ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ := sorry

-- def is_function (A B f : set) : Prop := f ⊆ A ×ˢ B ∧ ∀ x ∈ A, ∃! y ∈ B, (x, y)ˢ ∈ f

-- end SetTheory_Part1

-- open SetTheory_Part1 in -- let you can write `is_function` instead of `SetTheory_Part1.is_function`
-- class SetTheory_Part2 (set : Type u) [SetTheory_Part1 set] where
--   choice (S : set) (hS : S ≠ ∅) : ∃ f, (is_function (𝒫 S) S f) ∧
--     (∀ T, T ∈ (𝒫 S) → T ≠ ∅ → (∃ x ∈ T, (T, x)ˢ ∈ f))

-- class SetTheory (set : Type u) extends SetTheory_Part1 set, SetTheory_Part2 set

-- end Method_4_1


-- /-
-- 方法 4.2
--   用 lean 的選擇公理 Classical.choice
--   把 ∃! y ∈ B, (x, y)ˢ ∈ f 中的 y 取出來
--   定義一個函數（lean 函數）叫 toFun
--   他輸入 (hf : is_function A B f) 和 (hx : x ∈ A)
--   輸出一個集合 (toFun hf hx : set)
--   再附帶兩個小 lemma 確保 toFun hf hx ∈ B ∧ (x, toFun hf hx) ∈ f 而且
--   toFun hf hx 是唯一一個滿足這性質的人 i.e. if y ∈ B ∧ (x, y) ∈ f then y = toFun hf hx
--   優點：toFun hf hx 用起來像是 f(x) 了
--     而且強制要求提供 (hf : is_function A B f) 和 (hx : x ∈ A) 這兩個證明
--     媽媽再也不用擔心我 f(x) 的 x 不在 f 的定義域內了
--   缺點：什麼 竟然要用到 lean 的選擇公理 Classical.choice 嗎 -/
-- #check Classical.choice /-
--     關於這個的討論要深入去看 Type theroy 的層級機制怎麼運作的
--     還有強制提供 x ∈ A 的證明有時候會不方便
--     一般數學可以寫 f(x + y)，用 toFun 會強制你證明 x + y ∈ A
--     尤其當表達式變得複雜時，toFun 會讓你寸步難行
--     或許用一些自動證明的 tactic, subtype, junk value 可以做一些改善
-- -/

-- -- 方法 4.2 範例

-- namespace Method_4_2

-- class HasMem (set : Type u) where
--   mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- def HasMem.subset {set : Type u} [HasMem set] (S T : set) : Prop := ∀ x ∈ S, x ∈ T

-- instance (set : Type u) [HasMem set] : HasSubset set where
--   Subset := HasMem.subset

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class HasPowerset (set : Type u) where
--   powerset : set → set

-- prefix:100 "𝒫 " => HasPowerset.powerset

-- class SetTheory_Part1 (set : Type u) extends HasMem set, HasEmptyset set, HasPowerset set where
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)
--   replacement (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y):
--     ∀ U : set, ∃ S : set, ∀ y, y ∈ S ↔ ∃ x ∈ U, P x y
--   mem_powerset_iff (S : set): ∀ T : set, T ∈ 𝒫 S ↔ T ⊆ S
--   sUnion (S : set) : ∃ U : set, ∀ x, x ∈ U ↔ ∃ A ∈ S, x ∈ A

-- namespace SetTheory_Part1

-- variable {set : Type u} [SetTheory_Part1 set]

-- def ordered_pair [SetTheory_Part1 set] (x y : set) : set := sorry

-- notation:150 "(" a:150 ", " b:150 ")ˢ" => ordered_pair a b

-- theorem ordered_pair_inj (a b x y : set) : (a, b)ˢ = (x, y)ˢ ↔ a = x ∧ b = y := sorry

-- def product [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : SProd set set set -- for notation ×ˢ
--   where sprod := product

-- theorem mem_product_iff (A B : set) : ∀ x, x ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ := sorry

-- def is_function (A B f : set) : Prop := f ⊆ A ×ˢ B ∧ ∀ x ∈ A, ∃! y ∈ B, (x, y)ˢ ∈ f

-- noncomputable def toFun -- 使用 Classical.choose 定義函數（lean 函數）的話，要在前面加 noncomputable
--   {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A) : set :=
--   Classical.choose (hf.2 x hx)
--   -- 有了證明 hf.2 x hx : ∃! y, y ∈ B ∧ (x, y)ˢ ∈ f
--   -- 回顧 (∃! y, P y) 的定義是 (∃ y, (P y) ∧ (∀ z, P z → z = y))
--   -- 用 Classical.choose 就能造出一個 (Classical.choose (hf.2 x hx) : set)
--   -- 而且 Classical.choose_spec (hf.2 x hx) 保證
--   -- 1. Classical.choose (hf.2 x hx) ∈ B ∧ (x, Classical.choose (hf.2 x hx))ˢ ∈ f)
--   -- 2. ∀ z, z ∈ B ∧ (x, z)ˢ ∈ f)→ z = Classical.choose (hf.2 x hx)

-- theorem toFun_spec
--   {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A) :
--   toFun hf hx ∈ B ∧ (x, toFun hf hx)ˢ ∈ f := by
--   rw [toFun]
--   exact (Classical.choose_spec (hf.2 x hx)).1

-- theorem toFun_unique
--   {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A)
--   {y : set} (hy : y ∈ B) (hxyf : (x, y)ˢ ∈ f) : y = toFun hf hx := by
--   rw [toFun]
--   have := (Classical.choose_spec (hf.2 x hx)).2
--   exact this y ⟨hy, hxyf⟩

-- end SetTheory_Part1

-- open SetTheory_Part1 in
-- class SetTheory_Part2 (set : Type u) [SetTheory_Part1 set] where
--   -- 因為後續的敘述中需要 hf : is_function (𝒫 S) S f
--   -- 從單純的 ∃ f, (is_function (𝒫 S) S f) ∧ (∀ T,..)
--   -- 變成了 ∃ f, ∃ (hf : is_function (𝒫 S) S f), (∀ T,..)
--   -- 本質上都會是 and 的意思
--   choice (S : set) (hS : S ≠ ∅) : ∃ f, ∃ (hf : is_function (𝒫 S) S f),
--     ∀ T, (hT : T ∈ (𝒫 S)) → T ≠ ∅ → (∃ x ∈ T, toFun hf hT ∈ f)

-- class SetTheory (set : Type u) extends SetTheory_Part1 set, SetTheory_Part2 set

-- end Method_4_2

-- /-
-- 到這裡基本上可以收工了
-- 沒想到講義寫起來那麼順的定義改成 lean 後會問題那麼多
-- 回顧一下
-- 問題1. 有 ∃ x, P x 但拿不出 x
-- 問題2. 綁定 notation
-- 問題3. 公理間有依賴關係
-- 問題4. 從 ∀ x, ∃! y, (x,y) ∈ f 實作函數符號 f(x)
-- 都是些紙筆數學中微妙不會注意的問題
-- 不知道到底是 lean 的語法麻煩 還是紙筆數學真的 handwaving 的地方

-- 總之，用上以上所有的技巧，我們最後可以得到 zfc 公理再 lean 的版本了！（還要一推些sorry）
-- 將class拆分更細的版本可見 `axioms.lean`
-- -/


-- namespace Version_final

-- class HasMem (set : Type u) where mem : set → set → Prop

-- instance (set : Type u) [HasMem set] : Membership set set where
--   mem := HasMem.mem

-- def HasMem.subset {set : Type u} [HasMem set] (S T : set) : Prop := ∀ x ∈ S, x ∈ T

-- instance (set : Type u) [HasMem set] : HasSubset set where
--   Subset := HasMem.subset

-- class HasEmptyset (set : Type u) where
--   emptyset : set

-- instance (set : Type u) [HasEmptyset set] : EmptyCollection set where
--   emptyCollection := HasEmptyset.emptyset

-- class HasPowerset (set : Type u) where
--   powerset : set → set

-- prefix:100 "𝒫 " => HasPowerset.powerset

-- class HassUnion (set : Type u) where
--   sUnion : set → set

-- prefix:110 "⋃₀ " => HassUnion.sUnion

-- class SetTheory_Part1 (set : Type u) extends
--   HasMem set, HasEmptyset set, HasPowerset set, HassUnion set  where

--   -- # 1. axiom of extensionality:
--   -- two sets are equal if and only if they have the same elements
--   -- that is, for any x, one has x ∈ A ↔ x ∈ B.
--   extensionality (A B : set) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B

--   -- # 2. axiom of empty set:
--   -- there exists a set S such that for all x, the statement x ∈ S is false
--   not_mem_emptyset : ∀ x, ¬ x ∈ (∅ : set)

--   -- # 3. axiom of replacement:
--   -- if P(x,y) is a predicate in two variables such that
--   -- for each x, there is a unique y such that P(x,y) holds,
--   -- then for every set U, {y | there exists x ∈ U such that P(x,y) holds} is a set
--   replacement (P : set → set → Prop) (U : set) : set
--   mem_replacement_iff (P : set → set → Prop) (hP : ∀ x, ∃! y, P x y) (U : set) :
--      ∀ y, y ∈ replacement P U ↔ ∃ x ∈ U, P x y

--   -- # 4. axiom of power set:
--   -- if S is a set, then the collection of all subsets of S is also a set, that is,
--   -- if S is a set, then the set {T | T ⊆ S} is a set.
--   mem_powerset_iff (S : set): ∀ T, T ∈ 𝒫 S ↔ T ⊆ S

--   -- # 5. axiom of union:
--   -- if S is a set, then the union of all sets that are elements in S is also a set, that is,
--   -- if S is a set then the set ⋃ A ∈ S, A = {x ∈ A | A ∈ S} is a set.
--   mem_sUnion_iff (S : set) : ∀ x, x ∈ ⋃₀ S ↔ ∃ A ∈ S, x ∈ A

-- namespace SetTheory_Part1

-- variable {set : Type u} [SetTheory_Part1 set]

-- -- # Proposition 15.1.1
-- -- The axioms of extensionality, empty set and replacement imply the axiom of specification,
-- -- that is, if U is a set and if P(x) is a predicate, then {x ∈ U | P(x)} is a set.
-- def specification [SetTheory_Part1 set] (P : set  → Prop) (U : set) : set := sorry

-- theorem mem_specification_iff (P : set → Prop) (U : set) : ∀ x, x ∈ specification P U ↔ x ∈ U ∧ P x := sorry

-- -- # Proposition 15.1.2
-- -- The axioms of empty set, power set, and replacement together imply
-- -- that the collection of two sets is a set, which is called the axiom of pairing.
-- def pairing [SetTheory_Part1 set] (A B : set) : set := sorry

-- theorem mem_pairing_iff (A B : set) : ∀ x, x ∈ pairing A B ↔ x = A ∨ x = B := sorry

-- -- corollary of Proposition 15.1.2
-- def union [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : Union set where union := union

-- theorem mem_union_iff (A B : set) : ∀ x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := sorry

-- def singleton [SetTheory_Part1 set] (x : set) : set := sorry

-- instance : Singleton set set where singleton := singleton

-- theorem mem_singleton_iff (x : set) : ∀ y, y ∈ ({x} : set) ↔ y = x := sorry

-- -- # Proposition 15.1.3.
-- -- It holds that if S is a set, then the intersection of all sets that are elements in S is also a set,
-- -- which is called the axiom of intersection.
-- def sInter [SetTheory_Part1 set] (S : set) : set := sorry

-- prefix:110 "⋂₀ " => sInter

-- theorem mem_sInter_iff (S : set) : ∀ x, x ∈ ⋂₀ S ↔ ∀ A ∈ S, x ∈ A := sorry

-- def inter [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : Inter set where inter := inter

-- theorem mem_inter_iff (A B : set) : ∀ x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := sorry


-- -- # Definition 8.1
-- -- Let A and B be two sets.
-- -- 1. For a ∈ A and b ∈ B, we define (a,b) = {{a},{a,b}} and call it an ordered pair.
-- -- Clearly, (a,b) = (x,y) if and only if a = x and b = y.
-- -- 2. The set-theoretic product of A and B is defined to be
-- -- the set A × B = { (a,b) | a ∈ A and b ∈ B}.
-- def ordered_pair [SetTheory_Part1 set] (x y : set) : set := sorry

-- notation:150 "(" a:150 ", " b:150 ")ˢ" => ordered_pair a b

-- theorem ordered_pair_inj (a b x y : set) : (a, b)ˢ = (x, y)ˢ ↔ a = x ∧ b = y := sorry

-- def product [SetTheory_Part1 set] (A B : set) : set := sorry

-- instance : SProd set set set where sprod := product

-- -- Hint : use specification on (𝒫 (𝒫 (A ∪ B)))
-- theorem mem_product_iff (A B : set) : ∀ x, x ∈ A ×ˢ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = (a, b)ˢ := sorry


-- -- # Definition 11.1.
-- -- Let A and B be two sets.
-- -- A function f ∶ A → B is defined to be a relation, denoted by f, from A to B
-- -- such that for any x ∈ A there exists a unique y ∈ B such that (x,y) ∈ f.
-- -- In this case, for x ∈ A, we denote such a unique y ∈ B by f(x),
-- def is_function (A B f : set) : Prop := f ⊆ A ×ˢ B ∧ ∀ x ∈ A, ∃! y ∈ B, (x, y)ˢ ∈ f

-- noncomputable def toFun {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A) : set :=
--   Classical.choose (hf.2 x hx)

-- theorem toFun_spec {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A) :
--   toFun hf hx ∈ B ∧ (x, toFun hf hx)ˢ ∈ f := by
--   rw [toFun]
--   exact (Classical.choose_spec (hf.2 x hx)).1

-- theorem toFun_unique {A B f : set} (hf : is_function A B f) {x : set} (hx : x ∈ A)
--   {y : set} (hy : y ∈ B) (hxyf : (x, y)ˢ ∈ f) : y = toFun hf hx := by
--   rw [toFun]
--   have := (Classical.choose_spec (hf.2 x hx)).2
--   exact this y ⟨hy, hxyf⟩

-- -- nice exercise
-- theorem toFun_ext {A B f g : set} (hf : is_function A B f) (hg : is_function A B g)
--   : f = g ↔ ∀ a, (ha : a ∈ A) → toFun hf ha = toFun hg ha := sorry

-- end SetTheory_Part1

-- open SetTheory_Part1

-- class SetTheory_Part2 (set : Type u) [SetTheory_Part1 set] where

--   -- # 6. axiom of infinity:
--   -- there exists a set S such that ∅ ∈ S and if x ∈ S then x ∪ {x} ∈ S.
--   infinity : set
--   empty_mem_infinity : ∅ ∈ infinity
--   succ_mem_infinity : ∀ x ∈ infinity, x ∪ {x} ∈ infinity

--   -- # 7. axiom of regularity:
--   -- every nonempty set S has an element which has empty intersection with S, that is,
--   -- if S ≠ ∅, then there exists A ∈ S such that A ∩ S = ∅.
--   regularity (S : set) (hS : S ≠ ∅) : ∃ A ∈ S, A ∩ S = ∅

--   -- # 8. axiom of choice:
--   -- if S is a nonempty set and P(S) denotes the power set of S,
--   -- then there exists a function f ∶ P(S) → S such that f(T) ∈ T for any nonempty set T ∈ P(S).
--   choice : set → set
--   choice_is_function (S : set) (hS : S ≠ ∅) : is_function (𝒫 S) S (choice S)
--   choice_mem (S : set) (hS : S ≠ ∅) : ∀ T, (hT : T ∈ 𝒫 S) → T ≠ ∅ → toFun (choice_is_function S hS) hT ∈ T

-- class SetTheory (set : Type u) extends SetTheory_Part1 set, SetTheory_Part2 set

-- -- usage example
-- section usage_example

-- variable {set : Type u} [SetTheory set]

-- open SetTheory_Part1  SetTheory_Part2

-- -- # Theorem 18.2

-- def zero : set := ∅

-- def succ (n : set) : set := n ∪ {n}

-- def is_infinity (S : set) : Prop := zero ∈ S ∧ ∀ n ∈ S, succ n ∈ S

-- theorem infinity_is_infinity : is_infinity (infinity : set) := ⟨empty_mem_infinity, succ_mem_infinity⟩

-- def nat : set := specification (fun x ↦ ∀ (S : set), is_infinity S → x ∈ S) infinity

-- end usage_example

-- end Version_final
