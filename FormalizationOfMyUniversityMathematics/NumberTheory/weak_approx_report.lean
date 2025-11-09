import Mathlib
/-
代數數論的期中報告，請於 11 月 12 日（星期三）中午 12:00 前寄給我。
1. 頁數約 3–5 頁的 pdf 檔案，請使用英文撰寫。
2. 內容架構建議：
 - 主題介紹與動機說明
 - 基本符號與定義
 - 主定理（Main Theorem）的敘述
 - 自行撰寫的證明與思考過程
 - 參考文獻
-/

/-
主題：弱逼近定理（Weak Approximation Theorem）
（基本背景與定理應用，可是視做中國剩餘定理的推廣)
值得注意的是這個證明參考的是 lean 證明助手裡 mathlib 的實作與
https://github.com/smmercuri/mathlib4/blob/4e0ee3a83cb68f70cca116898ab4380e29cfe210/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean
這個 mathlib fork 裡的實作。
lean 裡面多處理了一些 type class 的細節，這些細節在手寫證明時可以忽略。
還有我繞開了兩個絕對值等價 iff ∃ c > 0, |·|₁ = |·|₂ ^ c 的證明
直接用證明了兩個絕對值誘導同一個拓樸 iff 在field上定義同一個預序。
-/

/-
基本符號：
K field
|.| : K → ℝ 稱作 K 上的絕對值
（以下我們只會關注同一個 field K, 我們就只說 |.| 是一個絕對值）
如果
1. |xy| = |x||y|
2. |x| ≥ 0
3. |x| = 0 iff x = 0
4. |x + y| ≤ |x| + |y|
-/
#check AbsoluteValue

/-
簡單 lemma :
|1| = 1
|-x| = |x|
|x⁻¹| = |x|⁻¹
-/

/-
例子：
定義 |.|_trivial by
|x|_trivial = if x = 0 then 0 else 1
|.|_trivial 是一個絕對值

令|.| 為一個絕對值以下幾個等價：
1. |.| ≠ |.|_trival
2. ∃ x ≠ 0, |x| ≠ 1
3. ∃ x, 0 < |x| < 1
4. ∃ x, |x| > 1
任何一個成立我們就叫 |.| 是 nontrivial 的
-/
#check AbsoluteValue.trivial
#check AbsoluteValue.IsNontrivial
#check AbsoluteValue.isNontrivial_iff_ne_trivial
#check AbsoluteValue.IsNontrivial.exists_abv_gt_one
#check AbsoluteValue.IsNontrivial.exists_abv_lt_one

/-
證明：
1 -> 2 -> 3 -> 4 -> 1
1 -> 2: ∃ x, |x| ≠ |x|_trival
if x = 0 then 0 = |x| ≠ |x|_trivial = 0 contradiction
if x ≠ 0 then |x| ≠ |x|_trival = 1, this x exaclty is we want
2 -> 3 : let x ≠ 0, |x| ≠ 1
case |x| < 1, then x ≠ 0 → |x| > 0, done
case |x| > 1, consider |x⁻¹| = |x|⁻¹ < 1 and x ≠ 0 → x⁻¹ ≠ 0 → |x|⁻¹ > 0, done
3 → 4 : let 0 < |x| < 1, then |x⁻¹| = |x|⁻¹ > 1
4 → 1 : |x| > 1 but ∀ x, |x|_trival ≤ 1, done
-/


/-
注意 定義 d(x,y) = |x-y| 可以讓 K 變成一個 metric space 進而變成一個拓樸空間
令 |.|₁, |.|₂ 以下幾個性質等價
1. |x|₁ ≤ |y|₁ ↔ |x|₂ ≤ |y|₂
2. |x|₁ < 1 ↔ |x|₂ < 1
3. |.|₁, |.|₂ 誘導同一個拓樸
任何一個成立我們就叫 |.|₁, |.|₂ 是等價的
-/
#check AbsoluteValue.IsEquiv
#check AbsoluteValue.isEquiv_iff_lt_one_iff
#check AbsoluteValue.isEquiv_iff_isHomeomorph
#check AbsoluteValue.isEquiv_of_lt_one_imp

/-
證明：1 ↔ 2, 2 ↔ 3

1 → 2 :
let |x|₁ ≤ |y|₁ ↔ |x|₂ ≤ |y|₂ hold for all x, y
only show |x|₁ < 1 → |x|₂ < 1
let |x|₁ < 1.
then |x|₁ ≤ 1 = |1|₁ → |x|₂ ≤ |1|₁ = 1
if |x|₂ = 1 then |x|₂ ≥ 1 → |x|₁ ≥ 1, contradiciton
thus |x|₂ < 1. done

2 → 1 :
let |x|₁ < 1 ↔ |x|₂ < 1 hold for all x
show |x|₁ ≤ |y|₁ ↔ |x|₂ ≤ |y|₂
which is equiv to |y|₁ < |x|₁ ↔ |y|₂ < |x|₂
if x = 0 then |y|₁ < 0 ↔ False ↔ 0 < |x|₂
if x ≠ 0 then
|y|₁ < |x|₁ ↔ |y/x|₁ < 1 ↔ |y/x|₂ < 1 ↔ |y|₂ < |x|₂, done

2 → 3 : (first nontrivial proof)
let |x|₁ < 1 ↔ |x|₂ < 1 hold for all x (*)
let U be a open set in the topo induce by |.|₁
(i.e. ∀ x ∈ U, ∃ r > 0, ∀ y, |x - y|₁ < r → y ∈ U)
to show U is a open set in the topo induce by |.|₂
if |.|₂ is triv, then
∀ x, {x} = {y | |x - y|₂ < 1/2} is open in |.|₂
→ the topo induce by |.|₂ is discreate topo → U is open in |.|₂
let |.|₂ be nontriv.
let x ∈ U, since U is open in |.|₁, let r > 0,
  ∀ y, |x - y|₁ < r → y ∈ U
since |.|₂ is nontriv, let z s.t. 0 < |z|₂ < 1
by (*), we have 0 < |z|₁ < 1 (and 0 < |z|₂ → z ≠ 0 → 0 < |z|₁)
since r > 0, 0 < |z|₁ < 1, we must can find n ∈ ℕ (ℕ = {0, 1, 2, ...}) s.t.
  |z ^ n|₁ = |z|₁ ^ n < r
notice R := |z|₂ ^ n > 0
now, let |x - y|₂ < R
we have |x - y|₂ < R = |z|₂ ^ n = |z ^ n|₂
→ |(x - y)/(z ^ n)|₂ < 1
→ |(x - y)/(z ^ n)|₁ < 1 (by (*))
→ |x - y|₁ < |z ^ n|₁ < r
→ y ∈ U
this show any open set in |.|₁ is a open set in |.|₂
simiarly and open set in |.|₂ also open in |.|₁
thus |.|₁, |.|₂ induce the same topo, done.

3 → 1 :
let |.|₁, |.|₂ induce the same topo.
let |x|₁ < 1 ↔ |x|₂ < 1 hold for all x (*)
notice
|x|₁ < 1
↔ x ^ n → 0 as n → ∞ in |.|₁
↔ x ^ n → 0 as n → ∞ in |.|₂ (since |.|₁, |.|₂ induce the same topo)
|x|₂ < 1
done.
-/

/-
remark, 透過 等價條件 1. 我們很容易檢查這真的是一個絕對值之間的等價關係
K 上的絕對值的等價類就叫做 K 上的一個 place

lean 裡面的實作用另一種方式刻畫了
|.|₁, |.|₂ induce the same topo 這件事
考慮 (K, |.|₁) (lean 叫做 WithAbs) 這個拓樸空間 是 K 附上 |.|₁ induce topo
而 (K, |.|₂) 這拓樸空間 是 K 附上 |.|₂ induce topo
令 id : (K, |.|₁) → (K, |.|₂), x ↦ x
（這個映射在lean 裡叫做 WithAbs.equivWithAbs）
這個映射是 Homeomorph 就代表 |.|₁, |.|₂ induce the same topo on K
-/
