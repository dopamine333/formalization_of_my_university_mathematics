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

在這份文件中，我們會建立field上絕對值的記號
他可以induce一些有趣的topo, order的結構在field上
並介紹絕對值之間的等價性和nontrivarl條件
最後證明 weak approx thm
某種意義上說了field上不等價的絕對值真的是幾乎獨立的
in the sense that, 你可以找到一個元素同時在好幾個絕對值上任意靠近好幾個元素
-/

/-
基本符號：
K field，|.| : K → ℝ 稱作 K 上的絕對值
（以下我們只會關注同一個 field K, 我們就只說 |.| 是一個絕對值）
如果
1. |x| ≥ 0
2. |x| = 0 iff x = 0
3. |x + y| ≤ |x| + |y|
4. |xy| = |x||y|
前三個條件讓 d(x,y) = |x-y| 在 K 上定義了個 metric的結構 進而產生一個拓樸
顯然所有field的運算+,*,-,⁻¹都是連續的（x ↦ x⁻¹ 在 x ≠ 0 連續）
（所有證明都和實數的四則運算是連續的證明相同）
而第四個乘法可拆開的條件 加上 field 中可以做除法
拓樸上允許你考慮 xⁿ 這個重要序列與絕對值的關係
序結構上也讓你把 |x|ⁿ < |y|ᵐ 複雜的不等式化簡成 |z| < 1 只要 1 做比較

我們一個一個介紹更多定義與結果

-/
#check AbsoluteValue

/-
例子：
定義 |.|_trivial by
|x|_trivial = if x = 0 then 0 else 1
很簡單檢查這是個絕對值

我們說一個絕對值是 |.| nontriv 如果 |.| ≠ |.|_trival
等價的，滿足以下的任何條件
1. |.| ≠ |.|_trival
2. ∃ x ≠ 0, |x| ≠ 1
3. ∃ x, 0 < |x| < 1
4. ∃ x, |x| > 1
證明條件等價：
1 ↔ 2 絕對值一定會會有 |0| = 0 ，兩個絕對值不相等一定是在非零的地方不相等
2 → 3 對 |x| ≠ 1 分情況討論，如果 0 < |x| < 1 那就做完了 否則 1 < |x| 則取 x⁻¹ 就能得到 0 < |x⁻¹| < 1
3 → 4 在取一次 x⁻¹ 就好
4 → 1 根據定義 |x|_trival ≤ 1, ∀ x ∈ K

尤其第三個條件 ∃ x, 0 < |x| < 1 允許我們考慮
|xⁿ| = |x|ⁿ → 0 as n → ∞ 所以只要取夠大的 n ，我們就有 ∀ ε > 0, ∃ x, 0 < |x| < r
類似的 第四個條件也能嚷我們得到 ∀ M > 0, ∃ x, |x| > M
這也能很快的給出 finite field 上只有 trivial 絕對值的結果
-/
#check AbsoluteValue.trivial
#check AbsoluteValue.IsNontrivial
#check AbsoluteValue.isNontrivial_iff_ne_trivial
#check AbsoluteValue.IsNontrivial.exists_abv_gt_one
#check AbsoluteValue.IsNontrivial.exists_abv_lt_one

/-
接著我們來定義兩個絕對值的等價性
我們說 |.|₁, |.|₂ 等價如果 以下任何一個等價條件成立
1. |x|₁ ≤ |y|₁ ↔ |x|₂ ≤ |y|₂, ∀ x, y
2. |x|₁ < 1 ↔ |x|₂ < 1, ∀ x
3. ∃ β > 0, |.|₁ ^ β = |.|₂
4. |.|₁, |.|₂ 誘導同一個拓樸
-/
#check AbsoluteValue.IsEquiv
#check AbsoluteValue.isEquiv_iff_lt_one_iff
#check AbsoluteValue.isEquiv_iff_isHomeomorph

/-
證明條件等價 1 ↔ 2, 2 → 3 → 4 → 2

1 ↔ 2 :
注意到
∀ x,y, |x|₁ ≤ |y|₁ ↔ |x|₂ ≤ |y|₂
等價 ∀ x,y, |y|₁ < |x|₁ ↔ |y|₂ < |x|₂
而又因為 |x|₁ < |y|₁ ↔ |x/y|₁ < 1 for y ≠ 0, done

2 → 3
let ∀ x, |x|₁ < 1 ↔ |x|₂ < 1
如果 |.|₁ is triv 那 for all x ≠ 0,
|x|₁ = 1 thus |x|₁ < 1 is false and |x⁻¹|₁ < 1 is false
by assumption,|x|₂ < 1 is false and |x⁻¹|₂ < 1 is false
we must have |x|₂ = 1
所以 |.|₂ 也是 triv
那麼取 c = 1 就做完了
如果 |.|₁ 不是 triv 那根據剛剛的說法 |.|₂ 也不會是 triv
這裡的關鍵是去觀察 對於整數 n,m, m≠0 和非零 x,y 我們有
|x|₁ ^ (n/m) < |y|₁
↔ |x|₁ⁿ < |y|₁ᵐ
↔ |xⁿ/yᵐ|₁ < 1
↔ |xⁿ/yᵐ|₂ < 1
↔ |x|₂ⁿ < |y|₂ᵐ
↔ |x|₂ ^ (n/m) < |y|₂
更進一步我們就有 ∀ x,y ≠ 0, ∀ q₁, q₂ ∈ ℚ
if   |x|₁ ^ q₁ < |y|₁ < |x|₁ ^ q₂
then |x|₂ ^ q₁ < |y|₂ < |x|₂ ^ q₂

這是件很重要的事情 你可以隨便挑一個 |x| ≠ 1 的元素當比例尺
透過 |x| ^ q, q ∈ ℚ 在整個 ℝ>0 畫出刻度
任何一個元素 y ≠ 0 他的絕對值就會被釘在這刻度的某個位置
更重要的是 y 在透過 |.|₁, |.|₂ 畫出的刻度中的位置會一模壹樣
更explicty 的構造是：
因為 |.|₁ 是 nontriv, ∃ x, |x|₁ > 1
let y ≠ 0, then |y|₁ > 0
我們一定可以找到一個 α ∈ ℝ 使得 |y|₁ = |x|₁ ^ α
拿兩個有理數數列 {qₙ}, {pₙ} 分別從上面下面趨近 α
我們就有
|x|₁ ^ qₙ < |x|₁ ^ α = |y|₁ < |x|₁ ^ pₙ for all n
→ |x|₂ ^ qₙ < |y|₂ < |x|₂ ^ pₙ for all n
take n → ∞, then |y|₂ = |x|₂ ^ α.
最後因為 |x|₁ > 1 透過取⁻¹一下可以得到 |x|₂ > 1
我們可以找到 β > 0 使得 |x|₂ = |x|₁ ^ β
那麼對於所有 y ≠ 0, 我們有 |y|₂ = |x|₂ ^ α = |x|₁ ^ α β = |y|₁ ^ β for some α
that is |.|₁ ^ β = |.|₂.

3 → 4,
如果 ∃ β > 0, |.|₁ ^ β = |.|₂ 那 |.|₁ 中的開球自然也是 |.|₂ 的開球
所以 |.|₁, |.|₂ 誘導同一個拓樸

4 → 2,
如果 |.|₁, |.|₂ 誘導同一個拓樸
那我們就有
|x|₁ < 1
↔ x ^ n → 0 as n → ∞ in |.|₁
↔ x ^ n → 0 as n → ∞ in |.|₂
|x|₂ < 1

done
-/

/-
remark
很容易檢查這樣定出來的絕對值等價真的是一個等價關西
K 上絕對值的一個等價類就叫做 K 的 place
更進一步還能去討論絕對值是不是 Archimedean
對應到 infilty place 和 finity place 的記號 這裡就不繼續展開了
還有一點有趣的點可以提出來 下面 weak apporm 的證明
其實只有用到 |x|₁ < 1 ↔ |x|₂ < 1, ∀ x 這的條件當作等價定義
或許直接以這條件當作定義能直接的進入到  weak apporm  ?

-/
#check AbsoluteValue.isEquiv_iff_exists_rpow_eq

/-
介紹最主要定理：
thm. weak apporm
let {|.|ᵢ}_(i ∈ I) be a finite collection of nontrivial,
(pairwise) inequiv absolute value on a field K.
then for all {zᵢ}_(i ∈ I) ⊆ K,
there exist a element in K arbtriy close to zᵢ in |.|ᵢ for each i ∈ I
i.e. ∀ r > 0, ∃ x ∈ K, ∀ i ∈ I, |x - zᵢ|ᵢ < r
-/

/-
first we need some lemma
1. |.|₁, |.|₂ be nontri, if ∀ x, |x|₁ < 1 → |x|₂ < 1 then |.|₁, |.|₂ are equiv
2. |.|₁, |.|₂ be nontri inequiv, then ∃ a, |a|₁ > 1 ∧ |a|₂ < 1

pf of lemma
1. |.|₁, |.|₂ are equiv 等價條件是 ∀ x, |x|₁ < 1 ↔ |x|₂ < 1
我們已經有正向敘述 假設反向敘述是錯的話
then ∃ x, |x|₁ ≥ 1 and |x|₂ < 1
我們手上的  ∀ x, |x|₁ < 1 → |x|₂ < 1 條件其實告訴我們
兩個元素在 |.|₁ 下的大小關係會被保持到 |.|₂ 上
也就是我們只要找到一組 a,b ≠ 0 使得 |a|₁ < |b|₁, |b|₂ < |a|₂
我們就得到 |a/b|₁ < 1 → |a/b|₂ < 1 < |a/b|₂ 了 矛盾
這很容易做到 因為 |.|₁ is nontri,
take y s.t. 0 < |y|₁ < 1, by assumption, 0 < |y|₂ < 1
since |x|₂ < 1, take n large 那我們就有 |xⁿ|₂ < |y|₂  而且 |xⁿ|₁ ≥ 1 > |y|₂ 了。

2. 第一個 lemma 的逆否命題 直接給我們
 ∃ a, |a|₁ < 1 and |a|₂ ≥ 1
 ∃ b, |b|₁ ≥ 1 and |b|₂ < 1
取 b/a 就結束了
-/

/-
pf of weak approx
claim : for any finite collection of nontrivial, inequiv absolute value {|.|ᵢ}_(i ∈ I),
we have for all i ∈ I, ∃ aᵢ, |aᵢ|ᵢ > 1 and ∀ j ≠ i, |aᵢ|ⱼ < 1

pf of claim
induction on |I|
case |I| = 0, 沒事可做
case |I| = 1, 因為 |.|ᵢ is nontri, ∃ a, |a|ᵢ > 1 就夠了
case |I| = 2, 這剛好就是上面 lemma 2 的內容
case |I| ≥ 3, assume for any finite set J with |J| < |I|, the statement holds,
任給 i ∈ I, 取一個 k ∈ I-{i}, then |I-{k}| < |I|, 根據歸納法假設
我們能找到
  ∃ a, |a|ᵢ > 1 and ∀ j ∉ {i, k}, |a|ⱼ < 1  and |a|ₖ = ?
根據 lemma 2, 因為 |.|ᵢ, |.|ₖ 不等價 我們又有
  ∃ b, |b|ᵢ > 1 and ∀ j ∉ {i, k}, |b|ⱼ = ?  and |b|ₖ < 1
這裡我們對 |a|ₖ 的大小分情況討論

如果 |a|ₖ ≤ 1 那 {aⁿb}ₙ 就能在
|.|ᵢ 下保持 > 1
|.|ⱼ 下收斂到 0 for j ∉ {i, k}
|.|ₖ 下保持 < 1
由於 I 的有限性, 可以同時夠大的 n 使得同時 |aⁿb|ⱼ < 1 for j ∉ {i, k}

如果 |a|ₖ > 1, 比較 tricky 的考慮 {1/(1+a⁻ⁿ) * b}ₙ 這個數列
注意到 if |a| > 1 then 1/(1+a⁻ⁿ) → 1 as n → ∞ in |.|
      if |a| < 1 then 1/(1+a⁻ⁿ) → 0 as n → ∞ in |.|
（為什麼是 1/(1+a⁻ⁿ) 這個數列 下面remark會稍微給一點動機）
所以 {1/(1+a⁻ⁿ) * b}ₙ 這個數列的絕對值在
|.|ᵢ 下收斂到 1 * |b|ᵢ > 1
|.|ⱼ 下收斂到 0 for j ∉ {i, k}
|.|ₖ 下收斂到 1 * |b|ₖ < 1
由於 I 的有限性, 可以同時夠大的 n 使得同時 1/(1+a⁻ⁿ) * b 滿足 claim 的敘述

有了 claim 後 對於 r > 0, {zᵢ}_(i ∈ I) ⊆ K,
因為 1/(1+aᵢ⁻ⁿ) → δᵢⱼ as n → ∞ in |.|ⱼ (where δᵢⱼ = if i = j then 1 else 0) 所以
∑ i ∈ I, zᵢ * 1/(1+aᵢ⁻ⁿ) → zⱼ as n → ∞ in |.|ⱼ
只要挑 n 夠大 ∑ i ∈ I, zᵢ * 1/(1+aᵢ⁻ⁿ) 就會滿足 weak apporm will holds. qed

-/

/-
remark
這個數列 1/(1+a⁻ⁿ) 是怎麼來的？
我們知道如果兩個數列的絕對值趨近到 0 或 ∞
他們相乘也會趨近到 0 或 ∞
但如果一個趨近 0 一個趨近 ∞ 相乘起來的結果就不確定了
相同的加法也有類似的現象
只是就變成 兩個數列的絕對值趨近於 ∞ 時 相加反而會失去控制
而要是有一個數列趨近 0 相加的結果就被另一個數列控制
最後是 (.)⁻¹ 也是一樣
我們可以整理成一個形式上的加法乘法表

* | 0  ∞
--------
0 | 0  ?
∞ | ?  ∞

+ | 0  ∞
--------
0 | 0  ∞
∞ | ∞  ?

⁻¹| 0 ∞
--------
  | ∞ 0

稍微玩一玩這個表格 就會發現如調和平均 1/(1/a+1/b) 或是 1/(1+a⁻¹) 有蠻不錯的性質


1/(1/a+1/b)
  | 0  ∞
--------
0 | ?  0
∞ | 0  ∞

1/(1+a⁻¹)
  | 0 ∞
--------
  | 0 1


weak approx 的證明到這裡結束
以下是我分享我在讀證明時的心得
除了參考書本外 其實我大部分的證明是看 lean 證明助手裡面的實作
lean 是一個程式輔助證明系統 能幫你檢查寫出來的證明是否正確
相應的裡面要求每一步用到哪個 lemma 都要寫非常清楚
用 lean 看證明的感覺和看書證明的感覺真的好不一樣
證明長度比書本的版本多上好幾倍
有一些小觀察
1. 很多步驟要檢查 |x| ≠ 0 的條件 其實書本證明（連同我的這份證明也是）蠻多沒寫出來
2. lean 裡面的絕對值定義其實也訂得更廣
let R, S be a semiring, S equiv a partia order
if |.| : R → S satisfy ... (絕對值的公理) then |.| is a absolue value on R to S
在後續的性質證明才陸續家條件
S 是
LinearOrder
IsStrictOrderedRing (ring運算和order相容)
Archimedean (∀ x y ∈ S, 0 < y → ∃ n : ℕ, x ≤ n * y)
TopologicalSpace
OrderTopology (而且 S 上的拓樸是由 (∞, a), (a, ∞) 生成的
3. lean 裡面花了不少心力去維護一個叫做 WithAbs 的東西
主要想法是
let (K, |.|ᵢ) denote the same field of K but equiv with |.|ᵢ induced topo for i = 1,2
define
  id₁ : (K, |.|₁) → K, x ↦ x
  id₁,₂ : (K, |.|₁) → (K, |.|₂), x ↦ x
與其說 x ∈ K, 因為 |.|₁, |.|₂ 誘導同一個拓樸在 K 上 所以
  xⁿ → 0 as n → ∞ in |.|₁
→ xⁿ → 0 as n → ∞ in |.|₂
lean會偏好說 x ∈ (K, |.|₁), 因為 id₁,₂ 是 Homeomorph 所以
  xⁿ → 0 as n → ∞
→ id₁,₂(x)ⁿ → 0 as n → ∞
透過 x 和 id₁,₂(x) 各自在空間就自動推導這個收斂是在哪個拓樸下收斂
透過 id₁, id₁,₂ 這些映射
lean才能更好現在到底在講哪個絕對值誘導的拓樸
以範疇論的視角說 id₁ 就有點像 forgetful functor
而 id₁,₂ 則像是 (not) amnestic functor 的概念


參考文獻：

Jiirgen Neukircht
Translator:
Norbert Schappacher
U.F.R. de Mathematique et d'Informatique
Universite Louis Pasteur
7, rue Rene Descartes
F-67084 Strasbourg, France
e-mail: schappa@math.u-strasbg.fr
The original German edition was published in 1992 under the title
Algebraische Zahlentheorie
ISBN 3-540-54273-6 Springer-Verlag Berlin Heidelberg New York
Library of Congress Cataloging-in-Publication Data
Neukirch, lurgen, 1937-. [Algebraische zahlentheorie. English] Algebraic number
theory 1 Jiirgen Neukirch; translated from the German by Norbert Schappacher.
p. cm. - (Grundlehren der mathematischen Wissenschaften; 322
Includes bibliographical references and index.
ISBN 978-3-642-08473-7 ISBN 978-3-662-03983-0 (eBook)
DOI 10.1007/978-3-662-03983-0
1. Algebraic number theory. 1. Title II. Series.
QA247.N51713 1999 512'.74-dc21 99-21030 CIP
Mathematics Subject Classification (1991): u-XX, 14-XX
ISSN 0072-7830
ISBN 978-3-642-08473-7
This work is subject to copyright. All rights are reserved, whether the whole or part
of the material is concerned, specifically the rights of translation, reprinting, reuse of
illustrations, recitation, broadcasting, reproduction on microfIlm or in any other
way, and storage in data banks. Duplication of this publication or parts thereof is
permitted only under the provisions of the German Copyright Law of September 9,
1965, in its current version, and permission for use must always be obtained from
Springer-Verlag Berlin Heidelberg GmbH.
Violations are liable for prosecution under the German Copyright Law.
© Springer-Verlag Berlin Heidelberg 1999
Originally published by Springer-Verlag Berlin Heidelberg New York in 1999
Softcover reprint of the hardcover 1st edition 1999
Cover design: MetaDesign plus GmbH, Berlin
Photocomposed from the translator's LATEX files after editing and reformatting by
Raymond Seroul, Strasbourg
SPIN: 10994771 41/3111- 543 2 Printed on acid-free paper



https://github.com/smmercuri/mathlib4/blob/4e0ee3a83cb68f70cca116898ab4380e29cfe210/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean
-/




/-


# may be can remove this part?
basic property

1. |1| = 1, |-1| = 1, |x⁻¹| = |x|⁻¹ for x ≠ 0
|1| = |1 * 1| = |1||1| and |1| ≠ 0 → |1| = 1
|-1||-1| = |-1 * -1| = |1| = 1 and |-1| ≥ 0 → |-1| = 1
|x||x⁻¹| = |xx⁻¹| = |1| = 1 and |x| ≠ 0 → |x⁻¹| = |x|⁻¹

2. d(x, y) = |x - y| define a metric on K and so induce a topo on K

d(x, x) = 0
d(x, y) = |x - y| = |-1||x - y| = 1 * |x - y| = d(y, x)
d(x, z) = |x - z| ≤ |x - y| + |y - z| = d(x, y) + d(y, z)

3. (K, |.|) is topo field (i.e. +, *, - are conti and ⁻¹ are conti at a ∈ Kˣ)

|.| : K → ℝ conti
  ||x| - |a|| ≤ |x - a|
(. + .) : K × K → K conti
  |x + y - (a + b)| ≤ |x - a| + |y - b|
(. * .) : K × K → K conti
  |xy - ab| = |(x-a+a)(y-b+b) - ab| ≤ |x-a||y-b| + |x-a||b| + |a||y-b|
(- .) : K → K conti
  (- x) = (-1 * x)
(. ⁻¹) conti at a ∈ Kˣ
  fix 0 < r < |a|
  for x near a, r < |x|
  |1/x - 1/a| = |x-a|/|x||a| ≤ |x-a|/r|a|

-/
