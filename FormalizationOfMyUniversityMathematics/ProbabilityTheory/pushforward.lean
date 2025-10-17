import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes

#check MeasureTheory.integral_map
#check MeasureTheory.integral_map_of_stronglyMeasurable

#check MeasureTheory.SimpleFunc.approxOn
#check PseudoEMetricSpace
#check OpensMeasurableSpace

set_option trace.Meta.synthInstance true
example : PseudoEMetricSpace ℝ := inferInstance
example : OpensMeasurableSpace ℝ := inferInstance
example : TopologicalSpace.SeparableSpace ℝ := inferInstance
example (s : Set ℝ) : TopologicalSpace.SeparableSpace (↑s) := inferInstance
example [MetricSpace α] [MeasurableSpace α] [BorelSpace α] :
  PseudoEMetricSpace α := inferInstance
example [MetricSpace α] [MeasurableSpace α] [BorelSpace α] :
  OpensMeasurableSpace α := inferInstance
example (s : Set ℝ) : TopologicalSpace.SeparableSpace (↑s) := inferInstance
set_option trace.Meta.synthInstance false


/-
看到一個很炫炮的 simple function 的構造
固定 {x₁, ..., xₙ} ⊆ ℝ, n ≥ 1
給一個 y ∈ ℝ
找到 {x₁, ..., xₙ} 中和 y 最接近的點 比如說 xᵢ
（如果兩個點與 y 距離相同 選index較小的那個）
y ↦ xᵢ 就定義一個 ℝ → ℝ 的 simple function
確實 range 大小只有 finite
而且每個值的 preimage 長得都像是區間的樣子 所以是可測集
（這是騙人的 可以用 induciton 説）

上面那個simple function 叫做 nearestPt {x₁, ..., xₙ} : ℝ → ℝ
接著考慮一個 measurable function f : Ω → ℝ
因為 ℝ 是 separable space, 有一個可數稠密的子集（就是 ℚ ）
把這個子集編號 {xₖ}_{k ∈ ℕ} 對於每個 n ∈ ℕ 定義
fₙ : Ω → ℝ, fₙ = nearestPt {x₁, ..., xₙ} ∘ f
確實 simple 複合 measurable 還是 simple
如此就找到一組 simple funciton {fₙ}_{n ∈ ℕ}
根據{xₖ}_{k ∈ ℕ}是稠密的性質 或許還能證明 fₙ → f pointwisely
參見: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/SimpleFuncDense.html#MeasureTheory.SimpleFunc.approxOn
-/

#check DiscreteMeasurableSpace
#check MeasurableSet.of_discrete
#check Measurable.of_discrete
#check StandardBorelSpace

set_option trace.Meta.synthInstance true
example : PolishSpace ℝ := inferInstance
example : StandardBorelSpace ℝ := inferInstance
example : PolishSpace ℕ := inferInstance
example : StandardBorelSpace ℕ := inferInstance
example : CompleteSpace ℕ := inferInstance
example {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]:
  PolishSpace E := inferInstance
example (n : ℕ) : PolishSpace (Fin n → ℝ) := inferInstance
-- example {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]:
--   SecondCountableTopology E := inferInstance
set_option trace.Meta.synthInstance false

#check StieltjesFunction

#check MeasureTheory.Measure.sum
#check ENNReal.tsum_le_tsum
#check ENNReal.summable


#check Measurable
#check AEMeasurable
#check MeasureTheory.StronglyMeasurable
#check MeasureTheory.AEStronglyMeasurable
