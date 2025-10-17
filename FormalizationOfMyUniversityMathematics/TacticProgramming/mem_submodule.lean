import Mathlib.Algebra.Module.Submodule.Defs

-- some examples when you need to show
-- `v + w ∈ V`, `c • v ∈ V`, `0 ∈ V` for `V : Submodule R M, v w : M, c : R`

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v w : M) (hv : v ∈ V) (hw : w ∈ V) :
  v + w ∈ V := by
  apply V.add_mem hv hw

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v : M) (c : R) (hv : v ∈ V) :
  c • v ∈ V := by
  apply V.smul_mem c hv

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) :
  (0 : M) ∈ V := by
  apply V.zero_mem

-- more complex example

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v w : M) (c d : R) (hv : v ∈ V) (hw : w ∈ V) :
  c • v + d • w ∈ V := by
  apply V.add_mem
  · apply V.smul_mem c hv
  · apply V.smul_mem d hw

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v w : M) (c d : R) (hv : v ∈ V) (hw : w ∈ V) :
  (c • (d • (v + w))) ∈ V := by
  apply V.smul_mem c
  apply V.smul_mem d
  apply V.add_mem hv hw

-- write a tactic `mem_submodule` that can solve all the above goals

macro "mem_submodule" : tactic => `(tactic|
    repeat (first
    | apply Submodule.add_mem
    | apply Submodule.zero_mem
    | apply Submodule.smul_mem
    -- can easily add these too
    -- | apply Submodule.neg_mem
    -- | apply Submodule.sub_mem
    -- | apply nsmul_mem
    -- | apply zsmul_mem
    | assumption)
  )

example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v w : M) (c d : R) (hv : v ∈ V) (hw : w ∈ V) :
  c • v + d • w ∈ V := by
  mem_submodule
  -- show_term mem_submodule
  -- Try this: exact Submodule.add_mem V (Submodule.smul_mem V c hv) (Submodule.smul_mem V d hw)



example {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
  (V : Submodule R M) (v w : M) (c d : R) (hv : v ∈ V) (hw : w ∈ V) :
  (c • (d • (v + w))) ∈ V := by
  mem_submodule
  -- show_term mem_submodule
  -- Try this: exact Submodule.smul_mem V c (Submodule.smul_mem V d (Submodule.add_mem V hv hw))

-- oh, that is easy
-- how to prove that `mem_submodule` works for all goals of this form?
