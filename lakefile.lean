import Lake
open Lake DSL

package «formalization_of_my_university_mathematics» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FormalizationOfMyUniversityMathematics» where
  -- add any library configuration options here
