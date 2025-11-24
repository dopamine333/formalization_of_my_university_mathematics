import Lake
open Lake DSL

package «formalization_of_my_university_mathematics» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.24.0"

@[default_target]
lean_lib «FormalizationOfMyUniversityMathematics» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
