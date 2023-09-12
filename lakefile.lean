import Lake
open Lake DSL

package «flt-regular» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require modularforms from git
  "https://github.com/CBirkbeck/ModularForms_Lean4.git"

@[default_target]
lean_lib «FltRegular» {
  -- add any library configuration options here
}
