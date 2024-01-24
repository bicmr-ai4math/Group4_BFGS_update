import Lake
open Lake DSL

package «Group-4-P-1» where
  -- add package configuration options here

@[default_target]
lean_lib «Group4P1» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
