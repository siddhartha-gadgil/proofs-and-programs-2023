import Lake
open Lake DSL

package pnP2023 {
  -- add package configuration options here
}

lean_lib PnP2023 {
  -- add library configuration options here
}

@[default_target]
lean_exe pnP2023 {
  root := `Main
}

lean_exe lab1

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require leanaide from git "https://github.com/siddhartha-gadgil/LeanAide.git" @ "mathlib4"

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "main"