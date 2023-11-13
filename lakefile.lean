import Lake
open Lake DSL

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4"

package «tao4» {
  -- add package configuration options here
}

lean_lib «Tao4» {
  -- add library configuration options here
}

@[default_target]
lean_exe «tao4» {
  root := `Main
}
