import Lake
open Lake DSL

package «reckonlean» {
  -- add package configuration options here
}

lean_lib «ReckonLean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «reckonlean» {
  root := `Main
}

lean_exe «adder_test» {
  root := `AdderTest
}

lean_exe «ramsey_test» {
  root := `RamseyTest
}

require std from git "https://github.com/leanprover/std4" @ "main"
