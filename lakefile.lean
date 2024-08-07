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

lean_exe «prime_test» {
  root := `PrimeTest
}

lean_exe «herbrand_test» {
  root := `HerbrandTest
}

require "leanprover-community" / "batteries"
