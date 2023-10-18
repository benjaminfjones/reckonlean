import Lake
open Lake DSL

package «reckoning-lean» {
  -- add package configuration options here
}

lean_lib «ReckoningLean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «reckoning-lean» {
  root := `Main
}
