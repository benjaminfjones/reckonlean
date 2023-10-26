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
