import Lake
open Lake DSL

package «tagless» {
  -- add package configuration options here
}

lean_lib «Tagless» {
  -- add library configuration options here
}

@[default_target]
lean_exe «tagless» {
  root := `Main
}
