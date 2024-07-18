import Lake
open Lake DSL

package «cs» where
  -- add package configuration options here

lean_lib «Cs» where
  -- add library configuration options here

@[default_target]
lean_exe «cs» where
  root := `Main
