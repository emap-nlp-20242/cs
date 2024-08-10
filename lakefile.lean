import Lake
open Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.10.0"

package «cs» where
  -- add package configuration options here

lean_lib «CS» where
  -- add library configuration options here

lean_lib «IR» where
  -- add library configuration options here

@[default_target]
lean_exe «cs» where
  root := `Main
