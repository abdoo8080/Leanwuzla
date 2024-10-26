import Lake
open Lake DSL

require Qq from git "https://github.com/abdoo8080/quote4.git" @ "master"

package "leanwuzla" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Leanwuzla» where
  -- add library configuration options here

@[default_target]
lean_exe «leanwuzla» where
  root := `Main
  supportInterpreter := true
