import Lake
open Lake DSL System

package "learn-lean" where
  version := v!"0.1.0"

lean_lib LearnLean


target shim.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / "libsodium_shim.c"
  let leanInclude ← getLeanIncludeDir
  let cflagsOutput ← IO.Process.output {
    cmd := "pkg-config"
    args := #["--cflags", "libsodium"]
  }
  let cflags := cflagsOutput.stdout.trimAscii.toString.splitOn " " 
               |>.filter (· != "") 
               |>.toArray
  buildO oFile srcJob
    (#["-I", leanInclude.toString] ++ cflags ++ #["-fPIC"])

-- libsodium paths are system-specific. To find the correct values, run:
--   pkg-config --libs libsodium
-- and replace the paths below accordingly.
lean_lib Libsodium where
  moreLinkArgs := #["-L/opt/homebrew/Cellar/libsodium/1.0.22/lib", "-lsodium"]
  moreLinkObjs := #[shim.o]
  precompileModules := true

lean_exe «learn-lean» where
  root := `Main
  supportInterpreter := true
  moreLinkArgs := #["-L/opt/homebrew/Cellar/libsodium/1.0.22/lib", "-lsodium"]

require mathlib from git "https://github.com/leanprover-community/mathlib4"
