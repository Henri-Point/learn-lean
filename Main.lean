import LearnLean
import Mathlib
import Libsodium

def main : IO Unit := do
  let bytes ← randomByteArray 32
  IO.println s!"Got {bytes.size} random bytes"
  (← IO.getStdout).flush
