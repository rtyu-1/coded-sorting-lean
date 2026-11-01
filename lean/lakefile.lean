import Lake
open Lake DSL

package codedSorting where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib CodedSorting where
  -- Concrete frame proofs need the same 32 MiB thread stack as the local builder.
  -- Keep this in Lake so ordinary builds and CI use the same kernel resources.
  moreLeanArgs := #["-s", "32768"]
