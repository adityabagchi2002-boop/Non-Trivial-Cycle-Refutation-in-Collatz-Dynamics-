import Lake
open Lake DSL

package «collatz-cycle» where
  -- Settings for the package

lean_lib «CollatzCycles» where
  -- Ensure this matches the exact name of your main .lean file (without the .lean part)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"
