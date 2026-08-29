import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

package «formalism-lean» where
  restoreAllArtifacts := true

-- Bertrand Meyer's two formal specifications of the Naur / Goodenough-Gerhart
-- text-formatting problem: the 1985 IEEE Software paper and chapter 9 of the
-- 2022 Handbook of Requirements and Business Analysis. Specifications only;
-- there is no implementation of word wrap here, and none is wanted.
@[default_target]
lean_lib Meyer where
  globs := #[.andSubmodules `Meyer]

-- A third specification of the same problem, written to use what Lean already
-- has: words and lines as lists rather than as runs of characters.  Also
-- specification only.
@[default_target]
lean_lib Native where
  globs := #[.andSubmodules `Native]
