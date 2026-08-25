import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

package «formalism-lean» where
  restoreAllArtifacts := true

-- Meyer's formal specification of the Naur / Goodenough-Gerhart text-formatting
-- problem, transcribed from his 1985 IEEE Software paper. Specification only.
@[default_target]
lean_lib Meyer where
  globs := #[.submodules `Meyer]
