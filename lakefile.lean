import Lake
open Lake DSL

package «campi_operazionistici» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

-- Frozen library published as v1.0.1. Its modules are not edited.
@[default_target]
lean_lib «CampiOperazionistici» where
  -- add any library configuration options here

-- Translations in the quotient by the n-th power remainder. Imports the frozen library.
@[default_target]
lean_lib «Reencounters» where

-- General operationistic grasslands. Imports the frozen library.
@[default_target]
lean_lib «Grasslands» where
