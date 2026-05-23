/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Lean

open Lean.Quote Verso.Doc.Elab

@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do pure #[← ``(Verso.Doc.Inline.code $(quote Lean.versionString))]
  | _, _ => throwError "Unexpected arguments"
