/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Phrasebook.Meta.Lean

-- When adding new pages, add them to the `import` statements here,
-- and to the `{include 1 ...}` lines below.
import Phrasebook.LinearAlgebra
import Phrasebook.EllipticCurve

open Verso.Genre Manual

open Phrasebook

#doc (Manual) "Mathlib Phrasebook" =>

%%%
authors := ["the Mathlib community"]
%%%

{index}[example]
The Mathlib phrasebook tells you the answer to questions of the form "How do I say ... using Mathlib?"

{include 1 Phrasebook.LinearAlgebra}

{include 1 Phrasebook.EllipticCurve}

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
