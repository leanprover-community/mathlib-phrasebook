/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Phrasebook.Meta.Lean
import Phrasebook.Meta.MathlibCommit
import Phrasebook.Meta.Now
import Phrasebook.Meta.VersionString

-- When adding new pages, add them to the `import` statements here,
-- and to the `{include 1 ...}` lines below.
import Phrasebook.AdditiveCombinatorics
import Phrasebook.LinearAlgebra
import Phrasebook.Polynomials
import Phrasebook.ErgodicMaps
-- You can use `Phrasebook.Template` as a starting point for your own entry.
-- import Phrasebook.Template

open Verso.Genre Manual

open Phrasebook

#doc (Manual) "Mathlib Phrasebook" =>

%%%
authors := ["the Mathlib community"]
%%%

{index}[example]
The Mathlib phrasebook tells you the answer to questions of the form "How do I say ... using Mathlib?"
When you have a Lean formalization project you are working on or just getting started with,
the phrasebook tells you the idiomatic way to translate from mathematics to Mathlib.

The phrasebook is aimed at readers who are familiar with the mathematical subject and who know some Lean.
We recommend first having finished [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) before using the phrasebook.
This textbook is an excellent resource for getting started and explains its contents at a gentler pace.
More learning resources are available [on the community-maintained learning resources page](https://leanprover-community.github.io/learn.html).

The phrasebook is best consulted with a question in your mind, of the form "How do I ...?".
To get an answer to your question, use the table of contents on the left of the page to navigate to the page corresponding to your topic.
Alternatively, if you want to get an impression of Mathlib's coverage of a particular subject, you can also read the corresponding chapter from top to bottom.

This document has been last updated at *{now}[]* using Lean *{versionString}[]* and Mathlib commit {mathlibCommit}[].

{include 1 Phrasebook.LinearAlgebra}

{include 1 Phrasebook.Polynomials}

{include 1 Phrasebook.AdditiveCombinatorics}

{include 1 Phrasebook.ErgodicMaps}

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
