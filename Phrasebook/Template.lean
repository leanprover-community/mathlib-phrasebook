/-
Copyright (c) 2026 Your Name Here. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name here
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
-- Write a code block with ```savedLean ... ``` to save it to an external file.
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "Tutorial: How to write X using Mathlib" =>

This page explains how to express X using the definitions in Mathlib.
We assume basic knowledge of both Lean and X.

Please complete me. You can use `Phrasebook/LinearAlgebra.lean` as a cheat sheet.
