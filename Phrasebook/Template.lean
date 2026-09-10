/-
Copyright (c) 2026 Your Name Here. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name Here
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

-- Replace "Topic" with the mathematical topic of your contribution.
#doc (Manual) "Topic" =>

%%%
tag := "topic" -- Choose a tag that is not already used in the book.
%%%

Replace this paragraph with an introduction saying what questions the entry
answers and what mathematical and Lean background it assumes.

# The first task

%%%
tag := "topic-first-task" -- Choose a distinct tag for this section.
%%%

Replace "The first task" with a heading for your first section. In place of
this paragraph, give a Lean example answering the question in the heading
and explain how to use it.
