/-
Copyright (c) 2026 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
-- Write a code block with ```savedLean ... ``` to save it to an external file.
open Verso.Genre.Manual.InlineLean

open Phrasebook

set_option linter.unusedTactic false
set_option pp.rawOnError true

#doc (Manual) "How to write tests" =>

This page is about the ways of writing unit tests. Tests are located under {module}`MathlibTest` and can be run with

```
lake test
```

A newly added file inside the test library {module}`MathlibTest` will automatically be found without the need to adjust any imports anywhere.

Tests should be accompanied with comments and potentially links or issue numbers which provide enough context to understand what is being tested.

```lean
/-! This test ensures `existsi` is working -/

example : ∃ x : Nat, x = x := by
  existsi 42
  rfl
```

# Capturing messages

Test file are expected to be silent. Therefore, the main tool for tests is `#guard_msgs`, which allows to ensure the output of Lean (inf form of info, warning, or error) matches a specified content:

```lean
/--
error: `grind` failed
case grind
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
-/
#guard_msgs in
example : False := by grind
```

To make tests more robust, there are parameters `(substring := true)` and `(whitespace := lax)` to match only a substring or ignore whitespace discrepancies.

```lean
/--
error: `grind` failed
-/
#guard_msgs (substring := true) in
example : False := by grind

/--
error: `grind` failed
case grind
-/
#guard_msgs (substring := true, whitespace := lax)  in
example : False := by grind
```

To make tests even more robust, this can be combined with `pp` options like

```lean
set_option pp.mvars.anonymous false
```

which replaces anonymous meta variables with `?_`. There are more options and parameters documented in the docstring of `#guard_msgs`.

* [Reference manual: `#guard_msgs`](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#hash-guard_msgs)

## Capture failures

In a tactic proof, {tactic}`fail_if_success` can be used to ensure a tactic is failing.

```lean
example : True := by
  fail_if_success rfl
  trivial

/--
error: The tactic provided to `fail_if_success` succeeded
  but was expected to fail: trivial
-/
#guard_msgs (whitespace := lax) in
example : True := by
  fail_if_success trivial
```

There is also {tactic}`success_if_fail_with_msg`, which does a similar thing by capturing a failure of a tactic block; and there is `#guard_panic` to capture a panic in a tactic. However, a panic should be avoided and might indicate that the tactic should be redesigned.

# Guarding

During a tactic proof, {tactic}`guard_hyp` and {tactic}`guard_target` can be used to check the local hypotheses and goal at a certain point in the proof.

```lean
example {n : ℕ} (h : n + n = 4) : n = 2 := by
  fail_if_success guard_hyp h : n * 2 = 4
  ring_nf at h
  guard_hyp h : n * 2 = 4
  guard_target = n = 2
  grind
```

These comparisons can all be done at different reducibility levels

```lean
example {n : ℕ} (h : n + n = 4) : n = 2 := by
  ring_nf at h
  guard_hyp h : n * 2 = 4
  fail_if_success guard_hyp h : n * (1 + 1) = 4
  guard_hyp h :~ n * (1 + 1) = 4
  fail_if_success guard_target =ₛ n = (1 + 1)
  guard_target = n = (1 + 1)
  grind
```

{docstring Lean.Parser.Tactic.guardHyp}

{docstring Lean.Parser.Tactic.guardTarget}

## Comparing expressions

Moreover, {tactic}`guard_expr` can be used to compare arbitrary expressions, independent of current goal and hypotheses.

```lean
example {n : ℕ} (h : n + n = 4) : n = 2 := by
  guard_expr 2 + 2 = 4
  grind
```

{docstring Lean.Parser.Tactic.guardExpr}

## Check tactic functionality

To test the functionality of tactics one can either write an `example` as done previously in this guide or use the command `#check_tactic` which applies a tactic sequence to a term.

There is also `#check_simp` which tries to simplify a term.

```lean
variable (a b : Nat)

#check_tactic
  (a + b) ^ 2 ~>
  a * b * 2 + a ^ 2 + b ^ 2 by ring

#check_simp a + 0 ~> a
```

## `#eval`, `#check` and `#print`

Another typical pattern is to use `#guard_msgs` in compbination with  commands like `#eval`, `#check`, or `#print`.

```lean
def answer (n: ℕ) := n * 7

/-- info: 42 -/
#guard_msgs in
#eval answer 6

/-- info: answer 6 : ℕ -/
#guard_msgs in
#check answer 6
```
