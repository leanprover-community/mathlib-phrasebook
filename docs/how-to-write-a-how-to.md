# How to write a how-to

The Mathlib phrasebook is the *how-to* quadrant of
[Mathlib's documentation](https://leanprover-community.github.io/documentation.html),
in the sense of the [Diátaxis](https://diataxis.fr/) (originally
[Divio](https://docs.divio.com/documentation-system/)) four-quadrant
framework: tutorials, how-to guides, reference, and explanation.
A phrasebook entry is a *problem-oriented* guide for someone who
already knows the mathematics and some Lean and wants to start
working on a topic in Mathlib.

A typical entry covers the first few steps of working with one Mathlib
area, in around one to five printed pages. If a topic is longer, split
it (see *Length and structure* below).

## Audience

The reader already knows the mathematics and some Lean. They will not
read paragraphs to get to the answer. Give them the idiomatic Mathlib
patterns directly.

## Title format

Chapter titles take the form `"How to write X using Mathlib"` or
`"How to work with X in Mathlib"`. Use the same form as the existing
chapters.

## Creating a new entry

1. Add a file `Phrasebook/X.lean`. The header should look like:

   ```lean
   import VersoManual
   import Phrasebook.Meta.Lean
   import Mathlib

   open Verso.Genre Manual
   open Verso.Genre.Manual.InlineLean
   open Phrasebook

   set_option pp.rawOnError true

   #doc (Manual) "How to write X using Mathlib" =>

   One-sentence scope statement.

   # First topic

   ...
   ```

2. Register the entry in `Phrasebook.lean`: add
   `import Phrasebook.X` to the imports and
   `{include 1 Phrasebook.X}` where you want the page to appear in
   the book.
3. Build and render:

   ```bash
   lake build Phrasebook
   lake exe phrasebook
   ```

4. Open `_out/html-multi/index.html` in a browser and confirm the
   entry appears in the table of contents.

## Length and structure

If a topic exceeds five printed pages, split it. Write a short parent
page (intro plus a reference table) and include focused child entries
via `{include 1 Phrasebook.X.Y}`.

A *reference table* is a compact lookup the reader can scan instead of
reading prose: each row maps one piece of notation or one concept to its
meaning. A parent page is then just a one-paragraph intro, such a table,
and the child includes:

```
#doc (Manual) "How to work with X in Mathlib" =>

One paragraph: what this chapter covers and who it is for.

::: table +header

* * Object
  * What it means

* * `foo`
  * the first thing

* * {name}`Bar.baz`
  * the second thing

:::

{include 1 Phrasebook.X.Y}
{include 1 Phrasebook.X.Z}
```

The table can open the chapter as an overview or close it as a summary,
whichever the reader will reach for.

To register a child: add `import Phrasebook.X.Y` to the **parent**
file (not to `Phrasebook.lean`) and put the `{include 1 ...}` line
where the child should render. Tag each child with
`%%% tag := "..." %%%` right under its heading so siblings can
cross-link.

## House style

The reference is `Phrasebook/LinearAlgebra.lean` (Anne Baanen). Match
it:

- Start with the type, goal, or lemma signature before any prose
  explanation.
- Use annotated examples. Put `-- New goal: ...` comments inside
  example blocks at the points where the next step is not obvious.
- For variant syntaxes of a single tactic or lemma, use a bullet list
  with verbatim syntax on the left and a one-line description on the
  right.
- Use `+error` blocks to show what a common mistake actually looks
  like in Lean, then give the one-line fix. See the `negError`
  example in `Phrasebook/LinearAlgebra.lean`.
- One sentence per idea. No flourishes.

## Patterns that work well in longer entries

Entries toward the upper end of the page budget often benefit from
these structural patterns. Kevin Buzzard's
`Phrasebook/EllipticCurve.lean` is a worked example of all of them:

- *Learning objectives upfront.* Open with a "By the end of this
  entry, you should be able to: ..." bullet list. The reader can
  decide immediately whether the entry covers what they need.
- *A single running example.* Pick one concrete object (a specific
  elliptic curve, group, polynomial) and refer back to it across
  sections instead of inventing fresh notation each time.
- *Goal-state annotations inside proofs.* Inline `-- ⊢ goal`
  comments at the steps where the goal matters.
- *Live demos with `#eval` and `#check`.* These show Lean acting as
  a computer algebra system or type-checker, not just a proof
  assistant.
- *Be honest about gaps.* If something is not yet formalized in
  Mathlib, say so and point at the in-progress work (an arXiv
  paper, an open PR, a project repository).
- *Document non-keyboard unicode.* When a snippet uses a character
  the reader cannot easily type (`⁄`, `⊓`, `𝓝`, `≃ₐ`), give the
  abbreviation (e.g. `\textf` for `⁄`).
- *Reuse `variable` declarations within a `leanSection`.* Declare
  the running context once and let later examples in the same
  section use it.
- *End with exercises* when the topic invites follow-up work.

## Writing pitfalls

Concrete things that have tripped people up:

- Introduce notation before use. If you write `s ∈ l`, the reader
  should already know `l : Filter α` and `s : Set α`.
- Avoid the pattern `` `code` ({name}`X`)``. The parenthesised name
  reads as part of the term expression. Put the Mathlib name as the
  subject of a sentence instead: `The {name}`X` relation, written
  `code`, means ...`.
- Don't reuse type variables (`α`, `β`) as math placeholders.
- Be specific in example comments. Write `-- u : ℕ → ℝ converges to
  x as n → ∞`, not `-- u converges to x`.
- A "Variants" list should not repeat the canonical example you just
  showed. List actual variants.
- When you cite a dual or paired concept, define it directly. Saying
  "the dual is X" without saying what X means is a non-answer.
- Use one term consistently for each concept. Do not switch between
  "deleted limit", "classical deleted limit", and
  "deleted-neighbourhood limit".

## Verso mechanics

Verso is not Markdown. The conventions that catch people:

- Bold is `*x*`, single asterisk. The linter rejects `**x**`.
- Italics is `_x_`.
- Tables are a directive, not Markdown pipes. A minimal table:

   ```
   ::: table +header

   * * Column 1
     * Column 2

   * * `cell` row 1
     * description

   * * `cell` row 2
     * description

   :::
   ```

   Markdown `| ... |` pipes render as literal text inside a paragraph.

- Code blocks that should elaborate go inside a `leanSection`:

   ```
   ::: leanSection
   ```lean -show
   open Filter Topology
   ```
   ```lean
   example (x : ℕ) : x + 0 = x := Nat.add_zero x
   ```
   :::
   ```

   The `-show` flag hides setup code from the rendered output.

- Show an expected error with `+error (name := foo)` and a matching
  `leanOutput foo` block:

   ```
   ::: leanSection
   ```lean +error (name := nhdsNotOpened)
   example : Filter ℝ := 𝓝 (0 : ℝ)
   ```
   ```leanOutput nhdsNotOpened
   Unknown identifier `𝓝`
   ```
   :::
   ```

   The linter rejects any drift from the actual error text, so copy
   it verbatim from the build output.

## Cross-references

- Tag a section with a metadata block right under the heading:

   ```
   # My section
   %%%
   tag := "my-section"
   %%%
   ```

- Link to a tagged section with `{ref "my-section"}[My section]`.
- A sibling reference should always be a hyperlink, never plain text.
- `{name}`Foo.bar`` produces an in-document link to the Mathlib
  identifier with hover info. It does not produce an external
  `leanprover-community.github.io` URL; that is a Verso limitation.
- After rendering, click every sibling reference and hover every
  `{name}` reference in the changed page to confirm they resolve.

## Pedagogical idioms vs Mathlib idioms

Some entries exist to translate a non-Mathlib idiom (for example, ε-δ
statements from textbooks) into the Mathlib idiom.

When you write such an entry, say so in the intro: tell the reader to
stay in the Mathlib idiom and reach for the translation entry only
when bringing in classical input. Do not link a translation entry
from a recipes entry as if it were another tool.

## Before opening a PR

- `lake build Phrasebook.X` succeeds with no `error` diagnostics.
- `lake exe phrasebook` succeeds and renders to `_out/html-multi/`.
- Open the rendered page in a browser. A clean source build does not
  catch Markdown-pipe tables, ambiguous parenthetical patterns,
  unrendered code blocks, or broken cross-references. Generic
  Markdown previewers do not behave like Verso.
