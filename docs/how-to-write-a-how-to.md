# How to write a how-to

The Mathlib phrasebook is the *how-to* quadrant of
[Mathlib's documentation](https://leanprover-community.github.io/documentation.html),
in the sense of the [Diátaxis](https://diataxis.fr/) four-quadrant
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

## Organize by the task, not by Mathlib internals

Start from the mathematical object the entry is about and show how to
write it in Mathlib. Don't structure the entry as a list of Mathlib
definitions.

- Name sections for tasks, not types. Prefer "Write limits using
  `Tendsto`" over "`Tendsto`: the universal limit". The heading should
  name the problem the section solves.
- Show the usable pattern first; put theory later. Cut background that
  doesn't change what the reader types. A definition being unifying or
  elegant is worth a mention after the examples, not before them.
- Use the words a mathematician would search for: "on a neighbourhood",
  "for sufficiently large `n`", "almost everywhere", not the internal
  Mathlib names.
- Reference tables are indexed by Mathlib name, so put them at the end
  of a chapter as a summary, not before the examples.
- Order examples so each one compiles using only earlier setup. If an
  example needs an `open` or a hypothesis, introduce it first, so
  someone trying the examples in order doesn't hit an error.

## Title format

Chapter titles take the form `"How to write X using Mathlib"` or
`"How to work with X in Mathlib"`. Use the same form as the existing
chapters. A phrasebook page is a how-to, not a tutorial or a reference:
don't title it `"Tutorial: ..."`, and don't write it as one.

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
- Write Mathlib identifiers as Verso roles, not plain backticks, so
  the rendered page links to the declaration and shows its type on
  hover. Use `` {name}`Foo.bar` `` for a declaration name; it hides
  implicit arguments, so don't write `` {name}`@Foo` ``. Use
  `` {lean}`expr` `` for an expression Lean should elaborate in
  context, for example to show implicit arguments being filled in.
  Plain backticks are for text that isn't a Lean identifier.
- Put anything that should hover in Verso prose, not a Lean comment.
  A `-- Set G` comment is plain text; writing `` {name}`Set` `` in a
  sentence gives the same information with a link and a type.
- Use one notation per object, throughout the entry. Don't use `𝕜`
  for the base field and `k` for a smoothness exponent in the same
  file, and don't write the same object two ways (`ω` here, `⊤`
  there). Use Mathlib's conventional notation (`𝕜` for a base field,
  not `k`).
- Write mathematical variables in prose with Verso inline math,
  `` $`n` ``. Don't mix bare backticks and inline math for variables.
- Write "Mathlib" with a capital M.

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
- *Show what Mathlib does well.* Prefer examples that are short and
  idiomatic. When something is missing or still awkward to use, say so
  and link the in-progress work (an open PR, a project repository, 
  an arXiv paper); don't spend the entry cataloguing what's missing.
- *Document non-keyboard unicode.* When a snippet uses a character
  the reader cannot easily type (`⧸`, `⊓`, `𝓝`, `≃ₐ`), give the
  abbreviation (`\/`, `\inf`, `\nhds`, `\~-\_a`).
- *Reuse `variable` declarations within a `leanSection`.* Declare
  the running context once and let later examples in the same
  section use it.
- *End with exercises* when the topic invites follow-up work.

## Writing pitfalls

Concrete things to get right:

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
- Say whether a claim is true in Mathlib now or is future work. "You
  should expect good coverage" states a current fact; if it's a goal,
  say so.
- If a list of recipes or variants isn't complete, say so and link the
  full set. Get the count right: don't write "three recipes" above a
  list of five.

## Verso mechanics

Verso is not Markdown. The conventions to know:

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

   The `-show` flag hides setup code from the rendered output. Hide
   only boilerplate (`open`s, `variable` blocks, imports). If a line
   matters to the example, show it.

- Keep code lines short. A line wider than the page gives the rendered
  code block a horizontal scroll bar that hides its end. Wrap long
  signatures and `variable` blocks across several lines.

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

- Tag every page, and every section you might link to. A tag is cheap and
  makes the heading a stable link target; an untagged section cannot be
  referenced later without editing it first. When in doubt, add the tag.
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
- Remove leftovers from editing: `TODO`/`XXX` markers, stray characters
  (an unmatched `}` at the end of a comment), and copy-paste mistakes.
  Duplicated `variable` blocks and mismatched `leanOutput` names are the
  common ones. Check that each example still matches the prose around it.
