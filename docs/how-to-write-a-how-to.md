# How to write a how-to

A *phrasebook entry* answers a single question of the form
"How do I say X using Mathlib?". It is a reference for working users,
not a textbook.

## Audience

The reader already knows the mathematics and some Lean. They want the
idiomatic Mathlib pattern for one specific thing, and they will not
read paragraphs to get to it.

## Length and structure

Each entry should be at most two or three printed pages. If a topic
is longer, split it: write a slim landing page (intro plus a reference
table or two) and use Verso's `{include 1 Phrasebook.X.Y}` to nest
focused child entries underneath. `Phrasebook/Filters/` is the worked
example of this pattern. Tag each child with `%%% tag := "..." %%%`
right under its heading so siblings can cross-link.

## Title format

Chapter titles take the form `"How to write X using Mathlib"` or
`"How to work with X in Mathlib"`. Stay consistent with the existing
chapters.

## House style

The reference is `Phrasebook/LinearAlgebra.lean` (Anne Baanen). Match
it:

- Front-load the shape (the type, the goal, the lemma signature)
  before any prose explanation.
- Use annotated examples. Put `-- New goal: ...` comments inside
  example blocks at the points where the next step is not obvious.
- For variant syntaxes of a single tactic or lemma, use a bullet list
  with verbatim syntax on the left and a one-line description on the
  right.
- Use `+error` blocks to show what a common mistake actually looks
  like in Lean, then give the one-line fix. See the `negError` example
  in `Phrasebook/LinearAlgebra.lean`.
- One sentence per idea. No flourishes.

## Writing pitfalls

Concrete things that have tripped people up:

- Don't drop notation cold. If you write `s ∈ l`, the reader should
  already know `l : Filter α` and `s : Set α`.
- Avoid the pattern `` `code` ({name}`X`)``. The parenthesised name
  reads as part of the term expression. Put the Mathlib name as the
  subject of a sentence instead: `The {name}`X` relation, written
  `code`, means ...`.
- Don't reuse type variables (`α`, `β`) as math placeholders. If `α`
  is "any type" elsewhere in the file, the reader will not read it as
  a point in `lim x → α`.
- Be specific in example comments. Write `-- u : ℕ → ℝ converges to x
  as n → ∞`, not `-- u converges to x`.
- A "Variants" list should not repeat the canonical example you just
  showed. List actual variants.
- When you cite a dual or paired concept, define it directly. Saying
  "the dual is X" without saying what X means is a non-answer.
- Pick one terminology for each concept and use it everywhere. Don't
  drift between "deleted limit", "classical deleted limit", and
  "deleted-neighbourhood limit".

## Verso mechanics

Verso is not Markdown. The conventions that catch people:

- Bold is `*x*`, single asterisk. The linter rejects `**x**`.
- Italics is `_x_`.
- Tables are a directive: `::: table +header` followed by a nested
  `*` list (each outer item is a row, each inner item is a cell),
  then `:::`. Markdown `| ... |` pipes render as literal text. See
  `Phrasebook/Filters.lean` for examples.
- Code blocks that should elaborate are inside
  `::: leanSection ... :::`. Use ```` ```lean ```` (or
  ```` ```lean -show ```` for setup that should not render).
- Show an expected error with
  ```` ```lean +error (name := foo) ````
  followed by ```` ```leanOutput foo ```` containing the verbatim
  error text. The linter rejects any drift from the actual message.

## Cross-references

- Tag a section with a metadata block right under the heading:
  `%%%\ntag := "filters-tendsto"\n%%%`.
- Link to a tagged section with
  `{ref "filters-tendsto"}[Limit statements]`.
- A sibling reference should always be a hyperlink, never plain text.
- `{name}`Foo.bar`` produces an in-document link to the Mathlib
  identifier with hover info. It does not produce an external
  `leanprover-community.github.io` URL; that is a Verso limitation.

## The quarantine principle

Some material is for translation only, not for use. Examples: ε-δ
statements (the user translates them from textbooks into filter form
once, then stays in filter form forever after).

When a page exists to translate from a non-native style, name the
principle explicitly: tell the reader to stay in the native style and
to reach for the translation page only when bringing in classical
input. Don't link a translation page from a "Proving X" recipes page
as if it were another proof technique.
