# Writing your first phrasebook entry

This guide takes you from a question that came up in a Lean project to a
rendered phrasebook entry. By the end, you should have a small page that
answers that question with checked Lean examples and is ready for review.

The project [README](../README.md) explains what belongs in the phrasebook.
The short version is: write for a reader who knows the mathematics and some
Lean, is in the middle of a project, and wants to know how to express or use
one mathematical idea in Mathlib.

## 1. Start with the reader's question

Good entries usually begin with a problem you actually encountered. Write the
question down in mathematical language before looking at Mathlib's names. For
example, "How do I state that a sequence converges?" is a better starting
point than "How does `Filter.Tendsto` work?"

Before writing, search the existing phrasebook and
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).
A phrasebook entry may link to existing introductory material
and start where it stops.

When preparing a phrasebook entry, you should have in mind
* the type of problem the reader is working on
* the background knowledge they already have or don't have
* what they are trying to achieve
* what new skills they will have after reading the entry.

Begin by turning this into a short outline. Typically a phrasebook entry will have a few sections that can be
consulted independently. Name each section after the task it solves, using
words a mathematician would search for. For example, prefer "State that a sequence
converges" to "The `Tendsto` definition". Page titles can simply name the
mathematical topic, as the existing chapters do.

If the entry translates a familiar but non-idiomatic formulation into the
usual Mathlib formulation, say that in the introduction. Show the translation,
then tell the reader which formulation to use in subsequent work.

## 2. Make a compiling skeleton

Copy the repository's starter file and give the copy a module name for your
topic:

```bash
cp Phrasebook/Template.lean Phrasebook/YourTopic.lean
```

In the new file, replace the copyright holder, author, title, tag, scope
statement, and first section. The scope statement should say what the page
helps the reader do and what it assumes. Leave later ideas out for now: the
first useful section is enough to establish the shape of the entry.

Register the page in `Phrasebook.lean` in two places:

1. Add `import Phrasebook.YourTopic` with the other page imports.
2. Add `{include 1 Phrasebook.YourTopic}` where the page should appear in the
   book.

Check the skeleton immediately:

```bash
lake build Phrasebook.YourTopic
lake exe phrasebook
```

On a new checkout, run `lake exe cache get` first. To view the result, run:

```bash
python3 -m http.server 8000 -d _out/html-multi
```

and open <http://localhost:8000>. Confirm that the new page appears in the
table of contents before writing more.

## 3. Finish one useful section

Start the section with the Lean form the reader came to find. Introduce its
required variables, imports, namespaces, and notation before the example, then
explain only what the reader needs to adapt it.

A first section will often have this shape:

````text
# State the first kind of X
%%%
tag := "your-topic-first-kind"
%%%

To state ..., write:

::: leanSection
```lean -show
-- Put boilerplate needed by the visible example here.
```
```lean
-- Put a small, usable example here.
```
:::

The important arguments are ...
````

The example should compile in the context established immediately above it.
A reader copying examples in order should not discover a missing `open`,
variable, typeclass assumption, or hypothesis.

As you write:

- Put the usable pattern before background about why Mathlib is designed that
  way. Link to longer explanations instead of delaying the answer.
- Use one notation and one term for each object throughout the entry.
- Put `-- New goal: ...` comments inside a proof when the next step is not
  obvious. Make comments precise enough to stand on their own.
- Use a small expected-error example when seeing the actual error helps the
  reader recognize and fix a common mistake.
- Give the editor abbreviation for unusual Unicode used in code, such as
  `⧸` (`\/`), `⊓` (`\inf`), `𝓝` (`\nhds`), or `≃ₐ` (`\~-\_a`).
- Say whether descriptions of Mathlib's coverage are true now or are future
  work.

Render again after this first section. Check the code width, prose flow,
identifier links, and any error output before repeating the pattern for the
remaining sections.

## 4. Complete the entry as a collection of answers

Add the remaining sections from your outline. Each section should make sense
to a reader who arrived there from search or the table of contents. State any
prerequisites it needs and avoid relying on a long narrative from earlier
sections.

When several names or notations need a compact lookup, add a reference table
after the examples as a summary. Do not make the reader decode the table
before seeing how the main patterns are used.

If the entry becomes too large to navigate easily, split it into focused child
pages. The parent should briefly introduce the topic, link the children, and
optionally summarize them in a table. Import each child from the parent file
and include it with `{include 1 Phrasebook.YourTopic.Child}`; only the parent
needs to be registered in `Phrasebook.lean`.

Before polishing sentences, read only the title, introduction, and headings.
They should tell a coherent story about what the reader can now do. Then check
each section separately: its first example should answer the task named in its
heading.

Useful models in the repository are:

- `Phrasebook/LinearAlgebra.lean` for checked examples, expected errors, and
  concise explanations.
- `Phrasebook/Filters/Tendsto.lean` for task-oriented sections.
- `Phrasebook/Filters.lean` for a parent page that links focused child pages.

## 5. Check the rendered entry before opening a PR

- `lake build Phrasebook.YourTopic` succeeds without unexpected errors.
- `lake exe phrasebook` succeeds.
- The page appears in the table of contents at the intended location.
- Every section's heading states a reader task or recognizable mathematical
  topic.
- Examples compile with only the setup shown earlier in their section.
- Long code lines do not require horizontal scrolling.
- Every sibling reference works, and every `{name}` reference links to a
  declaration and shows useful hover information.
- The rendered output contains no raw table syntax, broken code blocks, or
  stale expected-error text.
- Placeholders, `TODO`/`XXX` markers, duplicated setup, and copy-paste
  leftovers are gone.

## Verso quick reference

Verso is not Markdown. These are the pieces most entries need.

### Checked code and hidden setup

Put related code in a `leanSection`. A `-show` block is elaborated but hidden
in the rendered page, so use it for boilerplate only:

````text
::: leanSection
```lean -show
open Filter Topology
```
```lean
example (x : ℕ) : x + 0 = x := Nat.add_zero x
```
:::
````

### Identifiers and mathematical expressions

- Write a declaration as `` {name}`Foo.bar` ``. It links to the declaration
  and shows its type on hover.
- Write an expression Lean should elaborate as `` {lean}`f x` ``.
- Write a mathematical variable in prose with inline math, `` $`x` ``.
- Use plain backticks only for text that is not a Lean identifier or
  expression.

### Tags and links

Give every page and every section that may be linked a stable tag directly
under its heading:

```text
%%%
tag := "your-topic-first-kind"
%%%
```

Link to it with `{ref "your-topic-first-kind"}[the first kind of X]`.

### Tables

Use a Verso table, not Markdown pipes:

```text
::: table +header

* * Form
  * Meaning

* * `first`
  * the first form

* * `second`
  * the second form

:::
```

### Expected errors

Use a named `+error` block and a matching `leanOutput` block. Copy the error
text from the build output; the linter rejects stale output.

````text
```lean +error (name := exampleError)
-- Code that should fail.
```
```leanOutput exampleError
-- Exact error text.
```
````

For prose, bold is `*bold*` and italics is `_italic_`; Markdown's `**bold**`
is rejected by the linter.
