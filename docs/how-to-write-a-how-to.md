# Writing your first phrasebook entry

If you have worked out how to use a part of Mathlib, a phrasebook entry is
an opportunity to share that experience. This guide discusses choosing a
question to answer, writing examples, and adding your contribution to the
book. An entry may occupy one page or several pages in the generated website.

The project [README](../README.md) explains what belongs in the phrasebook.
The short version is: write for a reader who knows the mathematics and some
Lean, is in the middle of a project, and wants to know how to express or use
one mathematical idea in Mathlib.

## Choose a question

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

An entry about convergence might have sections on stating convergence,
proving convergence, and using it in a proof. Such headings help a reader
find the part they need without knowing the names of Mathlib's definitions.
A heading such as "The `Tendsto` definition" is less helpful to someone
who has not yet learnt how Mathlib expresses convergence.

A section can have prerequisites: for example, composing linear maps
requires knowing how to declare vector spaces and linear maps. A link to
the section that explains those declarations lets a reader find the
necessary background without reading the whole entry in order.

## Write examples the reader can adapt

For the question "How do I state that a sequence converges?", an example
could be the following, in a file that imports `Mathlib`:

```lean
open Filter Topology

variable (u : ℕ → ℝ) (a : ℝ)
  (hu : Tendsto u atTop (𝓝 a))
```

Here `hu` is the assumption that the real sequence `u` converges to `a`.
The accompanying text should explain the notation: `atTop` specifies that
the index tends to infinity, and `𝓝 a` is the neighbourhood filter of `a`.
It can also say how to type `𝓝` in the editor: `\nhds` followed by a space.
The reader can then substitute their own sequence and limit. The `open`
commands are shown because they are needed to use these names and notation.

What the reader needs to know depends on the question. An entry on ring
extensions might introduce a single algebra first, and the compatibility
assumptions for a tower in a later section. Introduce each convention where
it is used. Explanations of why Mathlib chose a particular definition belong
in separate documentation, which the entry can link to.

When a mistake is likely to puzzle the reader, an example showing the error
and its correction can help. For instance, the
[linear algebra entry](../Phrasebook/LinearAlgebra.lean) shows why an
`AddCommMonoid` assumption does not suffice to negate a vector, and gives
the assumption needed to do so. The [output examples below](#expected-errors)
explain how to include Lean's messages in the text.

It is also helpful to mention missing theorems or known difficulties that
affect the reader's project. Describe what is available and what remains to
be done; if there is work in progress, link to it. This can help someone
decide whether to use the current library or contribute the missing result.

When reading over your draft, consider someone arriving at a section with
the question in its heading. Can they find the relevant example, understand
its assumptions, and use it in their own file? This is also a useful question
to ask a reviewer when you open a pull request.

## Create the file and view it in a browser

Copy the repository's starter file and give the copy a module name for your
topic:

```bash
cp Phrasebook/Template.lean Phrasebook/YourTopic.lean
```

In the copy, fill in your name in the copyright and author lines. Choose a
title and tags for your topic, then replace the introduction and first
section with your text. The introduction tells the reader what questions
the entry answers and what background it assumes. Tags are names used in
links; their syntax is described [below](#tags-and-links).

Register the page in `Phrasebook.lean` in two places:

1. Add `import Phrasebook.YourTopic` with the other imports.
2. Add `{include 1 Phrasebook.YourTopic}` where the page should appear in the
   book.

On a new checkout, first download the compiled dependencies:

```bash
lake exe cache get
```

Then check that your file compiles and generate the HTML:

```bash
lake build Phrasebook.YourTopic
lake exe phrasebook
```

If either command reports errors, they need to be fixed before you can view
the updated page. The first command checks your file; the second builds the
complete phrasebook and writes the HTML to `_out/html-multi/`.

To view it, start a local web server:

```bash
python3 -m http.server 8000 -d _out/html-multi
```

and open <http://localhost:8000>. Your page should appear in the table of
contents. If it is missing, check that both the `import` and `{include ...}`
lines are present in `Phrasebook.lean`, then run `lake exe phrasebook` again
and refresh the browser.

As you edit, run `lake exe phrasebook` in another terminal and refresh the
browser to see your changes. This also recompiles files that have changed;
you can leave the web server running and do not need to fetch the cache
again. Viewing the page helps you see whether the code and prose are readable
together. Follow the links you have added to check that they lead where you
intended.

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
