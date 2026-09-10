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
the assumption needed to do so. The [output examples below](#showing-leans-output)
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

The phrasebook uses Verso to check the Lean examples and generate the website.
In the template, the text after `#doc (Manual) "Topic" =>` is written in
Verso's markup. Headings, lists, and links have familiar Markdown syntax;
the examples below show how to include Lean code and mathematical notation.

### Lean code and variables

A block beginning with three backticks followed by `lean` contains code
that Verso checks when the file is compiled. Variables and opened namespaces
remain available to later code blocks and inline expressions. To limit
their scope, put `::: leanSection` before the text and `:::` after it,
as you would use `section` and `end` in a Lean file:

````text
::: leanSection
```lean
variable (n : ℕ)
```
```lean
#check n + 1
```
:::
````

Here `n` is available in both blocks, but its declaration does not affect
the text after `:::`.

Adding `-show` to a code block hides it in the website while still checking
it. This can supply a variable used only in prose, where its type is stated
in words:

````text
::: leanSection
```lean -show
variable (x : ℝ)
```
For a real number {lean}`x`, its absolute value is {lean}`|x|`.
:::
````

For a code example that the reader will copy, show the `variable` and `open`
commands it needs along with the example.

### Identifiers and mathematical expressions

- A reference such as `` {name}`Nat.add_zero` `` links to the declaration
  and shows its type on hover.
- An expression such as `` {lean}`n + 1` `` is checked by Lean, using the
  variables available at that point in the text.
- Inline mathematics is written in LaTeX, for example `` $`x` `` or
  `` $`\sum_{i=0}^n i` ``.
- Plain backticks display text verbatim, for example an editor input
  sequence such as `` `\nhds` ``.

### Emphasis

Write `*bold*` for bold text and `_italic_` for italic text.

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

Verso has its own syntax for tables. For example, a table comparing two
notations for linear maps can be written as:

```text
::: table +header

* * Form
  * Meaning

* * `M →ₗ[R] N`
  * an R-linear map from M to N

* * `M ≃ₗ[R] N`
  * an R-linear equivalence between M and N

:::
```

### Showing Lean's output

To display the result of a command such as `#check`, `#eval`, or `#synth`,
give the code block a name and use that name in a `leanOutput` block:

````text
```lean (name := sumOutput)
#eval (2 : ℕ) + 2
```
```leanOutput sumOutput
4
```
````

Copy the message Lean displays in the editor into the `leanOutput` block.
Verso checks that this text agrees with Lean's actual output. If it changes,
you will see an error at the block in the editor or when compiling the file.

To include code that produces an error, add `+error`:

````text
```lean +error (name := boolError)
#check (true : ℕ)
```
```leanOutput boolError
Type mismatch
  true
has type
  Bool
but is expected to have type
  ℕ
```
````

The `+error` option tells Verso that the failure is intentional, so the
surrounding document can still compile. An example like this would be
followed by the correction: here, a natural number such as `1` can be used
in place of `true`.
