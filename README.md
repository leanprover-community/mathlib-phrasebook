# A Mathlib Phrasebook

The documentation is intended to answer the question: "How do I say ... using Mathlib?"
where "..." stands for a mathematical topic or object.
As a [how-to guide](https://diataxis.fr/how-to-guides/), the focus is on practical guidance
that answers a specific question or resolves a specific issue.

## Contribution guide

You are invited to contribute more answers to mathematical formalization questions to the phrasebook.
Before opening a pull request, always make sure your contribution gets built and displayed correctly
by following the development guide below to check the output in your browser.

The basic rule for writing a good phrasebook entry: keep the target audience in mind.
The reader of the phrasebook is working on a project, encounters a specific mathematical question and is looking for an answer.

The phrasebook is structured as a collection of sections that should be readable independently of one another.
Make sure each section clearly indicates the prerequisites needed to understand it.
Use titles to clearly indicate where the reader can find their answer.
A phrasebook entry should be structured around the mathematics, not the way it is implemented in Mathlib:
a title that contains Lean code is a good indication that restructuring is needed.

The text of a phrasebook entry should consist of advice using idiomatic Mathlib design patterns.
Do not make the reader search through multiple long paragraphs.
Use examples to make your point, but keep your advice general:
the reader already has a project and does not want to work through a tutorial from top to bottom.
In a how-to guide, resist the temptation to explain *why*:
at most link to a different website that can be read at leisure after the reader's problem has been fixed.

To avoid duplication of effort, we currently do not accept material that can be fully
covered by referring to existing community-maintained documentation.
In particular, a lot of undergraduate mathematics is already explained in [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).
You can start your phrasebook section with a reference to the relevant MiL chapter
and then list how your chapter goes beyond that level.

## Development guide

To build this documentation on your machine, run:

```
lake exe cache get
lake exe phrasebook
```

To display the documentation in your browser, you need a simple HTTP server, like the one included in Python. Run:

```
python -m http.server 8000 -d _out/html-multi
```

and navigate in your browser to <http://localhost:8000>. You will see the local copy of the documentation as it was built on your computer.
(You can also run the `local-build.sh` script.)

If you do not have Python installed, you can open the generated output in `_out/html-multi/index.html` in your browser.

We use the Verso textbook template as a base. Its Readme file follows below:

# Original Verso readme:

This textbook is written in the `Manual` genre. It uses the same
version of Lean for the example code as it does for Verso itself;
please see [the package description example](../package-docs) for an
example in which the Lean code is external to the document and written
in a different version of Lean.

# Code Samples

Additionally, this example demonstrates a non-trivial extension to the
manual genre: extraction of Lean modules from the inline examples. This
extension uses [a custom `savedLean` code block](TextbookTemplate/Meta/Lean.lean)
to indicate that an example or exercise should be saved. At elaboration time,
a custom block element saves the original filename and the contents of the
code block. Then, in [`TextbookTemplateMain.lean`](TextbookTemplateMain.lean), the
custom build step `buildExercises` traverses the entire book prior to HTML
generation, collecting the exercise blocks. The collected blocks are assembled
into files and written to the `example-code` subdirectory of the output.


