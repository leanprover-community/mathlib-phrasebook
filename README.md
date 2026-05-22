This is a template for what would become a Mathlib phrasebook.

The documentation is intended to answer the question: "How do I say ... using Mathlib?"

To build it, run:

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


