# Repository agents

Before writing or editing a phrasebook entry:

1. Read [`docs/how-to-write-a-how-to.md`](docs/how-to-write-a-how-to.md).
2. Read the project [`README.md`](README.md).

## Verify the rendered page

Source build success is not enough. Before declaring a page ready,
look at the rendered HTML in a browser, or export it to PDF, or
attach screenshots. Markdown-pipe tables, ambiguous parenthetical
patterns, and other layout issues build cleanly from source but only
become visible in the rendered output.

## AI-tells to avoid

Edit these out before declaring a page ready. They read as AI slop:

- Em-dashes (`—`). Use parens, semicolons, or sentence breaks. If a
  sentence wants an em-dash, it has two ideas; split it.
- Structural metaphors: "bridge", "gate", "smoke test", "tapestry",
  "weave". Name the actual artifact and the actual translation.
- Vague flourishes: "comprehensive", "leverage", "navigate"
  (metaphorical), "delve", "ensure" (when meaning "make sure"),
  "robust", "in essence", "earn their keep".
- Forward references to gotchas you have not shown yet. Either
  explain now or do not mention.
- Overclaims: "every time", "almost every proof", "the only way".
  Soften to "usually", "most", "often".
- Anthropomorphising definitions ("captures", "encodes"). Say what
  the definition is.
