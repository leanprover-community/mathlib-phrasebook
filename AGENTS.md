# Repository agents

Before writing or editing a phrasebook entry:

1. Read [`docs/how-to-write-a-how-to.md`](docs/how-to-write-a-how-to.md).
2. Read the project [`README.md`](README.md).
3. Start from `Phrasebook/Template.lean` for a new entry.

Make each section answer one question a reader might bring from a
formalization project. Put the usable Lean pattern before background, and
introduce every required namespace, notation, variable, instance, and
hypothesis before the example that needs it.

## Verify the rendered page

Run the relevant module build and render the complete phrasebook:

```bash
lake build Phrasebook.YourTopic
lake exe phrasebook
```

Inspect the result in `_out/html-multi/` in a browser. Source build success is
not enough: table syntax, long code lines, unrendered blocks, and broken
cross-references may only become visible in the rendered output.

## Final editing pass

Edit these out before declaring a page ready:

- Structural metaphors such as "bridge", "gate", "smoke test", "tapestry",
  and "weave". Name the actual artifact or translation.
- Vague flourishes such as "comprehensive", "leverage", "navigate"
  (metaphorical), "delve", "robust", and "in essence".
- Forward references to problems that are not explained later.
- Overclaims such as "every time", "almost every proof", and "the only way".
- Anthropomorphic descriptions such as a definition "capturing" or
  "encoding" something. State what the definition is.
- Placeholders, editing markers, duplicated setup, and copy-paste leftovers.
