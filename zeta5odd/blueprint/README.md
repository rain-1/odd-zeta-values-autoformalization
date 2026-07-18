# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) for the
formalization: an explorable dependency graph in which every node is a
definition/lemma/theorem of the paper, coloured by formalization status and
linked to its Lean declaration. Here **every node is green** — the whole proof
is formalized and sorry-free.

- `src/content.tex` — the mathematical content, annotated with `\lean{…}`
  (the Lean declaration), `\leanok` (formalized), and `\uses{…}` (dependency
  edges).
- `src/web.tex`, `src/print.tex` — HTML and PDF roots.
- `web/`, `print/` — generated output (git-ignored).

## Build

Requires [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)
(`pip install leanblueprint`), a LaTeX toolchain with `xelatex`, and
**graphviz** (`dot`, e.g. `apt install graphviz`) for the dependency graph.

```bash
cd blueprint/src
plastex -c plastex.cfg web.tex     # → ../web/   (HTML + dependency graph)
latexmk                            # → ../print/print.pdf
```

Or, from the project root with the `leanblueprint` CLI:

```bash
leanblueprint web      # HTML
leanblueprint pdf      # PDF
```

## View

```bash
python3 -m http.server -d blueprint/web 8800
# then open http://localhost:8800  (see the "Dependency graph" link)
```
