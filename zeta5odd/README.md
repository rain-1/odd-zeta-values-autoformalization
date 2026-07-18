# zeta5odd — one of ζ(5), …, ζ(33) is irrational, in Lean 4

A complete, sorry-free Lean 4 / Mathlib formalization of W. Zudilin's elementary
theorem ([SIGMA 2018, arXiv:1801.09895](https://arxiv.org/abs/1801.09895)), in
the s = 33 variant:

> **At least one of ζ(5), ζ(7), …, ζ(33) is irrational.**

```lean
theorem Zeta5Odd.zeta_odd_irrational : ∃ j ∈ oddIdx, Irrational (zetaVal j)
```

`#print axioms` → `[propext, Classical.choice, Quot.sound]`; zero sorries.
The s = 33 variant uses Hanson's elementary `d_n ≤ 3ⁿ` (also formalized from
scratch — current Mathlib has no PNT; s = 33 is the paper's own stated fallback).

## Explore

- 📈 **[Interactive blueprint](https://rain-1.github.io/odd-zeta-blueprint/)** —
  the dependency graph of the whole proof, every node linked to its Lean
  declaration (source in [`blueprint/`](blueprint/)).
- 📄 **Paper**: [`paper.pdf`](paper.pdf) (7 pp) — the human-readable writeup.
- ✅ **Independent verification**: [`COMPARATOR.md`](COMPARATOR.md) — a
  [`leanprover/comparator`](https://github.com/leanprover/comparator) harness
  ([`Challenge.lean`](Challenge.lean) / [`Solution.lean`](Solution.lean)) that
  re-checks the Mathlib-only statement with the Lean kernel; it **passes**.
- 🗂 **[`formalization.yaml`](formalization.yaml)** — provenance/process metadata
  ([schema](https://github.com/mathlib-initiative/formalization.yaml)).

## Build & check

```bash
lake exe cache get      # fetch the Mathlib olean cache
lake build              # builds the Zeta5Odd library (root theorem in Zeta5Odd/Main.lean)
printf 'import Solution\n#print axioms zeta_odd_irrational\n' > axcheck.lean
lake env lean axcheck.lean && rm axcheck.lean
# ⇒ depends on axioms: [propext, Classical.choice, Quot.sound]
```

Toolchain: `leanprover/lean4:v4.33.0-rc1` (see [`lean-toolchain`](lean-toolchain)).

## Layout

| Path | Contents |
|---|---|
| `Zeta5Odd/Main.lean` | Final assembly: `zeta_odd_irrational` (root-test endgame) |
| `Zeta5Odd/` | Lemma 4 asymptotics, Lemmas 1–3 integrality, Hanson's bound, numerics |
| `Challenge.lean`, `Solution.lean`, `config.json` | comparator harness |
| `blueprint/` | leanblueprint source (dependency graph) |
| `paper.tex`, `paper.pdf` | companion paper |
