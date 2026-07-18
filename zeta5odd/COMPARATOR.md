# Independent verification

> **Status: comparator has been run on this project and it passes** —
> `Lean default kernel accepts the solution` / `Your solution is okay!`
> (toolchain `leanprover/lean4:v4.33.0-rc1`). Reproduce it below.

This project ships a [`leanprover/comparator`](https://github.com/leanprover/comparator)
harness so anyone can confirm, without trusting the internals of the
formalization, that:

1. the **Mathlib-only** statement in `Challenge.lean` is what gets proved,
2. the proof uses no axioms beyond `propext`, `Quot.sound`, `Classical.choice`, and
3. the whole thing is accepted by the Lean kernel (via `lean4export` + a checker).

## The statement being verified

`Challenge.lean` imports **only Mathlib** and states, with `sorry`:

```lean
theorem zeta_odd_irrational :
    ∃ j ∈ (Finset.Icc 5 33).filter (fun j => Odd j),
      Irrational (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ j)
```

i.e. *at least one of ζ(5), ζ(7), …, ζ(33) is irrational*, where each ζ(j) is the
explicit real series ∑_{n≥1} 1/nʲ. `Solution.lean` proves the identical
statement from `Zeta5Odd.zeta_odd_irrational`. See `config.json`.

## Quick check (no comparator needed)

```bash
lake exe cache get      # fetch the Mathlib olean cache
lake build              # builds Zeta5Odd, Solution, and Challenge
printf 'import Solution\n#print axioms zeta_odd_irrational\n' > axcheck.lean
lake env lean axcheck.lean && rm axcheck.lean
# ⇒ 'zeta_odd_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Full comparator run

Install `landrun` (main branch) and a `lean4export` matching this toolchain
(`leanprover/lean4:v4.33.0-rc1`), then, from this directory:

```bash
lake exe cache get
lake build
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator/binary config.json'
```

(The `systemd-run` wrapper is comparator's recommended sandbox; see its README.)
