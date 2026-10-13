# Lean 4 + Mathlib formalization

Formalization of Section 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008), including R. M. Robinson's theorem and Lemma 3.3.

**Naming:**
- `funX` is the function X of the paper, and `opX` an operator;
- `exprX` is the expression that the paper writes as `X ≡ …`;
- `X_expr` / `exprX_val` / `X_in` are the lemmas saying, respectively, what an expression
  computes, its value at a point, and membership in the closure.

## Requirements

- **elan**, the Lean toolchain manager: <https://github.com/leanprover/elan>. It installs the
  Lean version pinned in `lean-toolchain` (Lean 4.34.1).
- **Mathlib v4.34.1**. It is fetched automatically by `lake`, as pinned in `lakefile.toml` and
  `lake-manifest.json`.
- About 6 GB of disk space for the prebuilt Mathlib cache.

## Installation and build

```sh
lake exe cache get     # download the prebuilt Mathlib (once)
./build.sh             # build the library; prints only errors and warnings
```

The build takes about 95 s from clean: loading Mathlib, plus the proof search of the closure
tactics.

## Files

| File | Lines | Content |
|---|---|---|
| `UPRF/Attr.lean`, `UPRF/Tactics.lean` | 7 + 90 | proof automation: the simp attribute `clos_defs` and the tactics `clos_solve`, `prim_sound`, `simulate` (see below) |
| `UPRF/Basic.lean` | 267 | Section 2 functions and operators; Cantor A, V, K, L, J; bases; `Clos` (an inductive predicate); `PrimNN := Nat.Primrec`; `Suitable`; simulation and soundness lemmas; arithmetic facts; primitive recursiveness of the paper's functions |
| `UPRF/Sec6.lean` | 368 | the basis ⟨1, E, F⁺, FG, F^□⟩, first functions, Definition 6.1, Lemmas 6.2–6.6 (`Lemma_6_2` … `Lemma_6_6`) |
| `UPRF/Robinson.lean` | 281 | Robinson's theorem: `PrimNN_sub_C6`, `Robinson_1947_sec7_thm3` |
| `UPRF/Thm67.lean` | 51 | `Lemma_3_3`, `Theorem_6_7`, `Theorem_6_7_via_L33` (the paper's route) |
| `UPRF/Thm68.lean` | 191 | `Theorem_6_8` (bases with K and L) |
| `UPRF/Rem69.lean` | 150 | `Remark_6_9_I`, `_II`, `_III` (iteration from 1) |

## Status

Complete, with no `sorry`. The main theorems depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Every basis of Section 6 is proved suitable, that is, it
generates exactly Mathlib's `Nat.Primrec`.

## Proof automation (`Tactics.lean`)

Three mechanisms recur in every theorem. `Tactics.lean` captures them as tactic macros.

- **`clos_solve`** proves `Clos B F` by recursive search with backtracking (`first`). At each
  step it tries, in order:
  1. an assumption;
  2. a basis side condition (`clos_mem`: `simp only` with the basis definitions tagged
     `@[clos_defs]`);
  3. a registered membership lemma (`clos_hint`);
  4. a hypothesis used as a rule (`apply_assumption`);
  5. a generic closure rule, one per operator;
  6. an initial function of the basis.

  All applications use `with_reducible`, so unification never unfolds the paper's functions.
  `clos_hint` is extensible: each file registers its lemmas with
  ``macro_rules | `(tactic| clos_hint) => `(tactic| with_reducible apply S_in)``.
- **`prim_sound`** proves soundness: `clos_sound`, a case analysis of the basis, then
  `solve_by_elim` with the primitive recursiveness lemmas and the hypotheses.
- **`simulate S`** proves `Suitable B` from a suitable basis `S`, with the two tactics above.

With them, every theorem of 6.8 and 6.9 and Lemma 3.3 is a `simulate`, and a membership lemma
is `by rw [← X_expr]; clos_solve`.

## Notes

- **Mathlib's `Nat.Primrec`** is a unary characterization: $`0`$, $`S`$, the two components of
  `Nat.unpair`, `Nat.pair`, composition and `prec`.
- **Mathlib pairs with Szudzik's function**, not Cantor's. So the Robinson proof needs
  `Nat.pair` and `Nat.unpair` in the closure, and these involve a case split on $`e < s`$. The
  proof builds three things, using only Lemmas 6.2–6.6:
  - a comparison indicator
    $`[F < G] = \mathrm{Sgn}\big(d(d(F,G) + G,\,F)\big)`$, where $`d`$ is the difference
    function of Lemma 6.6;
  - general truncated subtraction;
  - definition by cases.
- **Primitive recursion comes from $`F^\square`$.**
  - A step function walks the rows of a Cantor triangle.
  - The value $`R(z,m)`$ is read in row $`J(m,z)+1`$.
- **Closures are an inductive predicate** (`Clos`), so induction over a closure is structural.
- **Automation used:** `simp`, `omega` (linear arithmetic, truncated subtraction), `nlinarith`,
  `ring`.
- **Pitfall:** `∘` associates to the right, so membership proofs nest to the right.
