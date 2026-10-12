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

The build takes about 60 s from clean, mostly to load Mathlib.

## Files

| File | Lines | Content |
|---|---|---|
| `UPRF/Basic.lean` | 267 | Section 2 functions and operators; Cantor A, V, K, L, J; bases; `Clos` (an inductive predicate); `PrimNN := Nat.Primrec`; `Suitable`; simulation and soundness lemmas; arithmetic facts; primitive recursiveness of the paper's functions |
| `UPRF/Sec6.lean` | 357 | the basis ⟨1, E, F⁺, FG, F^□⟩, first functions, Definition 6.1, Lemmas 6.2–6.6 (`Lemma_6_2` … `Lemma_6_6`) |
| `UPRF/Robinson.lean` | 288 | Robinson's theorem: `PrimNN_sub_C6`, `Robinson_1947_sec7_thm3` |
| `UPRF/Thm67.lean` | 75 | `Lemma_3_3`, `Theorem_6_7`, `Theorem_6_7_via_L33` (the paper's route) |
| `UPRF/Thm68.lean` | 222 | `Theorem_6_8` (bases with K and L) |
| `UPRF/Rem69.lean` | 179 | `Remark_6_9_I`, `_II`, `_III` (iteration from 1) |

## Status

Complete, with no `sorry`. The main theorems depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Every basis of Section 6 is proved suitable, that is, it
generates exactly Mathlib's `Nat.Primrec`.

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
