# Lean 4 + Mathlib formalization

Formalization of Section 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008), including R. M. Robinson's theorem and Lemma 3.3, and of the
open questions answered in the root README (§2, including §2.3 on general recursive functions).

**Naming:**
- `funX` is the function X of the paper, and `opX` an operator;
- `exprX` is the expression that the paper writes as `X ≡ …`;
- `X_expr` / `exprX_val` / `X_in` are the lemmas saying, respectively, what an expression
  computes, its value at a point, and membership in the closure.

## Requirements

- **elan**, the Lean toolchain manager: <https://github.com/leanprover/elan>. It installs the
  Lean version pinned in `lean-toolchain` (Lean 4.35.0).
- **Mathlib v4.35.0**. It is fetched automatically by `lake`, as pinned in `lakefile.toml` and
  `lake-manifest.json`.
- About 6 GB of disk space for the prebuilt Mathlib cache.

## Installation and build

```sh
lake exe cache get     # download the prebuilt Mathlib (once)
./build.sh             # build the library; prints only errors and warnings
```

The build takes about 2 min from clean: loading Mathlib, plus the proof search of the closure
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
| `UPRF/ExtA.lean` | 369 | open question of Remark 6.9: ⟨X, F⁺, FG, F^□⁽ᵃ⁾⟩ is suitable for every a ≥ 1 and X ∈ {E, K, L} (`Ext_a_E`, `Ext_a_K`, `Ext_a_L`, `Ext_a_all`) |
| `UPRF/ExtVb.lean` | 142 | ⟨E, F⁺ᵇ, FG, F^□⟩ with F⁺ᵇ(x) = F(x) + x + b is suitable iff b ≥ 1 (`Ext_Vb`, `Ext_Vb_zero`, `Ext_Vb_iff`) |
| `UPRF/ExtGR.lean` | 852 | README §2.3: the inversion `opInv`, the tactics `inv_eq` and `eval`, the generic lemmas `sub_inv_surj` and `sub_inv_val` (see below); ⟨1, X, F⁺, FG, F⁻¹⟩ generates J. Robinson's closure ⟨S, E, F + G, FG, F⁻¹⟩ (`GR_E_eq_JR`, `GR_K_eq_JR`, `GR_L_eq_JR`, `Ext_GR`); without 1 it does not (`Ext_GR0`); 1 and S are interchangeable (`GRS_eq_GR`, `Ext_GRS`) |
| `UPRF/ExtGRb.lean` | 494 | ⟨X, F⁺ᵇ, FG, F⁻¹⟩ generates the general recursive functions iff b ≥ 1 (`Ext_GRb_iff`) |
| `UPRF/ExtCn.lean` | 254 | any constant n̄ in place of 1: ⟨n̄, X, F⁺, FG, F^□⟩ is suitable iff n ≥ 1 (`Ext_Cn_suitable`), and ⟨n̄, X, F⁺, FG, F⁻¹⟩ generates the general recursive functions iff n ≥ 1 (`Ext_GRCn`) |

## Status

Complete, with no `sorry`. The main theorems depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Every basis of Section 6 is proved suitable, that is, it
generates exactly Mathlib's `Nat.Primrec`.

For §2.3, J. Robinson's theorem (Proc. AMS 1 (1950), §4, Theorem 3: her basis
⟨S, E, F + G, FG, F⁻¹⟩ generates the unary general recursive functions) is not formalized. It is
a hypothesis `Robinson_1950_sec4_thm3 : ∀ F, CJR F ↔ GR F` of the theorems `Ext_GR`, `Ext_GRS`,
`Ext_GRb_iff` and `Ext_GRCn`. Everything else is proved; `opInv` uses `Nat.find` with classical
logic.

## Metadata

`formalization.yaml` describes this formalization in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard (v0.4),
as used by the [Palomar Registry](https://palomar-registry.org): sources, scope, automation,
review status, and the correspondence between the paper's results and the Lean declarations.

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

For §2.3, `ExtGR.lean` adds:

- **`inv_eq h`** proves `opInv F x = v`, where `h : Function.Surjective F`, through
  `opInv_eqI`. It leaves two goals: `F v = x`, and the minimality `∀ y, F y = x → v ≤ y`. Each
  is tried with `rfl`, `omega` and `simp_all`, and is left to the user if these fail. For
  `opInv F = G`, use `funext x` first. Example: `Kinv_eq_Z` (K⁻¹ = Z).
- **`eval`** (or `eval [lemmas]`) computes the value of an expression at a point. It unfolds
  the operators and the basic functions, then tries `omega`, `ring1` and `nlinarith`.
- **Subtraction by inversion** is the generic pair `sub_inv_surj` / `sub_inv_val`. Suppose
  every y decomposes as y = base(t) + X(y) with X(y) ≤ bound(t), and X(base(t) + k) = k for
  k ≤ bound(t). If V(y) = y + c, then X (X V)⁻¹ subtracts c. `E_sub_inv` is the instance
  base(t) = t², bound(t) = 2t, and `K_sub_inv` is the instance base = A, bound = id.

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
