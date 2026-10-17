# Isabelle/HOL formalization

Formalization of Sections 2, 3 and 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008), including R. M. Robinson's theorem and the extensions
described in §2 of the main [README](../README.md):
- iteration from any a ≥ 1 (§2.1);
- the shifted operator (§2.2);
- the general recursive analogue with inversion, assuming J. Robinson's theorem (§2.3), and
  its remarks (1̄ can be replaced by S, or by any n̄ with n ≥ 1).

## Requirements

- **Isabelle2025-2**: <https://isabelle.in.tum.de>.
- **The AFP entry *Recursion Theory I*** (M. Nedzelsky), from the Archive of Formal Proofs
  release that matches Isabelle2025-2: <https://www.isa-afp.org/download/>.
  - Its `PrimRec1` is used as Prim(ℕ,ℕ).
  - Its Cantor pairing `sf`/`c_pair`/`c_fst`/`c_snd` is proved equal to the paper's
    `funA`/`funJ`/`funK`/`funL` in `UPRF_Aux.thy`.

## Installation and build

1. Install Isabelle, so that the `isabelle` executable is on the `PATH`. Otherwise set
   `ISABELLE=/path/to/isabelle` when calling the scripts.
2. Download and unpack the AFP. Then do one of the following:
   - point the scripts at its `thys` directory: `export AFP=/path/to/afp/thys`;
   - or copy (or symlink) `thys/Recursion-Theory-I` into `isabelle/afp/`, which is the
     scripts' default location.
3. Check the session:

   ```sh
   ./build.sh                          # batch check; prints progress, errors and slow commands
   ```

   The first run also builds the `Recursion-Theory-I` session. After that, `UPRF` takes about
   30 s.
4. To browse the theories in Isabelle/jEdit, with `Recursion-Theory-I` as the logic:

   ```sh
   ./jedit.sh                          # opens UPRF/UPRF_Robinson.thy
   ./jedit.sh UPRF/UPRF_Sec6.thy       # or any theory files
   ```

## Files (`UPRF/`)

| Theory | Contents |
|---|---|
| `UPRF_Sec2_Notation` | §2: the functions `funS`, `funE`, `funRt`, `funK`, …; `cst n` (the constant n̄); the operators `opBox` (F^□), `opBoxA a` (F^□(a)), `opPlus`, … |
| `UPRF_Basis` | bases, `clos`, Definition 3.2 `suitable`, simulation and soundness lemmas |
| `UPRF_Aux` | facts used silently by the paper (√, E, Cantor pairing); primitive recursiveness of all functions and operators |
| `UPRF_Methods` | Eisbach proof methods `clos_solve`, `clos_sound_m`, `clos_subset_m`, `simulate` (see below) |
| `UPRF_Sec3_Preliminaries` | §3: Robinson's basis and its soundness, difference functions, the basis of Lemma 3.3 |
| `UPRF_Sec6` | `opPlusI` (F⁺), the first constructions of §6, Definition 6.1, Lemmas 6.2–6.6 |
| `UPRF_Robinson` | Robinson's theorem (`Robinson_1947_sec7_thm3`) |
| `UPRF_Sec6_Thm67` | Lemma 3.3 and **Theorem 6.7** |
| `UPRF_Sec6_Thm68` | **Theorem 6.8** (bases with K and with L) |
| `UPRF_Sec6_Rem69` | **Remark 6.9** (I), (II), (III): iteration from 1 without the constant 1̄ |
| `UPRF_Ext_a` | ⟨X, F⁺, FG, F^□(a)⟩ is suitable for every a ≥ 1 and X ∈ {E, K, L} (`Ext_a_E`, `Ext_a_K`, `Ext_a_L`, `Ext_a_all`) |
| `UPRF_Ext_Vb` | ⟨E, F ↦ F + I + b̄, FG, F^□⟩ is suitable iff b ≥ 1 (`Ext_Vb`, `Ext_Vb_0`, `Ext_Vb_iff`) |
| `UPRF_Ext_GR` | inversion `opInv`; J. Robinson's basis ⟨S, E, F + G, FG, F⁻¹⟩ (`basis_JR`); ⟨1̄, X, F⁺, FG, F⁻¹⟩ generates the same closure for X ∈ {E, K, L} (`GR_E_eq_JR`, `GR_K_eq_JR`, `GR_L_eq_JR`); without 1̄ every generated function fixes 0 (`GR0_fix0`); assuming J. Robinson's theorem, both bases give the general recursive functions (`Ext_GR`, `Ext_GR0`); the remark that 1̄ and S are interchangeable: ⟨S, X, F⁺, FG, F⁻¹⟩ generates the same closure (`GRS_eq_GR`, `Ext_GRS`), with 0̄ ≡ K S K⁻¹, (E S E⁻¹)², L (L S)⁻¹ S |
| `UPRF_Ext_GRb` | ⟨X, F^{+b}, FG, F⁻¹⟩ generates the same closure as J. Robinson's basis for b ≥ 1 (`GRb_E_eq_JR`, `GRb_K_eq_JR`, `GRb_L_eq_JR`); assuming J. Robinson's theorem, it gives the general recursive functions iff b ≥ 1 (`Ext_GRb_iff`) |
| `UPRF_Ext_Cn` | the constant 1̄ can be any n̄ with n ≥ 1: ⟨n̄, X, F⁺, FG, F^□⟩ is suitable iff n ≥ 1 (`Ext_Cn_suitable`), and, assuming J. Robinson's theorem, ⟨n̄, X, F⁺, FG, F⁻¹⟩ gives the general recursive functions iff n ≥ 1 (`Ext_GRCn`); generic in the set of unary operators (`C_eq_C1_ELK`), with the descents `E_desc`, `K_desc`, `L_desc1`, `L_desc2` |

**Naming:**
- the function X of the paper is `funX`, and an operator is `opX`;
- when the paper defines `X ≡ …`, the expression is `exprX` (or a lemma `X_expr`), and a
  lemma `…_val` states what it computes.

## Proof methods (Eisbach)

Three mechanisms recur in every theorem. `UPRF_Methods` captures them as Eisbach methods,
driven by three named-theorem collections:
- `clos_defs`: the selector equations of each basis, e.g. `inits basis_6 = {cst 1, funE}`,
  obtained from `basis.sel` folded with the basis definition;
- `clos_rules`: generic closure rules, one per operator, plus the membership lemmas
  (`S_in`, `exprMinusI_in`, …);
- `prim_intros`: the primitive recursiveness lemmas.

The methods:
- **`clos_solve`** proves `F ∈ clos B`. It is recursive and backtracks. At each step it tries,
  in order:
  1. an assumption;
  2. a basis side condition solved by `simp` with `clos_defs`;
  3. a rule from `clos_rules` (or from `add:`);
  4. an initial function of the basis.

  Each generic rule fixes its operator (for example `F ∈ clos B ⟹
  opPlusI ∈ unops B ⟹ opPlusI F ∈ clos B`), so unification stays first
  order.
- **`clos_sound_m`** proves `clos B ⊆ PrimNN`.
- **`clos_subset_m`** proves `clos B₁ ⊆ clos B₂`.
- **`simulate S`** proves `suitable B` from a suitable basis `S`. It applies
  `suitable_by_simulation`, splits the bases with `simp only` (so the functions are not
  normalized), and closes every case with the methods above.

With them, every suitability theorem of Theorem 6.8, Remark 6.9 and the extensions is
`by (simulate S: …)`, and a membership lemma is `by (subst X_expr[symmetric]) clos_solve`.

Two more methods and one generic lemma serve the general recursive extensions:
- **`eval`** (in `UPRF_Methods`) computes the value of an expression at a point. It unfolds
  the operators and the basic functions with `simp only` (collection `eval_simps`, extended in
  later theories with `opPlusIb_def` and `funM3_def`, plus the facts given with `add:`). Then it
  tries `simp` and `linarith` on the arithmetic goal that is left.
- **`inv_eq`** (in `UPRF_Ext_GR`) proves `opInv F x = v`, or `opInv F = G` after `rule ext`,
  through `opInv_eqI`. The surjectivity of F is the fact given with `surj:`. The goals
  `F v = x` and `F y = x ⟹ v ≤ y` are tried with `simp` and `linarith` using `add:`, and are left
  to the user if these fail. Examples: `Kinv_eq_Z`, `Linv_eq_sf`.
- **`sub_inv`** is the generic subtraction by inversion. Suppose every y decomposes as
  y = base(t) + X(y) with X(y) ≤ bound(t), and X(base(t) + k) = k for k ≤ bound(t). If
  V(y) = y + c, then X (X V)⁻¹ subtracts c (`sub_inv_val`), and X V is onto
  (`sub_inv_surj`). `E_sub_inv` (base(t) = t², bound(t) = 2t) and `K_sub_inv` (base = A,
  bound = id) are instances.

## Status

Everything is proved: there is no `sorry`, and the session builds without `quick_and_dirty`.
The only assumption is J. Robinson's theorem, stated as a locale assumption in
`UPRF_Ext_GR` (see below).

**How Robinson's theorem is proved** (`UPRF_Robinson`). This is not Robinson's proof.
- The AFP proves `PrimRec1 = PrimRec1'`. `PrimRec1'` is generated by $`0`$, $`S`$, $`K`$,
  $`L`$ under composition, pairing $`J(F,G)`$ and a unary recursion operator `UnaryRecOp`.
- Lemmas 6.2–6.6 do not depend on Robinson's theorem. With them, the closure of
  $`\langle 1, E, F^+, FG, F^\square\rangle`$ contains:
  - $`A`$, $`V`$, $`K`$, $`L`$ and $`J(F,G)`$;
  - products;
  - definition by cases.
- `UnaryRecOp g h` is obtained from one iteration $`T^\square`$.
  - $`T`$ walks a triangle, row $`N`$ and column $`y \le N`$, carrying the value
    $`J(J(N,y), f(y, L(N-1)))`$.
  - The value at $`z`$ is read in row $`z+1`$, so `UnaryRecOp g h` $`= L \circ T^\square \circ (A S + K)`$.

**General recursive functions** (`UPRF_Ext_GR`, `UPRF_Ext_GRb`, §2.3 of the main README).
- **Inversion.** J. Robinson applies F⁻¹(x) = μy [F(y) = x] only to onto functions. Operators of
  a basis must be total, so `opInv F` is the least preimage when `F` is onto, and `F` itself
  otherwise. A closure under `opInv` is exactly a closure under the restricted inversion.
- **J. Robinson's theorem is assumed, not proved.** The AFP entry has no total recursive
  functions. All closure equalities (`GR_E_eq_JR`, `GRb_E_eq_JR`, …) are proved without
  assumptions. Only the final statements live in the locale `Robinson_1950`, whose single
  assumption is `clos basis_JR = GR` for an abstract set `GR`. No axiom is added.
- **Reuse of Lemmas 6.2–6.6.** Their value lemmas (`exprPlus_val`, …) do not depend on the
  closure, so only the memberships are proved again, for the new closure. Before that,
  `E⁻¹` (`Einv_val`), `Sq`, `Hf` and `Rt` are generated with inversion. With K, the
  function E itself is generated (`E_expr_K`).
- **The shifted operator** reuses `opPlusIb` from `UPRF_Ext_Vb`. For each X, a successor is
  built for every b ≥ 1, with b as a variable. A predecessor then gives `F⁺ = P^b F^{+b}`
  (`plusI_from_pred`), and `GR_sub_GRb` simulates the basis of `UPRF_Ext_GR`.

**Deviations from the paper:**
- Lemma 3.3 is derived from Robinson's §7 Theorem 3 instead of Lemma 3.1 and Theorem 2 of
  Robinson's paper. This avoids formalizing closures of multi-argument functions.
- Operators such as $`F^-`$, $`\oplus`$, $`\ominus`$, $`\otimes`$ are defined twice: semantically
  (Definition 6.1) and as the paper's formulas (`exprMinusI`, `exprOplus`, …). Correctness is
  proved pointwise, so each value lemma assumes $`F(x) \ge x`$ only at the point $`x`$ where
  it is used.
