# Mizar formalization

Formalization of Section 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008).

**Naming:**
- `funX` is the function X of the paper, and `opX` an operator;
- `exprX` is the expression that the paper writes as `X ≡ …`;
- `XExpr` / `…Val` / `XIn` are the lemmas saying, respectively, what an expression computes,
  its value at a point, and membership in the closure.

## Requirements

- **The Mizar system 8.1.15 with MML 5.94.1493**: <https://mizar.uwb.edu.pl/system/>.
  Prebuilt packages exist for Linux, macOS and Windows.
- A POSIX shell and Python 3. They are used by `miz.sh` to print the errors with their
  explanations.

## Installation and verification

1. Download the package for your platform and run its `install.sh`. It asks for a directory
   for the binaries and one for the shared files (MML, vocabularies, `mizar.msg`).
2. Put the binaries on the `PATH` and set `MIZFILES` to the shared directory, for example:

   ```sh
   export MIZFILES=/usr/local/share/mizar
   export PATH=/usr/local/bin:$PATH
   ```

3. Verify the article (about 11 s):

   ```sh
   ./miz.sh uprf
   ```

   `miz.sh` runs the accommodator and the verifier on `text/uprf.miz`, and prints `OK` or the
   list of errors with their messages. The vocabulary `dict/uprf.voc` is found automatically,
   because `miz.sh` works from this directory.

`./mmlthm.sh ARTICLE REGEX` is a small helper used during development. It searches an MML
abstract and shows the theorem labels.

## Layout

| Path | Content |
|---|---|
| `text/uprf.miz` | the article. It is a single file because Mizar can cite the theorems of another article only by number. |
| `dict/uprf.voc` | vocabulary (the new symbols) |
| `miz.sh`, `mmlthm.sh` | scripts described above |

## Contents of `uprf.miz` (4094 lines, 157 theorems, 52 definitions, 6 schemes)

Functions are `Element of Funcs(NAT,NAT)`. Operators are `UnOp`/`BinOp of Funcs(NAT,NAT)`, so
that they can be members of a basis. `F*G` is the composition FG of the paper.

| Paper | Mizar |
|---|---|
| Section 2: I, n̄, S, D, Sq, Hf, Rt, E, O, Sgn; F⁺, F^□, F + G, F ∸ G, FG | `funI`, `cst n`, `funS`, …; `opPlusI`, `opBox`, `opPlus`, `opMinus`, `opComp` |
| Cantor functions A, V, K, L (V by the paper's formula) | `funA`, `funV`, `funK`, `funL`; `VChar`, `Diag`, `Decomp` |
| bases and closures | `X is_closed_under I,U,B`, `clos(I,U,B)`; `ClosInit`, `ClosUnop`, `ClosBinop`, `ClosLeast` |
| ⟨1, E, F⁺, FG, F^□⟩ | `C6` |
| first functions (S, Sgn, 0̄, D, M₃, O, Q, Mod₃, R, Sq) | `SExpr` … `SqExpr`, `SIn` … `SqIn` |
| Definition 6.1 | `opMinusI`, `opOplus`, `opOminus`, `opOtimes` |
| Lemma 6.2 | `MinusIExprVal`, `Lemma62` |
| Lemma 6.3 | `HfExpr`, `RtExpr`, `Lemma63` |
| Lemma 6.4 | `OplusExprVal`, `OminusExprVal`, `Lemma64` |
| Lemma 6.5 | `PhatVal`, `OtimesExprVal`, `Lemma65` |
| Lemma 6.6 (difference function of footnote 8: `opDiffE`) | `PlusExprVal`, `MinusExprEq`, `Lemma66` |
| Theorem 6.7 | `Theorem67`: `C6 = RobinsonClos`; `Theorem67L33`: the basis of Lemma 3.3 is generated |
| Theorem 6.8 | `Theorem68`: `C6K = C6 & C6L = C6` |
| Remark 6.9 (I)–(III), F^□(1) | `opBox1`, `Remark69`: `ClosB1 funE = C6 & ClosB1 funK = C6 & ClosB1 funL = C6` |

## Status

Everything is proved at the level of **closures**: the paper's results are reduced to equalities
between closures.

- `Theorem67` shows
  $`\mathrm{clos}\langle 1, E, F^+, FG, F^\square\rangle = \mathrm{clos}\langle S, E, F+G, FG, F^\square\rangle`$.
  So the basis of Theorem 6.7 is suitable **iff** Robinson's basis is (R. M. Robinson 1947, §7,
  Theorem 3).
- `Theorem68` and `Remark69` show that the other five bases generate the same closure, so they
  are suitable as soon as the basis of Theorem 6.7 is.

Not yet formalized:

1. **Prim(ℕ,ℕ) itself.** The MML's notion of primitive recursion (`COMPUT_1`, `PrimRec`) is for
   n-ary partial functions on tuples. It is still to be connected with `Funcs(NAT,NAT)`.
2. **Robinson's theorem.**

**Two remarks on the proofs:**

- At closure level, Remark 6.9 needs $`F^{\square(1)}`$ in the closure. This is proved directly
  (`Box1In`):
  - $`F^{\square(1)} = \hat P \circ T^\square \circ S`$ with
    $`T = \mathrm{Sgn}\cdot(S F \hat P) + D O`$;
  - the product comes from `TimesIn`:
    $`FG = \mathrm{Hf}\big((F+G)^2 \mathbin{\dot-} (F^2 + G^2)\big)`$.
- Theorem 6.8 needs $`K`$ and $`L`$ in the closure (`KIn`, `LIn`). This uses
  $`K = I \mathbin{\dot-} A V`$, with $`A = \mathrm{Hf}\,(\mathrm{Sq}^+)`$ and
  $`V = \mathrm{Hf}\,\hat P\,\mathrm{Rt}\,S D D D`$.

## Mizar pitfalls met

- An inference cannot combine a definitional expansion with arithmetic. Split it into a
  `.=` step `by DefX` and a separate arithmetic step (with no justification).
- Numerals block instantiation. To use `RtI` for `funRt.4 = 2`, first state the premises
  `2*2 <= 4 & 4 < (2+1)*(2+1)` explicitly.
- Linear inequalities are not automatic. Use `XREAL_1:6/7/29/64`, `XXREAL_0:2`,
  `NAT_1:11/13`.
- Monus `-'`: use `NAT_D:34` (`i + j -' j = i`), `XREAL_1:233/235` and `NAT_2:8`.
- `u.F`, for `u` a `UnOp of Funcs(NAT,NAT)`, is known to be a function only with
  `registrations FUNCT_1, NUMBERS`.
- `F.x` is known to be natural only after the article's own registration
  `cluster F.x -> natural`.
- Cross-article references are by number only, hence the single file.
