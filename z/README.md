# Z/EVES formalization

Formalization of Section 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008), and of the two open questions answered in the root README (§2),
in Z (ZF set theory with types), checked by Z/EVES 2.3.

The scope is the same as the Mizar version: everything is proved **at the level of closures**.
The paper's results become equalities between closures, and Robinson's theorem (that
⟨S, E, F + G, FG, F^□⟩ is suitable) is assumed, not proved.

**Naming** follows the other formalizations:
- `funX` is the function X of the paper, `opX` an operator, `cst n` the constant n̄;
- `exprX` is the expression that the paper writes as `X ≡ …`;
- `XExpr` / `…Val` / `XIn` say, respectively, what an expression computes, its value at a
  point, and membership in the closure.

## Requirements

- **Z/EVES 2.3.** It exists only as a 32-bit Linux program (a CMUCL core). A copy of the
  distribution is at <https://github.com/arandilopez/z-eves>.
- On Linux: the 32-bit C library (Debian: `dpkg --add-architecture i386` and
  `apt install libc6:i386`).
- On macOS: a Linux VM. The scripts use a [Lima](https://lima-vm.io) instance named `zeves`
  (Debian, set up as above). Lima mounts the home directory, so the files must be under `~`.

## Installation and verification

1. Unpack Z/EVES into `/opt/Z/Z-Eves` (inside the VM on macOS). It must contain `system/` and
   `library/`. Another place can be given with `ZEVES_DIR`.
2. On macOS, start the VM: `limactl start zeves` (`ZEVES_VM` names another instance).
3. Check the installation, then the development (about 45 s):

   ```sh
   ./zeves.sh smoke.tex
   ./zeves.sh uprf.tex
   ```

   `zeves.sh` reads the file in text mode, runs every proof script, and prints the status. The
   last lines must be `No unproved goals. Congratulations!`.

## PDF

`./pdf.sh` typesets `uprf.tex` into `uprf.pdf` (A4, about 140 pages, with the proof scripts),
using pdflatex. It needs a TeX distribution with `amssymb` and `geometry`, and it takes the
style file `z-eves.sty` from the Z/EVES distribution (`ZEVES_DIR`; on macOS through the VM).
The build files go to `build/`. The PDF is committed, so it can be read without building it.

`pdfsetup.tex` is read before `uprf.tex` and changes only the typesetting. In `z-eves.sty`
every line of a box is one row of an alignment, which TeX cannot break, so long formulas ran
off the page. `pdfsetup.tex` typesets each row as a ragged-right paragraph, with breaks allowed
after commas and between the words of proof scripts. It also fixes theorems whose text begins
with `Plus…`, which `z-eves.sty` read as a glue specification.

## Layout

| Path | Content |
|---|---|
| `uprf.tex` | the development (a single Z/LaTeX document) |
| `smoke.tex` | installation check: a few trivial facts |
| `zeves.sh` | checker: runs Z/EVES on a file and prints the proof status |
| `pdf.sh`, `pdfsetup.tex` | typesetting: builds `uprf.pdf` (see above) |
| `zcmd.sh` | development helper: reads a file, then runs interactive commands from a second file (`print declaration X;`, `try P;`, `prove;`, …) |
| `gen/zgen.py` | development helper: Python functions that print the recurring boilerplate (a function with its witness and consistency theorem, an operator, an induction, a closure with its rules, closure inclusions) |

## Contents of `uprf.tex` (8 320 lines, 632 theorems, 33 axiomatic definitions)

Functions are the elements of `\nat \fun \nat`. Operators are total functions on them, so they
can be members of a basis. `comp(F, G)` is the composition FG of the paper. The closure is
curried: `clos~I~U~B` is the least set that contains `I` and is closed under the unary
operators `U` and the binary operators `B`.

| Paper | Z/EVES |
|---|---|
| Section 2: I, n̄, S, D, Sq, Hf, Rt, E, O, Sgn; F⁺, F^□, F^□(a), F + G, FG | `funI`, `cst n`, `funS`, …; `opPlusI`, `opBox`, `opBoxA a`, `opPlus`, `comp` |
| bases and closures | `UClosed`, `BClosed`, `clos`; `ClosInit`, `ClosUnop`, `ClosBinop`, `ClosLeast` |
| ⟨1, E, F⁺, FG, F^□⟩ and Robinson's ⟨S, E, F + G, FG, F^□⟩ | `C6`, `RobinsonClos` |
| Definition 6.1 | `opOplus`, `opOtimes`; F ⊖ G only as the expression `exprOminus` |
| Lemma 6.2 | `Lemma62` |
| Lemma 6.3 | `HfExpr`, `RtExpr` |
| Lemma 6.4 | `OplusEq`, `Lemma64` |
| Lemma 6.5 | `PhatVal`, `OtimesExprVal`, `Lemma65` |
| Lemma 6.6 (difference function of footnote 8: `opDiffE`) | `PlusExprVal`, `MinusExprEq`, `Lemma66` |
| Theorem 6.7 | `Theorem67`: `C6 = RobinsonClos` |
| Cantor functions A, V, K, L | `funA`, `funV`, `funK`, `funL`; `VChar`, `Diag`, `Decomp`, `KAt`, `LAt` |
| Theorem 6.8 | `Theorem68`: `C6K = C6 \land C6L = C6` |
| Remark 6.9 (I)–(III) | `Remark69`: the closures of ⟨X, F⁺, FG, F^□(1)⟩, X ∈ {E, K, L}, equal `C6` |
| open question of Remark 6.9: iteration from any a ≥ 1 | `ExtAE` (a ≥ 2), `ExtAEOne`, `ExtAK`, `ExtAL`, `ExtAAll` |
| shifted operator F⁺ᵇ(x) = F(x) + x + b | `opPlusIb`, `ExtVb` (b ≥ 1), `ExtVbZero`, `ExtVbIff`: equal to `C6` iff `1 \leq b` |

## Status

Everything listed above is proved, and Z/EVES reports no unproved goals.

- `Theorem67` shows that ⟨1̄, E, F⁺, FG, F^□⟩ and Robinson's basis generate the same closure.
  So the basis of Theorem 6.7 is suitable **iff** Robinson's basis is.
- `Theorem68`, `Remark69`, `ExtAAll` and `ExtVb` show that the other bases generate the same
  closure as well. `ExtVbZero` shows that for b = 0 the closure is different: every generated
  function fixes 0 (`CVZeroFix`), so 1̄ is missing.

**Definitions are not axioms.** In Z an axiomatic box `axdef` is an axiom. Every one of the 33
boxes is therefore followed by a consistency theorem `XEx`, which proves `\exists X: T @ P` for
the box's declaration `X: T` and predicate `P`. The witness `XWit` is an explicit term (a
λ-term, an iterate `iter`, or a relation for the functions defined by a specification, such as
`funV`). The other definitions are abbreviations (`==`), which are conservative.

Not formalized:

1. **Prim(ℕ,ℕ) itself.** Z/EVES has no library of computable functions.
2. **Robinson's theorem.**

**Differences from the other formalizations:**

- **The cases of iteration from a.** The common part (`ExtAOne`, `ExtASup`) only needs `X ∈ Mult`
  (for every i ≥ 1 some r with X(r(i+1)) = i), 0̄ and a predecessor in the closure. It holds
  for every a ≥ 1, so the predecessors of K and L built for a ≥ 2 in the root README also
  work for a = 1, and Remark 6.9 (II)–(III) are instances of `ExtAK` and `ExtAL`. For E and
  a = 1, the predecessor of the root README needs a² − a − 1 ≥ 0, so `ExtAEOne` uses Remark 6.9's
  P̂ = E S² ((G⁺)⁺)⁺ instead. Its G is the function G of the root README with a = 1, which equals
  (n + 1)².
- **The shifted operator** is formalized with b = c + 1 throughout (`ExtVbSucc`), so that no
  truncated subtraction appears in the polynomial identities.

## Z/EVES pitfalls met

- **Abbreviations of types.** Do not abbreviate `\nat \fun \nat`: the domain checker cannot see
  through the abbreviation.
- **λ-terms do not reduce by themselves.** Total functions are built with the lemma `FunIntro`,
  and values are read with `pairInFunction`.
- **Normal forms.** Z/EVES rewrites `x + 1` to `1 + x`, so rewrite rules must be stated in
  normal form. Arguments of functions are *not* AC-normalized, so a lemma about `f~(a * b)`
  does not apply to `f~(b * a)`: state lemmas in the form that appears in the goal.
- **Arithmetic.** Linear arithmetic is automatic; nonlinear facts need
  `timesMonotonic2[a, b, c, d]`. Facts such as `0 \leq f~x` must be supplied (`UFNonneg`), and
  positive comparisons work better than negated ones (`LeOrGt`).
- **Rule order.** An enabled rule can rewrite a hypothesis added with `use` before it is used,
  so some definitions are disabled rules (`EVal`, `KVal`, `C6Def`, …). Value lemmas stated as
  conditional rules rewrite nested expressions innermost-first, which is usually what is
  wanted. Sometimes a rule fires too early, as `BoxSuc` does before a value lemma for `opBox`:
  `with disabled (BoxSuc) prove`.
- **Long membership chains.** A hypothesis added with `use` is simplified before the facts it
  depends on are known. Long chains of closure memberships are therefore proved one step at a
  time (`use CBComp[…]; prove;`, and so on).
- **Equalities in hypotheses** are used as rewrite rules, in a direction chosen by Z/EVES. To
  conclude `F \in C` from `G \in C` and `G = F`, prove `G \in C` as a separate lemma, or use
  `equality substitute`.
- **Types.** Membership in the maximal type `\power (\num \cross \num)` is not derived for
  compound terms, so the rule `UFInPow` supplies it. Instantiate generic lemmas at base types,
  for example `SubAntisym[\nat \fun \nat]`.
- **Generated names.** Bound variables are renamed (`x\_\_0`, `F\_\_1`, …). Read the names from
  the proof trace before writing `instantiate`.
- **Scripts.** A command with no effect aborts the rest of the script. So does a command that
  refers to a variable that no longer exists, for example after the goal has already been
  proved.
