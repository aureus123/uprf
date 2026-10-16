# Unary primitive recursive functions (UPRF)

This repository accompanies D. E. Severin, *Unary primitive recursive functions*,
J. Symbolic Logic 73(4) (2008), 1122–1138 ([arXiv:cs/0603063](https://arxiv.org/abs/cs/0603063)).

It contains:

- the paper's results;
- the questions it leaves open, with the ones answered here;
- the problems that are still open;
- machine-checked formalizations of Section 6 in four proof assistants: Isabelle/HOL, Mizar,
  Lean 4 and Rocq.

| Folder | Content |
|---|---|
| [`references/`](references/README.md) | summaries of the papers cited by the UPRF paper |
| [`others/`](others/README.md) | summaries of further papers on restricted recursion schemes (Péter, Kleene, Axt, Calude, Georgieva, Mazzanti, …) |
| [`isabelle/`](isabelle/README.md), [`mizar/`](mizar/README.md), [`lean/`](lean/README.md), [`rocq/`](rocq/README.md) | the formalizations |

---

## 1. Results of the paper

### Notation

All functions are unary, $`\mathbb{N} \to \mathbb{N}`$.

**Functions:**
- $`S`$ successor and $`I`$ identity;
- $`\bar n`$ the constant function with value $`n`$;
- $`E(x) = x - \lfloor\sqrt{x}\rfloor^2`$, the excess over a square;
- $`K`$ and $`L`$, the inverses of Cantor's pairing $`J(x,y) = A(x+y) + x`$, where
  $`A(t) = t(t+1)/2`$.

**Operators:**
- $`FG`$ is composition, and $`F + G`$ the pointwise sum.
- $`F^+(x) = F(x) + x`$.
- $`F^\square`$ is pure iteration without parameters:
  $`F^\square(0) = 0`$ and $`F^\square(x+1) = F(F^\square(x))`$.
- $`F^{\square(a)}`$ is the same iteration started at $`a`$.

**Bases.** A *basis* $`\langle F_1, \dots, F_n, \text{operators}\rangle`$ lists initial functions
and operators, and $`\mathrm{clos}\,\mathcal{F}`$ is the least set that contains the initial
functions and is closed under the operators. A basis is **suitable** when
$`\mathrm{clos}\,\mathcal{F} = \mathrm{Prim}(\mathbb{N},\mathbb{N})`$, the set of unary primitive
recursive functions (Definition 3.2).

### Main results

The paper studies restricted recursion schemes in the line of R. M. Robinson (1947) and
Gladstone (1967, 1971). Its main results are the following.

- **§3 (preliminaries).**
  - Lemma 3.3: $`\langle S, \mathrm{Sq}, O, \mathrm{Hf}, \mathrm{Rt}, F+G, F-G, FG, F^\square\rangle`$
    is suitable.
  - Lemma 3.4 (Robinson): the multi-argument primitive recursive functions are recovered from a
    suitable basis by adding projections, $`+`$ and substitution.
- **§4 (mixed iteration without parameters, scheme $`\mathrm{rec}_7`$).**
  - Theorem 4.4:
    $`\mathrm{Prim} = \mathrm{clos}\langle S, I^k_n, O, +, \mathrm{subst}, M[F]\rangle`$.
  - Theorem 4.5: without the cosignum $`O`$, every generated unary function is non-decreasing.
  - Theorem 4.6: $`O`$ can be replaced by any function that is not non-decreasing.
- **§5 (pure iteration without parameters).**
  - Theorem 5.8: $`\langle S, \vert F-G\vert, FG, F^\square\rangle`$ and
    $`\langle S, F \mathbin{\dot-} G, FG, F^\square\rangle`$ are suitable.
  - Theorem 5.9 is the multi-argument analogue.
- **§6 (iteration and a unary operator).** Robinson proved that
  $`\langle S, E, F+G, FG, F^\square\rangle`$ is suitable. The paper removes the binary operator:
  - **Theorem 6.7:** $`\langle \bar 1, E, F^+, FG, F^\square\rangle`$ is suitable.
    Lemmas 6.2–6.6 build $`F^-`$, $`F \oplus G`$, $`F \ominus G`$, $`F \otimes G`$, $`F + G`$
    and a difference $`F - G`$ from the unary operator $`F^+`$.
  - **Theorem 6.8:** $`\langle \bar 1, K, F^+, FG, F^\square\rangle`$ and
    $`\langle \bar 1, L, F^+, FG, F^\square\rangle`$ are suitable.
  - **Remark 6.9:** with iteration started at $`1`$, the constant can be dropped:
    $`\langle X, F^+, FG, F^{\square(1)}\rangle`$ is suitable for $`X \in \{E, K, L\}`$.
    Section 6 ends with the question for $`a > 1`$.

---

## 2. Open questions of the paper and similar problems (solved here)

Both results below are formalized in all four proof assistants, and the proofs below follow
the Isabelle formalization:

| | §2.1 (iteration from a) | §2.2 (shifted operator) |
|---|---|---|
| Isabelle/HOL | `isabelle/UPRF/UPRF_Ext_a.thy`: `Ext_a_all` | `isabelle/UPRF/UPRF_Ext_Vb.thy`: `Ext_Vb_iff` |
| Lean 4 | `lean/UPRF/ExtA.lean`: `Ext_a_all` | `lean/UPRF/ExtVb.lean`: `Ext_Vb_iff` |
| Rocq | `rocq/theories/ExtA.v`: `Ext_a_all` | `rocq/theories/ExtVb.v`: `Ext_Vb_iff` |
| Mizar | `mizar/text/uprf.miz`: `ExtA` | `mizar/text/uprf.miz`: `ExtVbIff` |

As for Section 6, Mizar states them at closure level: for $`a \ge 1`$ the bases generate the
same closure as $`\langle \bar 1, E, F^+, FG, F^\square\rangle`$, and the shifted basis does
so if and only if $`b \ge 1`$.

**Conventions used in the proofs:**
- $`F^k`$ denotes the $`k`$-fold composition $`F \circ \dots \circ F`$.
- A *predecessor* is any function $`\hat P`$ with $`\hat P(x+1) = x`$ for all $`x`$.
- Two arithmetic facts are used repeatedly:
  - $`E(m^2 + k) = k`$ whenever $`k \le 2m`$;
  - $`K(A(t)+k) = k`$ and $`L(A(t)+k) = t-k`$ whenever $`k \le t`$.
- *Soundness* is never an issue: every function and operator involved is primitive recursive.
  Each proof therefore only shows that the basis of Theorem 6.7 (or 6.8) is simulated.

### 2.1 Iteration started at any $`a \ge 2`$ (question at the end of Remark 6.9)

> **Theorem.** For every $`a \ge 1`$ and $`X \in \{E, K, L\}`$, the basis
> $`\mathcal{B}_a(X) = \langle X, F^+, FG, F^{\square(a)}\rangle`$ is suitable.

The case $`a = 1`$ is Remark 6.9. From now on, fix $`a \ge 2`$.

#### Common part

Assume that $`\mathrm{clos}\,\mathcal{B}_a(X)`$ contains $`\bar 0`$, that $`X(0) = 0`$, and that
there are multipliers $`m(j)`$ with $`X(m(j)\,j) = j - 1`$ for every $`j \ge 2`$.

1. **Multiples.** Let $`M_r = (\cdots(\bar 0^+)^+\cdots)^+`$, with $`r`$ applications of $`^+`$.
   Then $`M_r(x) = r x`$. In particular $`I = M_1`$ and $`D = M_2`$ are in the closure.
2. **Descent from $`a`$ to $`1`$.** Let $`T_j = X M_{m(j)}`$. Then $`T_j(j) = j-1`$ for
   $`j \ge 2`$, and $`T_j(0) = 0`$. Hence the composition $`N = T_2 T_3 \cdots T_a`$ satisfies
   $`N(a) = 1`$ and $`N(0) = 0`$.
3. **Constants and cosignum.**
   - $`I^{\square(a)} = \bar a`$, so $`\bar 1 = N \bar a`$ and $`S = \bar 1^+`$ are in the
     closure.
   - $`\bar 0^{\square(a)}`$ takes the values $`a, 0, 0, \dots`$. Hence
     $`O = N\,\bar 0^{\square(a)}`$ is the cosignum ($`O(0) = 1`$ and $`O(x+1) = 0`$).
4. **Iteration from $`0`$.** If a predecessor $`\hat P`$ is in the closure, then
   $$F^\square = \hat P^a \,\big(S^a F \hat P^a\big)^{\square(a)}.$$
   Indeed, by induction on $`n`$,
   $`\big(S^a F \hat P^a\big)^{\square(a)}(n) = F^\square(n) + a`$.
   Since $`\hat P^a(y + a) = y`$, the claim follows.

So, once $`\bar 0`$, the multipliers and a predecessor are available, the closure contains
$`\bar 1`$, $`X`$ and $`F^\square`$. It is also closed under $`F^+`$ and composition, so it simulates
$`\langle \bar 1, X, F^+, FG, F^\square\rangle`$. That basis is suitable by Theorem 6.7
($`X = E`$) or Theorem 6.8 ($`X = K`$).

**The constant $`\bar 0`$ for a decreasing $`X`$.** Suppose $`X(0) = 0`$ and $`X(y) < y`$ for
$`y > 0`$. Every value of $`X^{\square(a)}`$ is at most $`a`$. Moreover $`X^k(y) = 0`$ whenever
$`y \le k`$. Hence $`\bar 0 = X^a X^{\square(a)}`$.

#### The case $`X = E`$

- **Zero and multipliers.** $`E(y) < y`$ for $`y > 0`$, so $`\bar 0`$ is in the closure. Take
  $`m(j) = j-1`$: then $`E((j-1)j) = E\big((j-1)^2 + (j-1)\big) = j-1`$.
- **Square test.** By the common part, $`O`$ is in the closure, and so is the characteristic
  function of squares $`Q = O E`$.
- **A predecessor.** Let $`c = a^2 + a + 4`$ and
  $`H = S\,(D Q S^c)^+`$, that is, $`H(y) = 2Q(y + c) + y + 1`$. Let
  $`R(x) = x + 2\lfloor\sqrt{x}\rfloor`$; the step used in §6 gives
  $`R(t+1) = 2Q(R(t) + 4) + R(t) + 1`$.
  - $`B = H^{\square(a)}`$ satisfies $`B(n) + a^2 + a = R(n + a^2)`$, by induction on $`n`$.
  - $`G = (S^{a+1} B)^{\square(a)}`$ satisfies $`G(n) = n^2 + 2an + a`$. For the inductive step
    use $`\lfloor\sqrt{G(n) + a^2}\rfloor = n + a`$, since
    $`G(n) + a^2 = (n+a)^2 + a`$.
  - Let $`d = a^2 - a - 1`$ and $`\hat P = E\,S^d\,G^+`$. Then
    $$\hat P(k+1) = E\big(G(k+1) + (k+1) + d\big) = E\big((k+1+a)^2 + k\big) = k,$$
    so $`\hat P`$ is a predecessor.

#### The case $`X = K`$

- **Zero and multipliers.** $`K(0) = 0`$ and $`K(y) < y`$ for $`y > 0`$, so $`\bar 0`$ is in
  the closure. Take $`m(j) = 2j - 2`$: if $`j = i + 1`$, then $`(2j-2)\,j = A(2i) + i`$, so
  $`K\big((2j-2)j\big) = i = j - 1`$.
- **A predecessor.** Let $`c = A(a)`$ and $`B = \big(S^2 (K S^c)^+\big)^{\square(a)}`$.
  - By induction, $`B(n) + A(a) + 1 = A(n + a + 1)`$. Use $`B(n) + A(a) = A(n+a) + (n+a)`$, so
    $`K(B(n) + A(a)) = n + a`$.
  - Then $`\hat P = K S^c B^+`$ satisfies
    $$\hat P(k+1) = K\big(B(k+1) + (k+1) + A(a)\big) = K\big(A(k+a+2) + k\big) = k.$$

#### The case $`X = L`$

- **Zero.** $`\bar 0 = L\,L^+`$. Indeed, write $`x = A(t) + k`$ with $`k \le t`$. Then
  $`L(x) = t - k`$ and $`x + L(x) = A(t) + t`$, so $`L(x + L(x)) = 0`$.
- **Multipliers.** Take $`m(j) = 2j`$: if $`j = i+1`$, then $`2j \cdot j = A(2i+1) + (i+1)`$,
  so $`L(2j \cdot j) = i = j - 1`$.
- **Reduction to $`K`$.** By the common part, $`\bar 1`$ is in the closure. As in
  Theorem 6.8, $`K = L\,\bar 1^+\big((\bar 1^+)^+ L\big)^+`$, because $`K(x) = L(x + 2L(x) + 2)`$.
  So the closure contains $`K`$ and is closed under the operators of $`\mathcal{B}_a(K)`$,
  which is suitable by the previous case. $`\blacksquare`$

### 2.2 A shifted unary operator instead of the constant $`\bar 1`$

The constant $`\bar 1`$ of Theorem 6.7 cannot simply be dropped. Every function generated by
$`\langle E, F^+, FG, F^\square\rangle`$ fixes $`0`$: $`E(0) = 0`$, and the operators preserve
$`F(0) = 0`$. So $`\bar 1`$ is not generated. Shifting the unary operator fixes this.

> **Theorem.** Let $`F^{+b}(x) = F(x) + x + b`$. The basis
> $`\langle E, F^{+b}, FG, F^\square\rangle`$ is suitable **if and only if $`b \ge 1`$**.

*Proof.* For $`b = 0`$, $`F^{+0} = F^+`$ and every generated function fixes $`0`$, as above.

Now let $`b \ge 1`$. The following functions are in the closure; the powers are powers under
composition.

| Expression | Value |
|---|---|
| $`\bar 0 = E^\square`$ | $`0`$, since $`E(0) = 0`$ |
| $`A = \bar 0^{+b}`$ | $`A(x) = x + b`$ |
| $`C = E\,A^{b-1}\,\bar 0`$ | the constant $`b - 1`$, because $`E((b-1)b) = E((b-1)^2 + (b-1)) = b-1`$ |
| $`B = C^{+b}`$ | $`B(x) = x + 2b - 1`$ |
| $`T = B^{2b-2} A A`$ | $`T(x) = x + 4b^2 - 4b + 2`$ |
| $`G = \big(A^3 (E T)^{+b}\big)^\square`$ | $`G(n) = n^2 + 4bn`$ |
| $`\hat P = E\,A^{4b+1}\big((G^{+b})^{+b}\big)^{+b}`$ | a predecessor |

The two non-obvious values:

- **$`G`$**, by induction on $`n`$. Write $`b = c + 1`$. Then
  $`T(G(n)) = (n + 2c + 1)^2 + (2n + 1)`$, so $`E(T(G(n))) = 2n + 1`$, and
  $$G(n+1) = (2n+1) + G(n) + 4b = (n+1)^2 + 4b(n+1).$$
- **$`\hat P`$** is a predecessor:
  $$\hat P(k+1) = E\big(G(k+1) + 3(k+1) + 3b + (4b+1)b\big) = E\big((k + 2b + 2)^2 + k\big) = k.$$

Finally:
- $`S = \hat P^{b-1} A`$, since $`\hat P^{b-1}(x + 1 + (b-1)) = x + 1`$;
- $`\bar 1 = S\,\bar 0`$;
- $`F^+ = \hat P^b F^{+b}`$, since $`\hat P^b(F(x) + x + b) = F(x) + x`$.

So the closure contains $`\bar 1`$ and $`E`$, and is closed under $`F^+`$, $`F^\square`$ and
composition. It therefore contains the closure of $`\langle \bar 1, E, F^+, FG, F^\square\rangle`$,
which is suitable by Theorem 6.7. $`\blacksquare`$

---

## 3. Problems that remain open

### 3.1 The partial difference $`F - G`$ (Remark 5.11)

In Section 5 the subtraction is a **specific total** function, $`x \mathbin{\dot-} y`$ or
$`\vert x - y\vert`$, defined for all $`x, y`$. Remark 5.11 asks whether a **generic difference**
suffices: $`F - G`$ given by any function $`d(x, y)`$ that equals $`x - y`$ when $`x \ge y`$ and
is arbitrary when $`x < y`$ (footnote 3).

> **Open problem.** Is $`\langle S, F - G, FG, F^\square\rangle`$ suitable for every
> (primitive recursive) difference function $`d`$?

Partial progress:

- The paper notes that it would suffice to obtain $`\mathrm{Sq}`$. Definition by cases then
  becomes
  $`(F \to G) = \mathrm{Hf}\big(\mathrm{Sq}(OF + G) - \mathrm{Sq}(OF) - \mathrm{Sq}\,G\big)`$,
  and table 3 of the paper follows.
- With an arbitrary difference one can still subtract safely whenever the order of the
  arguments is known.
- A comparison works as soon as addition is available:
  $`[F < G] = \mathrm{Sgn}\big(((F - G) + G) - F\big)`$.
- Gated exponentials can be built: $`c \cdot 2^g = 2^{g+c} - 2^g`$ for $`c \in \{0,1\}`$.
- The whole question reduces to one **key lemma**: gate a value $`y`$ by a $`0/1`$ condition
  $`c`$, that is, obtain $`c \cdot y`$. This key lemma is equivalent to obtaining any of:
  - $`\dot-`$;
  - $`\mathrm{Sq}`$;
  - a logarithm on powers of two, $`\Lambda(2^k) = k`$.
- None of these has been obtained for every $`d`$. A barrier argument explains why the standard
  techniques (Gladstone's comparisons, Georgieva's $`\dot-`$-conditionals, Mazzanti's operators)
  do not reach it: they rely on a specific difference function.

### 3.2 General recursive functions with the unary operator $`F^+`$

Julia Robinson (*General recursive functions*, Proc. AMS 1 (1950), §4, Theorem 3) proved:

> $`\mathrm{clos}\langle S, X, F+G, FG, F^{-1}\rangle`$, for $`X \in \{E, K, L\}`$, is the set of
> all unary general recursive functions. Here $`F^{-1}(x) = \mu y\,[F(y) = x]`$, applied to onto
> functions only.

This is the exact analogue of R. M. Robinson's primitive recursive basis, with inversion in place
of iteration. She also showed that $`S`$ can be replaced by the constant $`\bar 1`$.

> **Open problem.** Can the binary operator $`F + G`$ be replaced by the unary operator
> $`F^+(x) = F(x) + x`$, as Section 6 of the paper does for primitive recursion? That is, is
> $`\mathrm{clos}\langle \bar 1, X, F^+, FG, F^{-1}\rangle`$ ($`X \in \{E, K, L\}`$) the set of
> unary general recursive functions? One may also ask whether the constant can be dropped, as in
> Remark 6.9 and §2.2.

The techniques of Section 6 do not transfer directly. Lemmas 6.2–6.6 rebuild $`F + G`$ from
$`F^+`$ using iteration in an essential way: $`\mathrm{Sq}`$, $`\mathrm{Hf}`$ and $`\mathrm{Rt}`$
all come from $`F^\square`$. In the general recursive setting only inversion is available, and it
can only be applied to onto functions, so those constructions would have to be redone.

---

## 4. The formalizations

All four formalize **Section 6**:

- Definition 6.1;
- Lemmas 6.2–6.6;
- Theorem 6.7, and Lemma 3.3 where it is used;
- Theorem 6.8;
- Remark 6.9.

They use the same names wherever the language allows:
- a function X of the paper is `funX` (`funS`, `funE`, `funRt`, `funK`, …), and `cst n` is the
  constant n̄;
- an operator is `opX` (`opPlusI` for F⁺, `opBox` for F^□, `opBoxA a` for F^□(a), …);
- when the paper defines `X ≡ expression`, `exprX` is the expression, built only with the
  operators of the basis. Lemmas `X_expr` / `exprX_val` (`XExpr` / `…Val` in Mizar) state that
  it computes X, and `X_in` (`XIn`) that it lies in the closure.

### 4.1 Requirements and installation

Each folder has its own README with detailed instructions.

| | Requirements | Install and check |
|---|---|---|
| [Isabelle/HOL](isabelle/README.md) | [Isabelle2025-2](https://isabelle.in.tum.de) and the AFP entry *Recursion Theory I* from the [AFP](https://www.isa-afp.org/download/) release for Isabelle2025-2 | `AFP=/path/to/afp/thys isabelle/build.sh` (or copy the entry into `isabelle/afp/`); `isabelle/jedit.sh` opens the IDE |
| [Mizar](mizar/README.md) | [Mizar 8.1.15 with MML 5.94.1493](https://mizar.uwb.edu.pl/system/), Python 3 | run the package's `install.sh`, set `MIZFILES`, put the binaries on `PATH`; then `mizar/miz.sh uprf` |
| [Lean 4](lean/README.md) | [elan](https://github.com/leanprover/elan) (it installs Lean 4.34.1); Mathlib v4.34.1 is fetched by `lake` | `cd lean && lake exe cache get && ./build.sh` |
| [Rocq](rocq/README.md) | [Rocq 9.3](https://rocq-prover.org), MathComp 2.6 (`rocq-mathcomp-ssreflect`), mczify (`coq-mathcomp-zify`), installed with [opam](https://opam.ocaml.org) | `opam repo add rocq-released https://rocq-prover.org/opam/released`; `opam install rocq-prover rocq-mathcomp-ssreflect coq-mathcomp-zify`; `rocq/build.sh` |

### 4.2 How to read them

A good reading order is:

1. the definitions of the functions and of the closure;
2. the `*_in` lemmas of Section 6, which mirror the table of formulas in the paper;
3. the `*_val` lemmas, which are the arithmetic behind each formula;
4. the final theorems.

| | Isabelle/HOL | Mizar | Lean 4 + Mathlib | Rocq + MathComp |
|---|---|---|---|---|
| Sources | `isabelle/UPRF/*.thy` | `mizar/text/uprf.miz` | `lean/UPRF/*.lean` | `rocq/theories/*.v` |
| Start with | `UPRF_Sec2_Notation.thy`, `UPRF_Sec6.thy` | the table in `mizar/README.md` | `Basic.lean`, `Sec6.lean` | `Basic.v`, `Sec6.v` |
| Main theorems | `Theorem_6_7`, `Theorem_6_8`, `Remark_6_9_I/II/III`, `Robinson_1947_sec7_thm3`, `Ext_a_all`, `Ext_Vb_iff` | `Theorem67`, `Theorem68`, `Remark69`, `ExtA`, `ExtVbIff` | `Theorem_6_7`, `Theorem_6_8`, `Remark_6_9_I/II/III`, `Robinson_1947_sec7_thm3`, `Ext_a_all`, `Ext_Vb_iff` | same names as Lean |
| Prim(ℕ,ℕ) | AFP `PrimRec1` | not connected | Mathlib `Nat.Primrec` | own inductive `PrimNN` (unary Cantor characterization) |

### 4.3 Comparison

Line counts cover Sections 2–6, including Robinson's theorem where it is proved (comments
included). The extensions of §2 add 675 more lines in Isabelle, 1 505 in Mizar, 511 in Lean
and 513 in Rocq.

| | Isabelle/HOL | Mizar | Lean 4 | Rocq |
|---|---|---|---|---|
| Lines | 2 011 (1 710 without Robinson; 84 are proof methods) | 4 094 | 1 405 (97 are proof automation) | 1 556 (160 are proof automation) |
| Check time from clean | ~15 s (after the AFP session) | ~11 s | ~95 s (loading Mathlib and proof search) | ~35 s |
| What is proved | everything; `suitable` means equal to Prim | everything **at closure level**: every basis generates the same closure as Robinson's ⟨S, E, F + G, FG, F^□⟩; Robinson's theorem itself is not proved | everything; `suitable` means equal to Prim | everything; `suitable` means equal to Prim |
| Robinson's theorem | proved, using the AFP characterization `PrimRec1'` | missing | proved against Mathlib's `Nat.Primrec` (Szudzik pairing) | proved against its own `PrimNN` (Cantor pairing) |
| Soundness (closure ⊆ Prim) | AFP `prec` tactic | not applicable | Mathlib `Primrec` API (`nat_iterate`, `nat_sqrt`, …) | bootstrapped by hand in `Prim.v` (+, ∸, ×, =, √, E, Hf, iteration) |
| Axioms | HOL | Tarski–Grothendieck set theory | `propext`, `Classical.choice`, `Quot.sound` | functional extensionality only |
| Arithmetic automation | `simp`, `algebra_simps`, `presburger`, `arith` | none beyond the checker's polynomial normalization; every inequality step needs a library lemma | `omega`, `nlinarith`, `ring`, `simp` | `lia`, `nia` (through mczify) |

### 4.4 Findings

- **Library support decides the size of the Robinson part.**
  - Isabelle (the AFP's `PrimRec1'`) and Lean (Mathlib's `Nat.Primrec`) both provide a
    *unary* characterization of the primitive recursive functions. With it, Robinson's theorem
    is an induction with seven cases.
  - Mizar's MML only has n-ary partial functions on tuples (`COMPUT_1`). That is why the Mizar
    version stops at closure level.
  - Rocq has nothing, so Prim(ℕ,ℕ) is defined there by the same unary characterization, and
    soundness is bootstrapped by hand.
- **The pairing function matters.**
  - Mathlib uses Szudzik's `Nat.pair`, whose `unpair` needs a case split. The Lean proof
    therefore builds three things inside the closure, using only Lemmas 6.2–6.6:
    - a comparison indicator, with the difference function of Lemma 6.6;
    - general truncated subtraction;
    - definition by cases.
  - With Cantor's pairing (Isabelle, Rocq) the triangle walk needs only the difference of
    Lemma 6.6. That difference is correct below the diagonal, and the walk never leaves it.
- **Proof automation.** Closure membership, soundness and simulation recur in every theorem.
  Three provers capture them with their own extension mechanisms:

  | Prover | Mechanism | Tactics |
  |---|---|---|
  | Rocq | Ltac2 (`Tactics.v`) | `clos_solve`, `sound`, `simulate` |
  | Isabelle | Eisbach methods with named theorems (`UPRF_Methods.thy`) | `clos_solve`, `clos_sound_m`, `clos_subset_m`, `simulate` |
  | Lean | tactic macros, extensible through `macro_rules` (`Tactics.lean`) | `clos_solve`, `prim_sound`, `simulate` |

  In all three, most membership lemmas and every suitability theorem of 6.8 and 6.9 became one
  line. The refactored files lost about 125 lines (Rocq), 160 lines (Isabelle) and 80 lines
  (Lean) of proof. One design point mattered in all three: decomposing a function **by its
  syntactic head**, never by unification modulo definitions. The Rocq version compares terms
  syntactically, Lean uses reducible transparency, and Isabelle uses one rule per operator.
  Without it, unification unfolds √ and the Cantor functions and can hang. Mizar has no
  user-definable tactics.
- **Closures as inductive predicates** (Lean, Rocq) give structural induction for free.
  Isabelle and Mizar define the closure as an intersection of closed sets and prove the
  induction principle (Isabelle) or work with "least closed set" arguments (Mizar).
- **The paper's proofs are mostly arithmetic.** Each formula `X ≡ …` hides a polynomial
  identity with truncated subtraction. Provers with a decision procedure for linear integer
  arithmetic plus a nonlinear heuristic (`omega`/`nlinarith`, `lia`/`nia`, `presburger`) prove
  most of them in one line. Mizar needs each step spelled out: an inference may not mix a
  definition expansion with arithmetic, and numerals block instantiation. Mostly for that
  reason it is about 2–3× longer.
- **Remark 6.9 hides one use of soundness.** At closure level (Mizar), Remark 6.9 needs
  F^□(1) in the closure, and Theorem 6.8 needs K and L there. Both were proved directly, using
  a general product built from Lemma 6.6. The other provers get these memberships from
  Robinson's theorem.
- **Pitfalls specific to each prover.** They are listed in each folder's README, for example:
  - Lean's and Rocq's `∘` associate in opposite directions;
  - ssreflect's `//` and `/=` try to compute √ and the Cantor functions and hang;
  - Mizar can cite other articles' theorems only by number, so its formalization is a single
    file.

---

## License

MIT (see [LICENSE](LICENSE)). The papers summarized in `references/` and `others/` are
copyrighted by their publishers and are not included.
