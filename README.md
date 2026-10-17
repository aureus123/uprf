# Unary primitive recursive functions (UPRF)

This repository accompanies D. E. Severin, *Unary primitive recursive functions*,
J. Symbolic Logic 73(4) (2008), 1122–1138 ([arXiv:cs/0603063](https://arxiv.org/abs/cs/0603063)).

It contains:

- the paper's results;
- the questions it leaves open, with the ones answered here;
- the problems that are still open;
- machine-checked formalizations of Section 6 and of the answered questions (§2.1–2.3) in five
  proof assistants: Isabelle/HOL, Mizar, Lean 4, Rocq and Z/EVES.

| Folder | Content |
|---|---|
| [`references/`](references/README.md) | summaries of the papers cited by the UPRF paper |
| [`others/`](others/README.md) | summaries of further papers on restricted recursion schemes (Péter, Kleene, Axt, Calude, Georgieva, Mazzanti, …) |
| [`isabelle/`](isabelle/README.md), [`mizar/`](mizar/README.md), [`lean/`](lean/README.md), [`rocq/`](rocq/README.md), [`z/`](z/README.md) | the formalizations |

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

The results of §2.1, §2.2 and §2.3 (with its remarks) are formalized in all five proof
assistants, and their proofs below follow the Isabelle formalization:

| | §2.1 (iteration from a) | §2.2 (shifted operator) | §2.3 (general recursive functions) |
|---|---|---|---|
| Isabelle/HOL | `isabelle/UPRF/UPRF_Ext_a.thy`: `Ext_a_all` | `isabelle/UPRF/UPRF_Ext_Vb.thy`: `Ext_Vb_iff` | `isabelle/UPRF/UPRF_Ext_GR.thy`: `Ext_GR`, `Ext_GR0`, `Ext_GRS`; `UPRF_Ext_GRb.thy`: `Ext_GRb_iff`; `UPRF_Ext_Cn.thy`: `Ext_Cn_suitable`, `Ext_GRCn` |
| Lean 4 | `lean/UPRF/ExtA.lean`: `Ext_a_all` | `lean/UPRF/ExtVb.lean`: `Ext_Vb_iff` | `lean/UPRF/ExtGR.lean`: `Ext_GR`, `Ext_GR0`, `Ext_GRS`; `ExtGRb.lean`: `Ext_GRb_iff`; `ExtCn.lean`: `Ext_Cn_suitable`, `Ext_GRCn` |
| Rocq | `rocq/theories/ExtA.v`: `Ext_a_all` | `rocq/theories/ExtVb.v`: `Ext_Vb_iff` | `rocq/theories/ExtGR.v`: `Ext_GR`, `Ext_GR0`, `Ext_GRS`; `ExtGRb.v`: `Ext_GRb_iff`; `ExtCn.v`: `Ext_Cn_suitable`, `Ext_GRCn` |
| Mizar | `mizar/text/uprf.miz`: `ExtA` | `mizar/text/uprf.miz`: `ExtVbIff` | `mizar/text/uprf.miz`: `GREqJR`, `GR0Neq`, `GRSEq`, `GRbIff`, `CnBox`, `CnInv` |
| Z/EVES | `z/uprf.tex`: `ExtAAll` | `z/uprf.tex`: `ExtVbIff` | `z/uprf.tex`: `GREqJR`, `ExtGR0`, `GRSEq`, `ExtGRbIff`, `CnBox`, `CnInv` |

As for Section 6, Mizar and Z/EVES state them at closure level:
- for $`a \ge 1`$ the bases generate the same closure as
  $`\langle \bar 1, E, F^+, FG, F^\square\rangle`$;
- the shifted basis does so if and only if $`b \ge 1`$;
- for §2.3, the bases with inversion generate the same closure as J. Robinson's
  $`\langle S, E, F+G, FG, F^{-1}\rangle`$.

J. Robinson's theorem itself (that this closure is the set of unary general recursive
functions) is not formalized anywhere. Isabelle, Lean and Rocq take it as a hypothesis
`Robinson_1950_sec4_thm3` of the final §2.3 theorems.

**Conventions used in the proofs:**
- $`F^k`$ denotes the $`k`$-fold composition $`F \circ \dots \circ F`$.
- A *predecessor* is any function $`\hat P`$ with $`\hat P(x+1) = x`$ for all $`x`$.
- Two arithmetic facts are used repeatedly:
  - $`E(m^2 + k) = k`$ whenever $`k \le 2m`$;
  - $`K(A(t)+k) = k`$ and $`L(A(t)+k) = t-k`$ whenever $`k \le t`$.
- *Soundness* is never an issue: every function and operator involved is primitive recursive
  (general recursive in §2.3). Each proof therefore only shows that the basis of Theorem 6.7
  (or 6.8, or Theorem 1 of §2.3) is simulated.

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

### 2.3 General recursive functions with the unary operator $`F^+`$

Julia Robinson (*General recursive functions*, Proc. AMS 1 (1950), §4, Theorem 3) proved the
analogue of R. M. Robinson's primitive recursive basis, with inversion in place of iteration:

> $`\mathrm{clos}\langle S, X, F+G, FG, F^{-1}\rangle`$, for $`X \in \{E, K, L\}`$, is the set
> $`\mathrm{GR}`$ of all unary general recursive functions.

Here $`F^{-1}(x) = \mu y\,[F(y) = x]`$, applied to onto functions only. Two facts about it
are used throughout:
- $`F F^{-1} = I`$, that is, $`F^{-1}(x)`$ is *a* preimage of $`x`$;
- $`F^{-1}(x)`$ is the *least* preimage of $`x`$.

Most constructions below only need the first fact. The question is whether $`F + G`$ can be
replaced by $`F^+`$, as Section 6 does for primitive recursion. Lemmas 6.2–6.6 of the paper
cannot be reused as they stand, because $`\mathrm{Sq}`$, $`\mathrm{Hf}`$ and $`\mathrm{Rt}`$
come from $`F^\square`$ there.

> **Theorem 1.** For $`X \in \{E, K, L\}`$,
> $`\mathrm{clos}\langle \bar 1, X, F^+, FG, F^{-1}\rangle = \mathrm{GR}`$.

*Proof.* The operators $`F^+`$, $`FG`$ and $`F^{-1}`$ (on onto functions) preserve general
recursiveness, so the closure is contained in $`\mathrm{GR}`$.

For the converse, look at what Lemmas 6.2–6.6 actually use. Their formulas build $`F + G`$ from
$`F^+`$ and composition, using only the functions
$`E, S, D, M_3, \mathrm{Sq}, \mathrm{Hf}, \mathrm{Rt}`$ and the predecessor $`\hat P`$ of
Lemma 6.5. Iteration enters only through the
construction of these functions. So it is enough to obtain $`E`$, $`\mathrm{Sq}`$,
$`\mathrm{Hf}`$ and $`\mathrm{Rt}`$ with inversion. The closure is then closed under
$`F + G`$, contains $`S = \bar 1^+`$ and $`E`$, and so contains J. Robinson's closure.

Write $`A(t) = t(t+1)/2`$, let $`V(y)`$ be the triangular root, so that $`y = A(V(y)) + K(y)`$
with $`K(y) \le V(y)`$, and let $`I - F`$ denote $`x \mapsto x - F(x)`$.

**The case $`X = E`$.** First, $`S = \bar 1^+`$, $`\bar 0 = E\bar 1`$, $`I = \bar 0^+`$,
$`D = I^+`$, $`M_3 = D^+`$ and $`M_4 = M_3^+`$. Then:

| Expression | Value |
|---|---|
| $`E^{-1}`$ | $`\lceil x/2\rceil^2 + x`$, so $`E^{-1}(2z) = z^2 + 2z`$ |
| $`F^- \equiv E\,(SSS\,M_3 F E)^+\,S\,(E^{-1} D F^+)^+`$ | $`F(x) - x`$, if $`F(x) \ge x`$ |
| $`\mathrm{Sq} \equiv ((E^{-1}D)^-)^-`$ | $`x^2`$ |
| $`I - F \equiv E\,(S (F^+)^+ E)^+ (\mathrm{Sq}\,F^+)^+`$ | $`x - F(x)`$, if $`F(x) \le x`$ |
| $`W \equiv E\,(SSDEE)^+ E^{-1}`$ | $`2E(y) + [y \text{ even}]`$ |
| $`\mathrm{Hf} \equiv E\,W^{-1}`$ | $`\lfloor x/2\rfloor`$ |
| $`\mathrm{Rt} \equiv \mathrm{Hf}\,\mathrm{Hf}\,SS\,E\,(I - \bar 1)(I - E)\,S\,M_4`$ | $`\lfloor\sqrt x\rfloor`$ |

- **$`F^-`$.** Let $`s = F(x) + x`$. The inner function gives $`(s+1)^2 + x`$, so $`E`$ recovers
  $`x`$ from it. Adding $`3F(x) + 3`$ gives $`(s+2)^2 + (F(x) - x)`$, and $`E`$ of this is
  $`F(x) - x`$.
- **$`I - F`$** is Robinson's formula $`E\big((x + F(x))^2 + 3x + F(x) + 1\big) = x - F(x)`$.
  The sum is built in the same way: $`E`$ recovers $`x`$ from $`(x + F(x))^2 + x`$.
- **$`W`$** is the function that J. Robinson inverts in her §3. She builds it with $`+`$; here it
  comes from $`F^+`$. Let $`c = \lceil y/2\rceil`$. Then $`E^{-1}(y) = c^2 + y`$ and $`E`$ of it is
  $`y`$, so
  $$W(y) = E\big(c^2 + y + 2E(y) + 2\big) = E\big((c+1)^2 + 2E(y) + 1 + y - 2c\big).$$
  Since $`2E(y) \le y + 1`$, the offset is at most $`2(c+1)`$. So
  $`W(y) = 2E(y) + 1 + y - 2c = 2E(y) + [y \text{ even}]`$.
- **$`\mathrm{Hf}`$.** $`W`$ is onto, and every $`y`$ with $`W(y) = x`$ has
  $`E(y) = \lfloor x/2\rfloor`$.
- **$`\mathrm{Rt}`$.** Let $`n = \lfloor\sqrt{4x+1}\rfloor \ge 1`$. Then
  $`(I - E)(4x+1) = n^2`$ and $`E(n^2 - 1) = 2(n-1)`$, so $`\mathrm{Hf}\,SS`$ gives $`n`$. Finally
  $`\lfloor n/2\rfloor = \lfloor\sqrt x\rfloor`$, because
  $`2\lfloor\sqrt x\rfloor \le n \le 2\lfloor\sqrt x\rfloor + 1`$. Using $`4x + 1`$ instead of $`x`$
  avoids the root $`0`$, where $`I - \bar 1`$ is not a predecessor.

The predecessor $`\hat P`$ of Lemma 6.5 only needs $`\mathrm{Sq}`$ and Lemma 6.4. So all the
ingredients of Lemmas 6.2–6.6 are in the closure.

**The case $`X = K`$.** Again $`S = \bar 1^+`$, $`\bar 0 = K\bar 1`$, $`I`$, $`D`$ and $`M_3`$
are in the closure. Then:

| Expression | Value |
|---|---|
| $`Z = K^{-1}`$ | $`A(x) + x`$ |
| $`I - F \equiv K\,SSS\,((Z F^+)^+)^+`$ | $`x - F(x)`$, if $`F(x) \le x`$ (proof of Theorem 6.8) |
| $`A \equiv K\,SSS\,(Y K)^+ Z`$, with $`Y \equiv (Z Z^+ K)^+ Z`$ | $`A(x)`$ |
| $`F^- \equiv K\,(SSS\,M_3 F K)^+ (A F^+)^+`$ | $`F(x) - x`$, if $`F(x) \ge x`$ |
| $`\mathrm{Sq} \equiv (((DZ)^-)^-)^-`$ | $`x^2 = 2Z(x) - 3x`$ |
| $`P \equiv K\,(KS)^{-1}`$ | $`x \mathbin{\dot-} 1`$ |
| $`U \equiv I - A K P (I - K)`$ | $`V(y) + K(y)`$ |
| $`\mathrm{Hf} \equiv K\,U^{-1}`$ | $`\lfloor x/2\rfloor`$ |
| $`B \equiv I - \big(I - \mathrm{Sq}\,(I - \mathrm{Hf})\,U\big)(I - K)`$ | $`K(y) + \lceil V(y)/2\rceil^2`$ |
| $`E \equiv K\,B^{-1}`$ | $`E(x)`$ |

- **$`A`$.** This is Robinson's difference $`K\big(Z(\alpha+\beta) + 2\alpha + 3\big) = \alpha - \beta`$
  with $`\alpha = Z(x)`$ and $`\beta = x`$. The sums with $`Z(x)`$ are formed as in
  $`F + Z = (F K)^+ Z`$, which works because $`K`$ is a left inverse of $`Z`$.
- **$`F^-`$.** Let $`s = F(x) + x`$. The inner function gives $`A(s) + x`$, from which $`K`$
  recovers $`x`$. The total is $`A(s+2) + (F(x) - x)`$.
- **$`U`$.** Write $`y = A(t) + k`$. Then $`(I - K)(y) = A(t)`$, and $`K P(A(t)) = t \mathbin{\dot-} 1`$.
  So $`U(y) = y - A(t-1) = t + k`$ for $`t \ge 1`$, and $`U(0) = 0`$. Also $`U(A(t)) = t`$.
- **$`\mathrm{Hf}`$** uses minimality. The least $`y = A(t) + k`$ with $`t + k = x`$ and
  $`k \le t`$ has $`t = \lceil x/2\rceil`$, so $`k = \lfloor x/2\rfloor`$.
- **$`B`$.** At $`A(t)`$ the inner function is $`A(t) - \lceil t/2\rceil^2`$, so
  $`B(y) = k + \lceil t/2\rceil^2`$.
- **$`E`$.** $`B`$ is onto: take $`t = 2\lfloor\sqrt x\rfloor`$ and $`k = E(x)`$. If $`B(y) = x`$
  and $`c = \lceil t/2\rceil`$, then $`x = c^2 + k`$ with $`k \le t \le 2c`$, so $`E(x) = k = K(y)`$.

So $`E`$ is in the closure, and the case $`X = E`$ applies.

**The case $`X = L`$.** As in Theorem 6.8, $`K = L\,\bar 1^+\big((\bar 1^+)^+ L\big)^+`$, and the
case $`X = K`$ applies. $`\blacksquare`$

**Remark** ($`\bar 1`$ and $`S`$ are interchangeable). The basis of Theorem 1 may contain $`S`$
instead of $`\bar 1`$, as J. Robinson's does.
- One direction is immediate: $`S = \bar 1^+`$.
- Conversely, $`\bar 1 = S\,\bar 0`$, and $`\bar 0`$ is obtained from $`S`$, $`X`$, composition and
  inversion alone:

  | $`X`$ | $`\bar 0`$ | Why |
  |---|---|---|
  | $`K`$ | $`K\,S\,K^{-1}`$ | $`K^{-1}(x) + 1 = A(x) + x + 1 = A(x+1)`$, a triangular number |
  | $`E`$ | $`(E\,S\,E^{-1})^2`$ | $`f = E\,S\,E^{-1}`$ maps $`2j`$ to $`E((j+1)^2) = 0`$ and $`2j+1`$ to $`E((j+1)^2 + 2j + 2) = 2j + 2`$; so $`f(x)`$ is even and $`f(f(x)) = 0`$ |
  | $`L`$ | $`L\,(LS)^{-1}\,S`$ | for $`x \ge 1`$ the least $`y`$ with $`L(y+1) = x`$ is $`A(x) - 1 = A(x-1) + (x-1)`$, and $`L`$ of it is $`0`$ |

  The first line is J. Robinson's $`O = K S K^{-1}`$. With $`F^+`$ available, $`E`$ also has
  her shorter $`\bar 0 = E\,S\,E^{-1} I^+`$, since $`E^{-1}(2x) + 1 = (x+1)^2`$.

**Remark** (any constant $`\bar n`$ with $`n \ge 1`$). The constant $`\bar 1`$ can be replaced
by any $`\bar n`$ with $`n \ge 1`$, both here and in Section 6:
- $`\langle \bar n, X, F^+, FG, F^\square\rangle`$ is suitable;
- $`\mathrm{clos}\langle \bar n, X, F^+, FG, F^{-1}\rangle = \mathrm{GR}`$.

For $`n = 0`$ both fail, because every generated function fixes $`0`$.

The argument uses only $`F^+`$, composition and $`X`$, so it does not depend on iteration or
inversion. Since $`\bar n^+(x) = x + n`$, every constant $`c + kn`$ is generated from a
constant $`c`$. Then $`X`$ steps down from $`c \ge 1`$ to $`c - 1`$:

| $`X`$ | Step |
|---|---|
| $`E`$ | $`c + kn = (nc+1)^2 + (c-1)`$ for $`k = nc^2 + 2c`$, and $`E`$ of it is $`c - 1`$ |
| $`K`$ | $`c + kn = A(2nc+1) + (c-1)`$ for $`k = 2nc^2 + 3c`$, and $`K`$ of it is $`c - 1`$ |
| $`L`$ | two steps, $`c \mapsto nc - c \mapsto c - 1`$, since $`c + n(2nc^2 + 2c) = A(2nc) + (nc + c)`$ and $`(nc - c) + n \cdot 2nc^2 = A(2nc - 1) + (2nc - c)`$ |

For $`L`$ a single step is not always possible, because triangular numbers miss some residues
modulo $`n`$.

Starting from $`c = n`$, the steps reach $`\bar 1`$. So the closure contains the basis with
$`\bar 1`$. Conversely, $`\bar n = (\bar 1^+)^{n-1}\,\bar 1`$ is in the closure of the basis with
$`\bar 1`$.

**The constant cannot be dropped.** In $`\langle X, F^+, FG, F^{-1}\rangle`$ every function fixes
$`0`$. Indeed $`X(0) = 0`$ and $`F^+(0) = F(0)`$, and if $`F(0) = 0`$ then also
$`F^{-1}(0) = 0`$. So $`\bar 1`$ is not generated. As in §2.2, shifting the operator fixes this.

> **Theorem 2.** Let $`F^{+b}(x) = F(x) + x + b`$. For $`X \in \{E, K, L\}`$,
> $`\mathrm{clos}\langle X, F^{+b}, FG, F^{-1}\rangle = \mathrm{GR}`$ **if and only if
> $`b \ge 1`$**.

*Proof.* The closure is contained in $`\mathrm{GR}`$, and for $`b = 0`$ it misses $`\bar 1`$.

Let $`b \ge 1`$. It is enough to obtain $`S`$. Then a predecessor $`\hat P`$ gives
$`F^+ = \hat P^b F^{+b}`$, and a constant $`\bar 0`$ gives $`\bar 1 = S\bar 0`$:

| $`X`$ | $`\hat P`$ | $`\bar 0`$ |
|---|---|---|
| $`E`$ | $`E\,(ES)^{-1}`$ | $`E\,S\,E^{-1} D`$, with $`D = I^+`$ |
| $`K`$ | $`K\,(KS)^{-1}`$ | $`K A`$, with $`A`$ as in Theorem 1 |
| $`L`$ | $`L\,S\,L^{-1}`$ | $`L\,(L^{-1})^+`$ |

The closure then contains $`\langle \bar 1, X, F^+, FG, F^{-1}\rangle`$, and Theorem 1 applies.

Two tools are used to obtain $`S`$:
- $`I = X X^{-1}`$ and $`T = I^{+b}`$, so that $`T(x) = 2x + b`$;
- **subtraction by inversion.** If $`V(x) = x + c`$ is in the closure and $`X \in \{E, K\}`$,
  then $`X\,(XV)^{-1}(x) = x - c`$ for $`x \ge c`$. Indeed, if $`E(y + c) = x`$ then
  $`y + c = m^2 + x`$ with $`x \le 2m`$, so $`E(y) = E\big(m^2 + (x - c)\big) = x - c`$. The same
  argument works with $`A(t)`$ and $`K`$. Any preimage works here, not only the least one.

**$`S`$ for $`X = E`$, $`b \ge 2`$.** Note that $`E^{-1}(2m) = (m+1)^2 - 1`$ and
$`E^{-1}(2m+1) = (m+2)^2 - 2`$. So, for $`m`$ large enough compared with $`x + b`$,
$$E\big((E^{-1} G)^{+b}\big)(x) = \begin{cases} x + b - 1 & \text{if } G(x) = 2m, \\ x + b - 2 & \text{if } G(x) = 2m + 1. \end{cases}$$
- $`G = T`$ has the parity of $`b`$ and gives one of the two shifts, $`U`$.
- $`G = U\,T`$ has the other parity and gives the other shift.

Call the shifts $`U_1(x) = x + b - 1`$ and $`U_2(x) = x + b - 2`$. Then
$`S = E\,(E U_2)^{-1}\,U_1`$.

**$`S`$ for $`X = E`$, $`b = 1`$.**
- $`\hat P = E\,(E^{-1}T)^{+1}`$ is a predecessor: $`E^{-1}(2x+1) + x + 1 = (x+2)^2 + (x-1)`$. Also
  $`\hat P(0) = 2`$.
- $`D = \hat P T`$ doubles.
- $`S = E\,\hat P^{-1}(E^{-1}D)^{+1}`$. Indeed $`(E^{-1}D)^{+1}(x) = x^2 + 3x + 1 \ne 2`$, its
  $`\hat P`$-preimage is $`x^2 + 3x + 2 = (x+1)^2 + (x+1)`$, and $`E`$ of that is $`x + 1`$.

**$`S`$ for $`X = K`$, $`b \ge 2`$.** Let $`Z = K^{-1}`$.
- $`U = K\,(ZT)^{+b}`$ gives $`U(x) = x + b - 1`$, because
  $`Z(2x+b) + x + b = A(2x + b + 1) + (x + b - 1)`$.
- $`P_1 = K\,(KU)^{-1}`$ subtracts $`b - 1`$.
- $`C = K\,(Z P_1)^{+b}\,U^3`$ is the constant $`2b - 4`$. With $`g = x + 2b - 2`$, the argument of
  $`K`$ is $`A(g) + g + (g + b - 1) + b = A(g+2) + 2b - 4`$.
- $`C^{+b}(x) = x + 3b - 4`$. Subtracting $`3b - 4`$ by inversion gives
  $`S = K\,(K C^{+b})^{-1}\,U^3`$.

**$`S`$ for $`X = K`$, $`b = 1`$.**
- $`\hat P = K\,(Z^{+1})^{+1}`$ is a predecessor: $`Z(x) + 2x + 2 = A(x+2) + (x - 1)`$. Also
  $`\hat P(0) = 1`$.
- $`S = K\,\hat P^{-1}(ZT)^{+1}`$. Indeed $`(ZT)^{+1}(x) = A(2x+2) + x \ge 3`$, its
  $`\hat P`$-preimage is $`A(2x+2) + x + 1`$, and $`K`$ of that is $`x + 1`$.

**$`S`$ for $`X = L`$, any $`b \ge 1`$.** Here $`L^{-1} = A`$. Applying the operator $`n`$ times
to $`A`$ gives $`A(x) + n(x + b)`$.
- For $`n = 2b - 2`$ this is $`A(x + 2b - 2) + (b - 1)`$, since
  $`(2b-2)\,b - A(2b-2) = b - 1`$. So $`L`$ of it is $`U(x) = x + b - 1`$.
- For $`n = 1`$ it is $`A(y) + y + b = A(y + 1) + (b - 1)`$. So $`L\,A^{+b}(y) = y + 2 - b`$ for
  $`y \ge b - 2`$.

Hence $`S = L\,A^{+b}\,U`$. $`\blacksquare`$

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

---

## 4. The formalizations

All five formalize **Section 6**:

- Definition 6.1;
- Lemmas 6.2–6.6;
- Theorem 6.7, and Lemma 3.3 where it is used;
- Theorem 6.8;
- Remark 6.9;

and the solved problems of §2 (§2.1, §2.2 and §2.3; see the table at the start of §2).

They use the same names wherever the language allows:
- a function X of the paper is `funX` (`funS`, `funE`, `funRt`, `funK`, …), and `cst n` is the
  constant n̄;
- an operator is `opX` (`opPlusI` for F⁺, `opBox` for F^□, `opBoxA a` for F^□(a), …);
- when the paper defines `X ≡ expression`, `exprX` is the expression, built only with the
  operators of the basis. Lemmas `X_expr` / `exprX_val` (`XExpr` / `…Val` in Mizar and Z/EVES)
  state that it computes X, and `X_in` (`XIn`) that it lies in the closure.

### 4.1 Requirements and installation

Each folder has its own README with detailed instructions.

| | Requirements | Install and check |
|---|---|---|
| [Isabelle/HOL](isabelle/README.md) | [Isabelle2025-2](https://isabelle.in.tum.de) and the AFP entry *Recursion Theory I* from the [AFP](https://www.isa-afp.org/download/) release for Isabelle2025-2 | `AFP=/path/to/afp/thys isabelle/build.sh` (or copy the entry into `isabelle/afp/`); `isabelle/jedit.sh` opens the IDE |
| [Mizar](mizar/README.md) | [Mizar 8.1.15 with MML 5.94.1493](https://mizar.uwb.edu.pl/system/), Python 3 | run the package's `install.sh`, set `MIZFILES`, put the binaries on `PATH`; then `mizar/miz.sh uprf` |
| [Lean 4](lean/README.md) | [elan](https://github.com/leanprover/elan) (it installs Lean 4.34.1); Mathlib v4.34.1 is fetched by `lake` | `cd lean && lake exe cache get && ./build.sh` |
| [Rocq](rocq/README.md) | [Rocq 9.3](https://rocq-prover.org), MathComp 2.6 (`rocq-mathcomp-ssreflect`), mczify (`coq-mathcomp-zify`), installed with [opam](https://opam.ocaml.org) | `opam repo add rocq-released https://rocq-prover.org/opam/released`; `opam install rocq-prover rocq-mathcomp-ssreflect coq-mathcomp-zify`; `rocq/build.sh` |
| [Z/EVES](z/README.md) | [Z/EVES 2.3](https://github.com/arandilopez/z-eves) (32-bit Linux only; on macOS inside a [Lima](https://lima-vm.io) VM) | unpack into `/opt/Z/Z-Eves`; on macOS `limactl start zeves`; then `z/zeves.sh z/uprf.tex` |

### 4.2 How to read them

A good reading order is:

1. the definitions of the functions and of the closure;
2. the `*_in` lemmas of Section 6, which mirror the table of formulas in the paper;
3. the `*_val` lemmas, which are the arithmetic behind each formula;
4. the final theorems.

| | Isabelle/HOL | Mizar | Lean 4 + Mathlib | Rocq + MathComp | Z/EVES |
|---|---|---|---|---|---|
| Sources | `isabelle/UPRF/*.thy` | `mizar/text/uprf.miz` | `lean/UPRF/*.lean` | `rocq/theories/*.v` | `z/uprf.tex` |
| Start with | `UPRF_Sec2_Notation.thy`, `UPRF_Sec6.thy` | the table in `mizar/README.md` | `Basic.lean`, `Sec6.lean` | `Basic.v`, `Sec6.v` | the table in `z/README.md` |
| Main theorems | `Theorem_6_7`, `Theorem_6_8`, `Remark_6_9_I/II/III`, `Robinson_1947_sec7_thm3`, `Ext_a_all`, `Ext_Vb_iff`, `Ext_GR`, `Ext_GR0`, `Ext_GRS`, `Ext_GRb_iff`, `Ext_Cn_suitable`, `Ext_GRCn` | `Theorem67`, `Theorem68`, `Remark69`, `ExtA`, `ExtVbIff`, `GREqJR`, `GR0Neq`, `GRSEq`, `GRbIff`, `CnBox`, `CnInv` | `Theorem_6_7`, `Theorem_6_8`, `Remark_6_9_I/II/III`, `Robinson_1947_sec7_thm3`, `Ext_a_all`, `Ext_Vb_iff`, `Ext_GR`, `Ext_GR0`, `Ext_GRS`, `Ext_GRb_iff`, `Ext_Cn_suitable`, `Ext_GRCn` | same names as Lean | `Theorem67`, `Theorem68`, `Remark69`, `ExtAAll`, `ExtVbIff`, `GREqJR`, `ExtGR0`, `GRSEq`, `ExtGRbIff`, `CnBox`, `CnInv` |
| Prim(ℕ,ℕ) | AFP `PrimRec1` | not connected | Mathlib `Nat.Primrec` | own inductive `PrimNN` (unary Cantor characterization) | not defined |

### 4.3 Comparison

Line counts cover Sections 2–6, including Robinson's theorem where it is proved (comments
included). The extensions of §2.1 and §2.2 add 675 more lines in Isabelle, 1 505 in Mizar,
511 in Lean, 513 in Rocq and 2 654 in Z/EVES. Z/EVES proves Remark 6.9 as the case a = 1 of
the extension §2.1, so its lines are counted there. §2.3 adds 2 116 lines in Isabelle, 3 566 in
Mizar, 1 600 in Lean, 1 776 in Rocq and 5 336 in Z/EVES. The check times below are for the whole
development, including §2.

| | Isabelle/HOL | Mizar | Lean 4 | Rocq | Z/EVES |
|---|---|---|---|---|---|
| Lines | 2 011 (1 710 without Robinson; 84 are proof methods) | 4 094 | 1 405 (97 are proof automation) | 1 556 (160 are proof automation) | 5 666 |
| Check time from clean | ~30 s (after the AFP session) | ~25 s | ~2 min (loading Mathlib and proof search) | ~1 min | ~3 min (on macOS, in a Linux VM) |
| What is proved | everything; `suitable` means equal to Prim; for §2.3, J. Robinson's 1950 theorem is a hypothesis | everything **at closure level**: every basis generates the same closure as Robinson's ⟨S, E, F + G, FG, F^□⟩ (for §2.3, as J. Robinson's ⟨S, E, F + G, FG, F⁻¹⟩); neither Robinson theorem is proved | as in Isabelle | as in Isabelle | everything **at closure level**, as in Mizar |
| Robinson's theorem | proved, using the AFP characterization `PrimRec1'` | missing | proved against Mathlib's `Nat.Primrec` (Szudzik pairing) | proved against its own `PrimNN` (Cantor pairing) | missing |
| Soundness (closure ⊆ Prim) | AFP `prec` tactic | not applicable | Mathlib `Primrec` API (`nat_iterate`, `nat_sqrt`, …) | bootstrapped by hand in `Prim.v` (+, ∸, ×, =, √, E, Hf, iteration) | not applicable |
| Axioms | HOL | Tarski–Grothendieck set theory | `propext`, `Classical.choice`, `Quot.sound` | functional extensionality only; §2.3 also uses excluded middle and indefinite description (`ClassicalEpsilon`), since inversion must decide whether a function is onto | ZF set theory (the Z mathematical toolkit) |
| Arithmetic automation | `simp`, `algebra_simps`, `presburger`, `arith` | none beyond the checker's polynomial normalization; every inequality step needs a library lemma | `omega`, `nlinarith`, `ring`, `simp` | `lia`, `nia` (through mczify) | linear arithmetic and polynomial normalization in the simplifier; nonlinear steps through `timesMonotonic2` |

### 4.4 Findings

- **Library support decides the size of the Robinson part.**
  - Isabelle (the AFP's `PrimRec1'`) and Lean (Mathlib's `Nat.Primrec`) both provide a
    *unary* characterization of the primitive recursive functions. With it, Robinson's theorem
    is an induction with seven cases.
  - Mizar's MML only has n-ary partial functions on tuples (`COMPUT_1`), and Z/EVES has no
    library of computable functions at all. That is why these two versions stop at closure
    level.
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
  Four of the provers automate them, each with its own mechanism; Mizar has no user-definable
  tactics.

  | Prover | Mechanism | Automation |
  |---|---|---|
  | Rocq | Ltac2 (`Tactics.v`, `ExtGR.v`) | `clos_solve`, `sound`, `simulate`; for §2.3 `inv_eq`, `eval_at` |
  | Isabelle | Eisbach methods with named theorems (`UPRF_Methods.thy`, `UPRF_Ext_GR.thy`) | `clos_solve`, `clos_sound_m`, `clos_subset_m`, `simulate`; `eval`; for §2.3 `inv_eq` |
  | Lean | tactic macros, extensible through `macro_rules` (`Tactics.lean`, `ExtGR.lean`) | `clos_solve`, `prim_sound`, `simulate`; for §2.3 `inv_eq`, `eval` |
  | Z/EVES | closure rules stated as rewrite rules, applied by the simplifier; a Python generator (`z/gen/zgen.py`) for the repetitive definitions | `prove` with `ClosInit`, `ClosUnop`, `ClosBinop` |

  In Rocq, Isabelle and Lean, most membership lemmas and every suitability theorem of 6.8 and
  6.9 became one line. The refactored files lost about 125 lines (Rocq), 160 lines (Isabelle)
  and 80 lines (Lean) of proof. One design point mattered in all three: decomposing a function
  **by its syntactic head**, never by unification modulo definitions. The Rocq version compares
  terms syntactically, Lean uses reducible transparency, and Isabelle uses one rule per
  operator. Without it, unification unfolds √ and the Cantor functions and can hang. In Z/EVES
  the rewrite rules close short membership goals by themselves, but long chains of memberships
  have to be built one step at a time.

  §2.3 brought two more recurring patterns, automated in Isabelle, Lean and Rocq:
  - `inv_eq` proves F⁻¹(x) = v from: F is onto, F(v) = x, and v is at most every preimage of x;
  - `eval` (`eval_at` in Rocq) computes the value of an expression at a point.

  A third pattern became a generic lemma, `sub_inv`, in the same three provers: "X (X V)⁻¹
  subtracts c when V(y) = y + c". It holds for every X with a decomposition
  y = base(t) + X(y), X(y) ≤ bound(t). E and K are instances.
- **Closures as inductive predicates** (Lean, Rocq) give structural induction for free.
  Isabelle, Mizar and Z/EVES define the closure as an intersection of closed sets and prove the
  induction principle (Isabelle) or work with "least closed set" arguments (Mizar, Z/EVES).
- **The paper's proofs are mostly arithmetic.** Each formula `X ≡ …` hides a polynomial
  identity with truncated subtraction. Provers with a decision procedure for linear integer
  arithmetic plus a nonlinear heuristic (`omega`/`nlinarith`, `lia`/`nia`, `presburger`) prove
  most of them in one line. The other two need more steps spelled out:
  - in Mizar, an inference may not mix a definition expansion with arithmetic, and numerals
    block instantiation;
  - Z/EVES decides linear arithmetic, but nonlinear facts must be supplied, and the arguments
    of functions are not normalized, so a value lemma applies only to the exact form of its
    argument.

  Mostly for these reasons, Mizar is about 2–3× and Z/EVES about 3–4× longer than the others.
- **Remark 6.9 hides one use of soundness.** At closure level (Mizar, Z/EVES), Remark 6.9 needs
  F^□(1) in the closure, and Theorem 6.8 needs K and L there. Both were proved directly, using
  a general product built from Lemma 6.6. The other provers get these memberships from
  Robinson's theorem.
- **Definitions and consistency.** In Isabelle, Lean and Rocq, definitions are conservative by
  construction, and Mizar requires correctness proofs (existence, uniqueness) for its definitions.
  In Z, an axiomatic definition is an unchecked axiom. The Z/EVES version therefore follows
  each of its 33 axiomatic definitions with a consistency theorem, which shows that an
  explicit witness term satisfies it.
- **Pitfalls specific to each prover.** They are listed in each folder's README, for example:
  - Lean's and Rocq's `∘` associate in opposite directions;
  - ssreflect's `//` and `/=` try to compute √ and the Cantor functions and hang;
  - Mizar can cite other articles' theorems only by number, so its formalization is a single
    file;
  - Z/EVES rewrites `x + 1` to `1 + x`, so rewrite rules must be stated in that normal form.

---

## License

MIT (see [LICENSE](LICENSE)). The papers summarized in `references/` and `others/` are
copyrighted by their publishers and are not included.
