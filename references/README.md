# References of Severin, *Unary primitive recursive functions* (JSL 2008, arXiv:cs/0603063)

The numbers are those of the paper's bibliography.

| # | Reference | DOI |
|---|---|---|
| 1 | Axt, *Iteration of relative primitive recursion*, Math. Ann. 167 (1966) 53–55 |  |
| 2 | Dima, *Sudan function is universal for the class of primitive recursive functions*, St. Cerc. Mat. 33 (1981) 59–67 |  |
| 3 | Georgieva, *Another simplification of the recursion scheme*, Arch. Math. Logik 18 (1976) 1–3 | doi:10.1007/BF02007251 |
| 4 | Georgieva, *Classes of one-argument recursive functions*, Z. Math. Logik Grundlagen Math. 22 (1976) 127–130 | doi:10.1002/malq.19760220117 |
| 5 | Germano, Mazzanti, *Primitive iteration and unary functions*, APAL 40 (1988) 217–256 | doi:10.1016/0168-0072(88)90032-2 |
| 6 | Gladstone, *A reduction of the recursion scheme*, JSL 32 (1967) 505–508 | doi:10.2307/2270177 |
| 7 | Gladstone, *Simplifications of the recursion scheme*, JSL 36 (1971) 653–665 | doi:10.2307/2272468 |
| 8 | Goodstein, *Recursive Number Theory*, 1957 (book) |  |
| 9 | Grzegorczyk, *Some classes of recursive functions*, Rozprawy Mat. 4 (1953) 1–46 |  |
| 10 | Mazzanti, *Bounded iteration and unary functions*, MLQ 51 (2005) 89–94 | doi:10.1002/malq.200410010 |
| 11 | Naumović, *A classification of the one-argument primitive recursive functions*, Arch. Math. Logik 23 (1983) 161–174 | doi:10.1007/BF02023023 |
| 12 | Ritchie, *Classes of recursive functions based on Ackermann's function*, Pacific J. Math. 15 (1965) 1027–1044 |  |
| 13 | J. Robinson, *General recursive functions*, PAMS 1 (1950) 703–718 |  |
| 14 | J. Robinson, *A note on primitive recursive functions*, PAMS 6 (1955) 667–670 |  |
| 15 | R. M. Robinson, *Primitive recursive functions*, Bull. AMS 53 (1947) 925–942 |  |
| 16 | R. M. Robinson, *Primitive recursive functions II*, PAMS 6 (1955) 663–666 |  |
| 17 | Szalkai, *On the algebraic structure of primitive recursive functions*, Z. Math. Logik Grundlagen Math. 31 (1985) 551–556 | doi:10.1002/malq.19850313503 |

## Results per reference

Statements only (proofs not checked). Notation used below, unless a paper says otherwise:
$`S`$ successor, $`I`$ identity, $`E(x) = x - \lfloor \sqrt{x}\rfloor^2`$ (excess over a square), $`Q = 0^E`$ (characteristic function of squares),
$`P`$ predecessor, $`B^x a`$ = pure iteration without parameter ($`F0 = a`$, $`F(x+1) = B(Fx)`$), $`B^{-1}x = \mu y[By = x]`$ (inversion, only when $`B`$ is onto).
$`J, K, L`$ are pairing functions; *which* pairing differs between papers (noted where it matters).
A "schema" or "formula" $`Fx = \dots`$ means a rule that builds a new unary function $`F`$ from given unary functions $`A, B`$.

### [1] Axt 1966 — *Iteration of relative primitive recursion*
Relativises Axt's hierarchy (in his paper "Iterations of primitive recursion") to an arbitrary oracle $`\kappa`$.
$`K_n^\kappa`$ = functions primitive recursive in $`\kappa`$ with at most $`n`$ nested applications of the primitive recursion schema (Kleene's schemata ( ), (I)–(V)).
- **Thm 1.** If $`K_n^\kappa = K_{n+1}^\kappa`$ for some $`n`$, then every function primitive recursive in $`\kappa`$ lies in $`K_n^\kappa`$ (the hierarchy cannot stop growing and then resume).
- **Thm 2.** For every $`n`$ there is a function primitive recursive in $`\kappa`$ outside $`K_n^\kappa`$. It is built with increasing "diagonal" functions $`\gamma_n^*`$, $`\gamma_n`$, and every function in $`K_n^\kappa`$ is eventually bounded by some $`\gamma_n^*(b, \cdot)`$.
- **Corollary.** $`K_n^\kappa \subsetneq K_{n+1}^\kappa`$ for all $`n`$ (proper hierarchy of length $`\omega`$, relative to any $`\kappa`$).

### [2] Dima 1981 — *Funcţia lui Sudan este universală pentru clasa funcţiilor primitiv recursive* (St. Cerc. Mat. 33, 59–67)
In Romanian, with an English abstract ("Sudan function is universal for the class of primitive recursive functions"). It repeats Ritchie's construction [12] for **Sudan's function**, prompted by a problem of Grzegorczyk [9] and a suggestion of C. Calude.
- **Sudan's function.** $`F(x,y,0) = x+y`$, $`F(x,0,n+1) = x`$, $`F(x,y+1,n+1) = F(F(x,y,n+1), F(x,y,n+1)+y+1, n)`$; write $`F_n(x,y) = F(x,y,n)`$.
- **§2.** Monotonicity facts, Props 2.1–2.10, some taken from Calude's book:
  - $`F_n(x,y) > x`$ for $`y > 0`$;
  - $`F_n`$ is strictly increasing in both arguments, and $`F_{n+1} > F_n`$;
  - $`F_n(F_n(x,k),l) \le F_n(x, F_{n+1}(k,l))`$;
  - $`xy \le F(x,y)`$ in a suitable level, etc.
- **Def 3.3.** $`\mathcal{A}_n`$ = the smallest class of unary functions containing $`S`$, $`E`$, $`\lfloor \sqrt{x}\rfloor`$ and $`F_i(x,x)`$ ($`i \le n`$), closed under sum, product, composition and **limited** iteration. This mirrors Ritchie's $`\mathcal{G}^n`$.
- **Thm 3.1.** $`\mathcal{A}_n`$ contains:
  - $`I`$, the constants, $`\mathrm{sg}`$, $`\overline{\mathrm{sg}}`$;
  - Robinson's pairing $`J, K, L`$ and the projections $`M_i^p`$;
  - pairing and conditional expressions.
- **Thm 3.2 + Cor.** For $`f \in \mathcal{A}_n`$ there is $`k`$ with $`f(x) < F_{n+1}(x,k)`$ for $`x \ge 2`$. So $`F_{n+1}(x,x)`$ majorizes $`\mathcal{A}_n`$ a.e., and the classes are distinct.
- **Lemma 3.1 + Cor.** Unlimited iteration of a function in $`\mathcal{A}_n`$ lands in $`\mathcal{A}_{n+1}`$. Hence $`\bigcup_n \mathcal{A}_n`$ is closed under composition and iteration, and so (by Robinson [15]) equals the unary PR functions.
- **§4.** $`\mathcal{F}_n`$ = the closure of $`S`$, $`0`$, the projections and $`F_n(x,y)`$ under substitution and limited recursion.
  - Thm 4.3–4.4: $`\mathcal{F}_n`$ is exactly the class of associates (multi-argument versions through the pairing) of $`\mathcal{A}_n`$.
  - **Cor:** $`\bigcup_n \mathcal{F}_n`$ = all PR functions. In other words, the hierarchy generated by Sudan's function covers exactly the PR functions: Sudan's function is *universal*, as Ackermann's is in Ritchie [12].

### [3] Georgieva 1976 — *Another simplification of the recursion scheme* (Arch. Math. Logik 18)
Unary functions with truncated subtraction and pure iteration from $`S`$ alone.
- **Ackermann-like sequence.** $`f_0(x) = S(x)`$, $`f_{n+1}(0) = f_n(1)`$, $`f_{n+1}(x+1) = f_n(f_{n+1}(x))`$.
- **Lemmas 1–5.** Growth and monotonicity: $`x+1 \le f_n(x)`$, $`f_n`$ is increasing in $`x`$, and $`f_n(x) \le f_{n+1}(x)`$.
- **Lemma 6 (majorization).** Every function in $`R_1`$ (unary PR functions) is bounded by some $`f_n`$. The proof is by induction on how the function is built, with $`h \mathbin{\dot-} g \le h`$.
- **Lemma 7 (addition).** If $`h, g \in R_1`$ then $`h + g \in R_1`$, via $`h + g = 2f_n \mathbin{\dot-} ((2f_n \mathbin{\dot-} h) \mathbin{\dot-} g)`$ with $`2f_n \ge h + g`$.
- **Thm 1.** $`R_1`$ = closure of $`S`$ under $`h \mathbin{\dot-} g`$, composition and pure iteration without parameter. In other words, the PR functions of one variable are not reduced if recursion is restricted to pure iteration with no parameter and $`x \mathbin{\dot-} y`$ is adjoined.
- **Thm 2.** That closure is not enough for functions of several variables. The class $`R'`$ (closure of zero, successor and projections under $`x \mathbin{\dot-} x_k`$, substitution and pure iteration) is a proper subclass of all PR functions: $`f_n(x_k) + f_n(x_i)`$ is not in $`R'`$ (Lemmas 8–9).

### [4] Georgieva 1976 — *Classes of one-argument recursive functions* (Z. Math. Logik 22)
A Grzegorczyk-like hierarchy of unary classes that uses only $`\mathbin{\dot-}`$, composition and limited iteration.
- **Definition.** $`\mathcal{L}_n`$ is the smallest class containing $`f_0 = S`$ and $`f_n`$ (the sequence of [3]) and closed under $`g \mathbin{\dot-} h`$, composition and limited iteration ($`f(x) = g^x(0) \le j(x)`$).
- **§1.**
  - $`\mathcal{L}_n`$ contains 0, the identity, the constants, $`\mathrm{sg}`$ and $`\overline{\mathrm{sg}}`$.
  - $`\mathcal{L}_n \subseteq \mathcal{L}_{n+1}`$.
  - For $`n \ge 2`$ it is closed under $`+`$ (Lemma 1.7) and under Boolean combinations of predicates (Lemma 1.9).
  - Unlimited iteration of $`g \in \mathcal{L}_n`$ lands in $`\mathcal{L}_{n+1}`$ (Lemma 1.8).
  - Each $`f \in \mathcal{L}_n`$ is eventually below $`f_{n+1}`$ (Thm 1.1), so the classes are distinct.
- **§2.**
  - $`\mathcal{L}_0 = \mathcal{L}_1`$ (Thm 2.1).
  - $`\mathcal{L}_1`$ contains $`x \bmod k`$ and $`\lfloor x/k\rfloor`$ for $`k = 2, 3, 5`$ (Lemma 2.1).
  - $`\mathcal{L}_3`$ contains $`2^x`$ and conditional definitions (Lemma 2.2). It also contains $`Q`$, by Gladstone's iteration ([7]) (Lemma 2.3), and $`x^2`$, $`\lfloor \sqrt{x}\rfloor`$, $`E`$ (Lemma 2.4).
  - For $`n \ge 3`$, $`\mathcal{L}_n`$ is closed under multiplication (Lemma 2.5).
- **Thm 2.2.** $`\bigcup_n \mathcal{L}_n`$ = all unary PR functions.
- **Thm 3.1.** $`\mathcal{L}_{n+1} = \mathcal{E}^1_{n+1}`$ (the unary part of Grzegorczyk's class $`\mathcal{E}^{n+1}`$) for $`n \ge 2`$.
  - **Caveat (C. Calude, 1982; see [`others/README.md`](../others/README.md)).** The proof of $`\supseteq`$ relies on $`r_n(x,x) = p_{n-1}(x)`$, which fails: for $`n = 3`$, $`r_3(x,x) = x^x`$ but $`p_2(x) = 2^x`$. The inclusion $`\subseteq`$ is correct. Calude–Tatarâm 1983 (Thm 3) later gives the equality.

### [5] Germano, Mazzanti 1988 — *Primitive iteration and unary functions* (APAL 40)
A systematic theory of **primitive iteration operators** that match programming constructs ("for ... do"), applied to the set $`\mathrm{prim}(\mathbb{N},\mathbb{N})`$ of unary PR functions.
- **Iteration operators.** The general one is $`I(f, g, h): x \mapsto h^{f x}(g x)`$ ("$`\mathrm{iter}_1`$"). It is specialised to:
  - $`f \vert h: x \mapsto h^{f x}(x)`$ ("$`\mathrm{iter}_2`$", the *for-until-do* construct);
  - $`g^\square`$-like forms ("$`\mathrm{iter}_3`$") and Robinson's $`C_0\square f`$.
- **Method.**
  - Unary functions are treated as *conjugates* of sequence functions $`\mathbb{N}^a \to \mathbb{N}^b`$ through a pairing.
  - §1 characterises primitive computable sequence functions with these operators.
  - §2: for **any** pairing $`J`$, $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(C, S, K_J, L_J, (f,g)_J, f\circ g, \mathrm{iter}_k)`$ for $`k = 1, 2`$ (Thm 2.1). There are variants with a "star" operator (Thm 2.2) and with composition only (Thm 2.3).
- **§3 (Cantor-like pairing $`R(x,y) = (x+y)^2 + x`$, so $`K_R = E`$, $`L_R = \lfloor \sqrt{\cdot}\rfloor \mathbin{\dot-} E`$):**
  - **Thm 3.1** ("the simplest known characterization"): $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(I, S, P, I(f,g,h))`$.
  - **Thm 3.2.1:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E, f + g, f\circ g, f \vert g)`$. This is the analogue of Robinson's §7 Thm 3 ([15]), with the for-loop operator $`f \vert g`$ in place of $`F^\square`$.
  - **Thm 3.2.2:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(C, S, \mathrm{quad},^+f, f\circ g, f \vert g)`$, where $`^+f`$ is a "plus" operator.
  - **Thm 3.2.3:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, P, \mathrm{quad}, \mathrm{rad}, f\circ g, f \vert g)`$ ($`\mathrm{quad} = x^2`$, $`\mathrm{rad} = \lfloor \sqrt{x}\rfloor`$).
- **§4 (Gödel-like pairing $`G(x,y) = 2^x3^y`$, $`K_G = \mathrm{exp}[2]`$, $`L_G = \mathrm{exp}[3]`$):**
  - **Thm 4.1:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, \mathrm{mult}[2], \mathrm{mult}[3], \mathrm{exp}[2], \mathrm{exp}[3], f\circ g, I(f,g,h))`$.
  - **Thm 4.2.1:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(\mathrm{pow}[2], \mathrm{pow}[3], \mathrm{exp}[2], \mathrm{exp}[3], f\cdot g, f\circ g, f \vert g)`$.
  - **Thm 4.2.2:** the same with a "times" operator.
  - **Thm 4.2.3:** $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(\mathrm{pow}[2], \mathrm{exp}[2], \mathrm{mult}[2], \mathrm{div}[2], \mathrm{div}[3], f\circ g, f \vert g)`$.
- **Historical note (p. 250–251).** It restates Robinson's unary results ([15] §6–7): $`\mathrm{clos}(S, E, f+g, f\circ g, g^\square)`$ and $`\mathrm{clos}(S, Q, \vert f-g\vert , f\circ g, g^\square)`$. It adds $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, \vert f-g\vert , f\circ g, g^\square)`$ (from Gladstone [7]) and $`\mathrm{clos}(S, f \mathbin{\dot-} g, f\circ g, g^\square)`$ (Georgieva [3]).

### [6] Gladstone 1967 — *A reduction of the recursion scheme* (JSL 32)
Answers Robinson's question ([15]) on **pure recursion with one parameter**, $`f(0,y) = g(y)`$, $`f(x+1,y) = h(f(x,y), y)`$ (scheme $`\mathcal{R}*`$, where $`h`$ does not see $`x`$).
- **Robinson's earlier result.** $`\mathcal{R}*`$ suffices for all PR functions if the predecessor $`P`$ is adjoined.
- **Theorem.** Nothing needs to be adjoined: $`P`$ is obtainable from zero, successor and identities by composition and $`\mathcal{R}*`$.
- **Proof.**
  - Lemmas 1–3: $`+`$, $`\cdot`$ and $`x^y`$, Boolean operations on characteristic functions, and definition by cases.
  - Lemma 4: $`C(x=0)`$, $`C(x=1)`$, $`x \bmod 2`$ and $`x \bmod 3`$.
  - **Lemma 5 (crux):** $`C(x < y)`$. Iterate $`y \mapsto 3y/2`$ while $`y`$ is even. Then $`g(x, 2^y) \ne 0`$ iff $`x < y`$, i.e. a comparison is read off the 2-adic valuation.
  - Lemma 6: $`P(x) = f(x, x)`$ with $`f(0,y) = y`$, $`f(x+1,y) = 0`$ if $`f(x,y) \ge y`$, and $`f(x,y) + 1`$ otherwise.
- **Open problem stated.** The analogous question for the scheme $`f(x+1,y) = h(f(x,y), x)`$ (the parameter replaced by the counter).

### [7] Gladstone 1971 — *Simplifications of the recursion scheme* (JSL 36)
Resolves three problems left open by Robinson ([15]). $`\mathrm{Clos}(M, \varphi)`$ = closure of zero, successor, projections and $`M`$ under substitution and the scheme $`\varphi`$.
- **Thm 1.** **Pure iteration with $`\le 1`$ parameter** needs nothing adjoined.
  - Lemmas 4–10: $`x \bmod n`$, $`\lfloor px/q\rfloor`$, $`n^x\cdot y`$, $`M_{p/q}`$, and comparison $`\mathrm{Ch}\{x<y\}`$ via valuations.
  - Lemma 11: $`\mathrm{Ch}\{\exists z: x = 2^z + z\}`$.
  - **Lemma 12:** $`P(x)`$.
  - Lemma 13: $`y \mathbin{\dot-} x`$, $`\vert x-y\vert`$.
  - Lemma 14: an explicit pairing $`2^x\cdot 3^y`$ with inverses inside the class.
- **Thm 2.** **Mixed recursion with no parameter** ($`f(0)=n`$, $`f(x+1) = g(x, f(x))`$) needs only $`x + y`$.
  - It suffices to get $`Q`$, because Robinson showed $`x+y, Q`$ suffice.
  - Steps: $`x^2`$, parity, $`\lfloor x/2\rfloor`$; then (Lemma 6, the crux) $`\mathrm{Ch}\{\exists z: x = 2^z\}`$; then $`\mathrm{Ch}\{x=y\}`$, since $`2^x + 2^y`$ is a power of 2 iff $`x = y`$; then $`\lfloor \sqrt{x}\rfloor`$ and $`Q`$.
- **Thm 3.** **Pure iteration with no parameter** needs only $`\vert x - y\vert`$.
  - Lemma 4: $`x + y = \vert \vert \vert f - x\vert - y\vert - f\vert`$ with $`f(x,y) = \vert 2^{2x+1} - 2^{2y+2}\vert \ge x + y`$.
  - Lemma 5: $`P(x) = \vert (x + \overline{\mathrm{sg}} x) - 1\vert`$.
  - Lemmas 7–10: $`x \bmod n`$, $`\lfloor px/q\rfloor`$.
  - **Lemma 11:** definition by cases. With $`g(x) = \vert 2^{x+1+[2\mid x]} - 2^{x+1}\vert`$, $`h(x) = \vert \vert g - (2^x + x)\vert - (2^x + x)\vert`$ is $`0`$ for even $`x`$ and $`2x`$ for odd $`x`$, and $`F(x) = \lfloor h(2f(x) + \mathrm{Ch}\{\neg A(x)\})/4\rfloor`$.
  - **Lemma 13 ($`Q`$):** a Conway-type map $`f(0) = 5`$, $`f(x+1) = \lfloor 3f/2\rfloor , \lfloor 2f/5\rfloor , \lfloor 2f/3\rfloor`$ or $`\lfloor 15f/2\rfloor`$ depending on divisibility by 2, 3 and 5. For $`x > 0`$, $`f(x)`$ is a power of 2 iff $`x`$ is a square, so $`Q(x) = \mathrm{Ch}\{3 \mid f(x)\}`$. This is the source of Severin's $`W`$ (Lemma 5.6).
- **Table.**
  - With one parameter, nothing is needed for either recursion or iteration.
  - With no parameter: for mixed recursion/iteration, $`\vert x-y\vert`$ or $`x+y`$; for pure recursion/iteration, $`\vert x-y\vert`$ or $`x+y, E`$.
- **Open questions (§6).**
  - Do the adjoined functions become redundant if, e.g., $`\mu`$ is added?
  - Is mixed recursion with no parameter enough with nothing adjoined, for unary functions?

### [9] Grzegorczyk 1953 — *Some classes of recursive functions*
Introduces the **Grzegorczyk hierarchy**.

§1–2: elementary functions (Kalmár), $`\mathcal{E}`$.
- $`\mathcal{E}`$ = closure of $`x+1, x+y, x\mathbin{\dot-}y`$ under substitution, limited sum and limited product.
- **Thm 1.1 / Cor 1.2.** If a class is closed under substitution and contains $`x+1, x+y, x\mathbin{\dot-}y`$ (or contains $`x^y`$), then its relations are closed under the propositional connectives.
- **Thm 2.1, 2.2a/b.** $`\mathcal{E}`$ is closed under limited minimum and its relations under limited quantifiers. More generally, closure under limited minimum gives closure under limited $`\exists`$.
- **Cor 2.1a.** Closure under substitution, $`x\mathbin{\dot-}y`$, $`x\cdot (1\mathbin{\dot-}y)`$ and the "narrowed limited sum" $`\Sigma_{i\le y} 1\mathbin{\dot-}F(u,i)`$ gives closure under limited minimum.
- **Thm 2.3.** $`\mathcal{E}`$ is closed under limited recursion. This uses the coding of finite sequences by prime powers; $`\mathrm{exp}`$, $`p_k`$, $`\lfloor x/y\rfloor`$ and $`\lfloor \sqrt{x}\rfloor`$ are elementary.
- **Thms 2.4–2.6.** These are equivalent definitions of $`\mathcal{E}`$:
  - $`x+1, x\mathbin{\dot-}y, x^y`$ + substitution + limited minimum;
  - $`x+1, x^y`$ + substitution + limited recursion;
  - $`x+1, x\mathbin{\dot-}y, x\cdot y, x^y`$ + substitution + limited summation.
  
  The seven "elementary operations" are interchangeable on this basis.

§3: classes based on limited recursion, and reduction to one argument.
- **Thm 3.1.** Suppose $`\mathcal{X}`$ is inductively defined from substitution plus operations that stay inside unary functions, and $`\mathcal{X}`$ contains pairing functions $`I, K, L`$. Then $`\mathcal{X}_1`$ (its unary part) is itself inductively definable. It needs only the unary operations, composition $`O_1: f(g(x))`$, and $`O_2: I(Kx, f(Lx))`$, $`I(f(Kx), Lx)`$.
- **Thm 3.2.** $`\mathcal{E}_1`$ (the unary elementary functions) is inductively definable in this sense.
- **Thms 3.3–3.4.** These are domination transfer results. Let $`\mathcal{X}`$ and $`\mathcal{Y}`$ be built by substitution and limited recursion, and let $`\mathcal{X}`$ contain non-decreasing functions dominating $`\mathcal{Y}`$'s initial functions.
  - Every $`f \in \mathcal{Y}`$ is then dominated by a non-decreasing function of $`\mathcal{X}`$.
  - If $`f`$ grows faster than every function of $`\mathcal{X}_1`$, it grows faster than every function of $`\mathcal{Y}_1`$.
- **Thm 3.5.** If every function of $`\mathcal{X}_1`$ is dominated by one of $`\mathcal{Y}_1`$, then $`\mathcal{X}`$ does not contain the universal function of $`\mathcal{Y}`$. (There is also the diagonal fact that a class containing $`x+1`$ never contains its own universal function.)
- **Thm 3.6.** If $`\mathcal{Y}`$ contains $`h(n,x)`$ bounding the $`n`$-th function of $`\mathcal{X}_1`$, then $`\mathcal{Y}`$ contains a universal function for $`\mathcal{X}_1`$.

§4: the classes $`\mathcal{E}^n`$.
- Definitions:
  - Growth functions: $`f_0 = y+1`$, $`f_1 = x+y`$, $`f_2 = (x+1)(y+1)`$. For $`n \ge 2`$, $`f_{n+1}(0,y) = f_n(y+1,y+1)`$ and $`f_{n+1}(x+1,y) = f_{n+1}(x, f_{n+1}(x,y))`$.
  - $`\mathcal{E}^n`$ = closure of $`x+1, U_1, U_2, f_n`$ under substitution and limited recursion.
- **Thms 4.1–4.3.** $`f_n(x,y) > y`$, and $`f_n`$ is strictly increasing in both arguments.
- **Thm 4.4.** $`\mathcal{E}^3 = \mathcal{E}`$, the Kalmár elementary functions.
- **Thm 4.5.** $`\mathcal{E}^0`$ contains $`E`$, $`Q`$, $`R`$ (a pairing pair) and the iterates $`Q^n`$, and is closed under limited minimum.
- **Thm 4.6.** Every $`\mathcal{E}^n`$ is closed under limited minimum, and its relations under limited quantifiers and propositional operations.
- **Thm 4.7.** $`\mathcal{E}^n \subseteq \mathcal{E}^{n+1}`$.
- **Thm 4.8.** In the unary class $`\mathcal{W}^n_1`$ used in the proofs, a function of construction order $`k`$ is bounded by $`f_{n+1}(k, x)`$.
- **Thm 4.9.** $`f_{n+1}(x,x)`$ grows faster than every function of $`\mathcal{E}^n`$. Hence $`\mathcal{E}^n \subsetneq \mathcal{E}^{n+1}`$.
- **Thm 4.10.** For $`n > 2`$, the relations of $`\mathcal{E}^n`$ are the smallest class containing six simple relations ($`x=0`$, $`x=y+1`$, $`x=y^z`$, $`x=y\mathbin{\dot-}z`$, $`x=f_n(y,z)`$, $`x\le f_n(y+1,z+1)`$) closed under the propositional connectives and limited quantifiers.
- **Lemma 4.11.** Every $`f \in \mathcal{E}^n`$ has an "estimating expression".
- **Thm 4.12.** For $`n > 2`$, $`\mathcal{E}^{n+1}`$ contains a universal function for the unary class $`\mathcal{E}^n_1`$.
- **Thm 4.13.** $`\bigcup_n \mathcal{E}^n = \mathcal{R}`$, the primitive recursive functions.
- **Lemma 4.14.** A unary PR function of construction order $`\le n`$ in **R. M. Robinson's unary basis** ($`x+1`$, $`E`$, $`+`$, composition, $`h^x(0)`$, from [15] Thm 3) lies in $`\mathcal{E}^{n+3}`$.
- **Thm 4.15.** Substitution plus limited recursion over any finite set of PR functions does not give all PR functions.
- **Open problems 1–9** (p. 41–42), among them:
  - Are limited recursion and limited minimum equivalent over $`\mathcal{E}^0`$, $`\mathcal{E}^1`$, $`\mathcal{E}^2`$?
  - Does the universal function for $`\mathcal{E}^0_1`$ lie in $`\mathcal{E}^1`$ or $`\mathcal{E}^2`$?
  - Can the relations of $`\mathcal{E}^n`$ for $`n < 3`$ be characterised as in Thm 4.10?
  - Is $`\mathcal{E}^n`$ obtainable by substitution alone?
  - Do Ackermann-style $`f'_n`$ give the same classes? (Answered positively in [12].)
  - Is single recursion enough for the double-recursive functions?

§5: applications of $`\mathcal{E}^0`$.
- **Thm 5.1.** Every computable function is $`A(\iota x[B(u,x)=0])`$ with $`A, B \in \mathcal{E}^0`$. This uses J. Robinson's result [13, Thm 4].
- **Thm 5.2.** This gives a canonical form $`f(u) = Q(\iota x[A(x,u)=0])`$ with $`A \in \mathcal{E}^0`$.
- **Thm 5.3.** Every recursively enumerable set is enumerated by a function of $`\mathcal{E}^0`$.

### [10] Mazzanti 2005 — *Bounded iteration and unary functions* (MLQ 51)
Unary characterizations of complexity classes using only composition and **bounded iteration** $`f \vert_j g: n \mapsto g^{fn}(n)`$, provided all iterates stay $`\le jn`$.
- **Pairings from increasing functions.** For a *standard increasing* $`h`$ ($`n < h(n+1) - h(n)`$):
  - $`\mathrm{rad}_h(n)`$ = the $`m`$ with $`h(m) \le n < h(m+1)`$;
  - $`E_h(n) = n \mathbin{\dot-} h(\mathrm{rad}_h n)`$;
  - $`J_h(n,m) = h(h(n+m) + n) + m`$ is a pairing with $`K = \mathrm{rad}_h \circ E_h`$, $`L = E_h`$ (Lemma 3.3).
  - Example: Robinson's $`((m+n)^2 + n)^2 + m`$ from [15].
- **Lemma 2.4.** If $`S`$, $`P`$ and an increasing bound $`h`$ are in the closure, it is closed under the conditional operator.
- **Thm 4.2.** $`\mathrm{clos}{S, P, f, h, \mathrm{rad}_h}`$ contains $`K_h`$, $`L_h`$ and is closed under addition and pairing.
- **Thm 4.5.** If $`\mathcal{C}_f`$ is the closure of $`f, S, C, \mathrm{max}`$ and the projections under substitution and bounded recursion, and $`h \in \mathcal{C}_f`$ is standard increasing and bounds $`f`$, then $`\mathcal{C}_f(\mathbb{N},\mathbb{N}) = \mathrm{clos}{S, P, f, h, \mathrm{rad}_h}`$.
- **Consequences.**
  - **Thm 5.1:** $`\mathcal{E}^n(\mathbb{N},\mathbb{N}) = \mathrm{clos}{S, P, f_n, \mathrm{rad}_{f_n}}`$ for $`n \ge 2`$ (Grzegorczyk levels).
  - **Cor 5.2:** linear-space unary functions = $`\mathrm{clos}{S, P, x^2, \lfloor \sqrt{x}\rfloor}`$.
  - **Cor 5.3:** elementary unary functions = $`\mathrm{clos}{S, P, 2^x, \lfloor \mathrm{log}_2 x\rfloor}`$.
  - **Thm 5.4:** polynomial-space unary functions = $`\mathrm{clos}{S, P, n^{\vert n\vert}, \mathrm{log}_2, \mathrm{div}[2]}`$.

### [11] Naumović 1983 — *A classification of the one-argument primitive recursive functions* (Arch. Math. Logik 23)
A unary analogue of the **Axt hierarchy** (number of nested iterations), compared with the unary Grzegorczyk classes $`\mathcal{E}^n_1`$.
- **Definition.** $`\mathcal{J}^n`$:
  - $`x + 1 \in \mathcal{J}^n`$;
  - closed under composition and $`g \mathbin{\dot-} h`$;
  - for $`n \ge 1`$, closed under pure iteration $`f(0) = a`$, $`f(x+1) = g(f(x))`$ with $`g \in \mathcal{J}^{n-1}`$.
- **Lemma 1 (what each level contains).**
  - $`\mathcal{J}^0`$: $`x \pm  c`$, $`\mathrm{sg}`$, $`\overline{\mathrm{sg}}`$.
  - $`\mathcal{J}^1`$: $`+`$, $`cx`$, $`x \bmod c`$, and Boolean closure of relations.
  - $`\mathcal{J}^2`$: $`2^x`$, $`\lfloor x/c\rfloor`$, the pairing $`J(x,y) = 2^{x+y+2} + x`$, and definition by cases.
  - $`\mathcal{J}^3`$: $`Q`$ (via Gladstone's map) and the relation $`\exists k \le x: x = 2^k + k - 2`$.
  - $`\mathcal{J}^4`$: $`\lfloor \sqrt{x}\rfloor`$, $`\lfloor \mathrm{log}_2 x\rfloor`$, $`K`$, $`L`$.
  - $`\mathcal{J}^5`$: $`x^2`$ and products.
- **Lemma 1 (comparison with Grzegorczyk).** $`\mathcal{J}^n \subseteq \mathcal{E}^{n+1}_1`$, and $`\mathcal{J}^n = \mathcal{E}^{n+1}_1`$ for $`n \ge 6`$ (classical methods).
- **Thm 1.** For $`n \ge 3`$: $`\mathcal{J}^n = \mathcal{E}^{n+1}_1`$ iff $`\mathrm{exp}_p(x)`$ (the exponent of the prime $`p`$ in $`x`$) is in $`\mathcal{J}^n`$. The proof simulates register machines within the running-time bound.
- **Thm 2.** $`\mathrm{Rel}(\mathcal{J}^n) = \mathrm{Rel}(\mathcal{E}^{n+1}_1)`$ for $`n \ge 3`$, where $`\mathrm{Rel}`$ is the class of relations.
- **Thm 3.** $`\mathrm{Rel}(\mathcal{J}^n) \subsetneq \mathrm{Rel}(\mathcal{J}^{n+1})`$ for $`n \ge 2`$ (a proper hierarchy of relations).

### [12] Ritchie 1965 — *Classes of recursive functions based on Ackermann's function*
Answers Grzegorczyk's problem 7 [9] affirmatively, using unary classes and Robinson's pure iteration.
- **Def 1.1 (Ackermann-style functions).**
  - $`f_0(x,y) = x+1`$, $`f_1 = x+y`$, $`f_2 = xy`$.
  - $`f_{n+1}(x,0) = 1`$ and $`f_{n+1}(x,y+1) = f_n(x, f_{n+1}(x,y))`$, so $`f_3 = x^y`$.
- **Lemmas 1.1–1.7, Thm 1.1.** Monotonicity and growth properties. Main estimate ($`n \ge 3`$, $`x,k \ge 2`$): $`f_n(f_n(x,k), l) \le f_n(x, f_{n-1}(k,l))`$. Also $`f_{n-1}(f_m(x,y), f_m(x,z)) \le f_m(x, y+z)`$ for $`m \ge n`$.
- **Def 2.3.** The **unary classes** $`\mathcal{G}^n`$ ($`n \ge 2`$) are the closure of $`S, E, \lfloor \sqrt{x}\rfloor , f_n(x,x)`$ under $`+`$, $`\cdot`$, composition, and *limited* iteration $`f(x) = h^x(0) \le j(x)`$. (Robinson's pairing $`J(x,y) = ((x+y)^2+x)^2+y`$, $`K = E(\lfloor \sqrt{\cdot}\rfloor)`$, $`L = E`$ is used.)
- **Thm 2.1.** $`\mathcal{G}^n`$ contains $`I`$, all constants, $`K`$, $`L`$, the n-tuple projections $`M_i^(n)`$, $`\mathrm{sgn}`$ and $`0^x`$, and $`f_0`$, $`f_1`$, $`f_2`$ on the diagonal. It is closed under pairing and conditional expression.
- **Thm 2.2 + Cor.** For $`f \in \mathcal{G}^n`$ there is $`k`$ with $`f(x) < f_{n+1}(x,k)`$ for $`x \ge 2`$. Hence $`f_{n+1}(x,x)`$ majorizes all of $`\mathcal{G}^n`$.
- **Thm 2.3.** If $`g \in \mathcal{G}^n`$, then its pure iteration $`g^x(0)`$ lies in $`\mathcal{G}^{n+1}`$. So unrestricted iteration climbs exactly one level.
  - **Cor.** $`\bigcup_n \mathcal{G}^n`$ is closed under $`+`$, $`\cdot`$, composition and (unlimited) iteration.
- **Def 3.1.** $`\mathcal{F}^n`$ = closure of $`S, 0, U_i^n, f_n`$ under substitution and limited recursion.
- **Thm 3.1.** $`x+y`$, $`xy`$, $`x\mathbin{\dot-}y`$, $`\lfloor \sqrt{x}\rfloor`$, $`E`$, $`f_n(x,x)`$ are in $`\mathcal{F}^n`$. Hence $`\mathcal{G}^n \subseteq \mathcal{F}^n`$ for $`n \ge 2`$.
- **Thm 3.2.** Any primitive recursion $`f(\vec{x}, y)`$ can be expressed through a unary function $`f'`$ defined by **pure iteration** $`f'(z+1) = H''(f'(z))`$, using the pairing functions.
- **Thms 3.3–3.4.** $`\mathcal{F}^n`$ is exactly the class of all "associates" (multi-argument versions through $`J^(n)`$, $`M_i^(n)`$) of functions in $`\mathcal{G}^n`$. Primitive recursion over associates of $`\mathcal{G}^k`$ lands in associates of $`\mathcal{G}^{k+1}`$.
- **Corollaries.**
  - $`\mathcal{G}^n`$ = the unary part of $`\mathcal{F}^n`$.
  - $`\mathcal{G}^n \subsetneq \mathcal{G}^{n+1}`$ and $`\mathcal{F}^n \subsetneq \mathcal{F}^{n+1}`$.
  - $`\bigcup_n \mathcal{F}^n`$ = all PR functions.
- **Thm 4.1.** $`\mathcal{F}^n = \mathcal{E}^n`$ (Grzegorczyk's classes) for all $`n \ge 0`$. So $`\mathcal{G}^n`$ is a purely unary characterisation of the unary part of $`\mathcal{E}^n`$ for $`n \ge 2`$.

### [13] J. Robinson 1950 — *General recursive functions*
Analogue of R. M. Robinson's programme [15] for **general** ($`\mu`$-)recursive functions.
- **§1.** Defines general recursive functions as closure under substitution, primitive recursion and $`\mu`$.
  - With the Cantor pairing $`2J(x,y) = (x+y)^2 + 3x + y`$, the functions $`J, K, L`$ are obtainable by substitution from $`x+y`$, $`x\mathbin{\dot-}y`$, $`x^2`$, $`\lfloor x/2\rfloor`$, $`\lfloor \sqrt{x}\rfloor`$.
- **§2.** On the forms of the $`\mu`$-rule:
  - $`\mu y[A_1 = A_2]`$, $`\mu y[A = 0]`$, $`\iota y[A = 0]`$ (unique y) and inversion $`\mu z[Bz = x]`$ are all interconvertible given substitution and primitive recursion.
  - The strongest and weakest forms are equivalent. A more elaborate construction handles the $`\iota`$-rule.
- **§3 (elimination of primitive recursion).** All general recursive functions are obtained by substitution plus $`\mu`$ alone if
  - $`x+y`$ and $`Q`$ are adjoined (with the standard $`\mu`$ form), or
  - $`x+y`$ and $`E`$ are adjoined (with **inversion** $`A^{-1}x = \mu y[Ay = x]`$). $`K`$ or $`L`$ may replace $`E`$.
  
  Open question: is the same possible with $`\iota`$ instead of $`\mu`$ and finitely many PR initial functions?
- **§4. Thm 1.** Unary functions obtainable by substitution and inversion can be obtained using substitution only to define unary functions.
- **§4. Thm 2.** With $`I`$, $`0`$, $`x+y`$ as the only multi-argument initial functions, every unary function obtainable is generated by $`Fx = Ax + Bx`$, $`Fx = B(Ax)`$, $`Fx = B^{-1}x`$ (the last only for onto $`B`$).
- **§4. Thm 3.** All unary general recursive functions come from $`S`$ and $`E`$ by $`Ax+Bx`$, $`B(Ax)`$, $`B^{-1}x`$. $`E`$ can be replaced by $`K`$ or $`L`$, and $`S`$ by $`S0`$ (the constant 1). This is the exact analogue of [15] Thm 3 with $`B^{-1}x`$ in place of $`B^x 0`$.
- **§4. Thm 4.** **Addition can be eliminated.** All unary general recursive functions come from *some two* PR functions by composition and inversion alone. Any finite set of initial functions can be packed into two using pairing.
- **§4. Thm 5.** Explicitly: from the three functions $`J(LK, KL)`$, $`J(I, S0)`$, $`J(K+KL, I)`$ by substitution and inversion.
- **§4. Thm 6.** No **single** function generates all general recursive functions by substitution and inversion. (Only powers $`A^n`$ would be onto, so only the identity permutation would be obtained.)
- **§5. Thm.** Kleene normal form without metamathematics: every general recursive $`F(\vec{x}) = A(\iota y[B(\vec{x},y)=0])`$ with $`A`$, $`B`$ PR.
  - **Cor 1.** Every unary general recursive function is $`A \circ B^{-1}`$ with $`A`$, $`B`$ PR and $`B`$ onto.
  - **Cor 2.** $`F`$ is general recursive iff $`F = A \circ C`$ with $`A`$ and $`0^{\vert y - C(\vec{x})\vert}`$ PR.

### [14] J. Robinson 1955 — *A note on primitive recursive functions*
PR analogue of [13] §4 Thms 4–6 (Cantor $`J, K, L`$).
- **Thm 1.** All unary PR functions come from **some two** PR functions by **composition and $`Fx = B^x 0`$ alone** (no $`+`$).
  - Proof idea: map each $`F`$ to $`F* = J(FK, L)`$. Show $`(BA)*`$, $`(A+B)*`$ and $`(B^x 0)*`$ are obtainable from $`A*`$, $`B*`$ and fixed functions.
  - The needed fixed functions are $`S*, K*, K, J(I,I), G_1, G_2, G_3, J(K, LL), H`$ (nine functions, packed into two by pairing).
- **Thm 2.** Explicit version: from the four functions $`J(LK, KL)`$, $`J(I, S0)`$, $`J(K+KL, I)`$, $`J(\mathrm{sgn} KLK, L)`$ by composition and $`Fx = B^x 0`$.
- **Lemma.** From a single $`A`$, using composition and $`B^x a`$ (any start values $`a`$), every obtainable $`F`$ either
  - is $`A^k`$ ($`k \ge 1`$), or
  - has every value of the form $`A^na`$ for some fixed $`a`$, apart from a finite exceptional set.
- **Thm 3.** No **single** function generates all unary PR functions by composition and $`Fx = B^x a`$.
  - Case analysis: if $`A`$ repeats only finitely many values, $`K`$ is not obtainable. Otherwise $`S`$ is not obtainable.

### [15] R. M. Robinson 1947 — *Primitive recursive functions* (PRF)
Systematic study of restricted recursion schemes.
- **§2 (schemes).** Defines the restricted schemes:
  - **one parameter:** recursion, pure recursion (no $`x`$ in $`B`$), iteration (no $`u`$ in $`B`$), pure iteration ($`F(u,x) = B^x u`$);
  - **no parameter:** recursion ($`F0 = a`$, $`F(x+1) = B(x, Fx)`$) and pure recursion $`Fx = B^x a`$, also with $`a = 0`$ only.
  
  Iteration with $`F(u,0) = Au`$ is as general as $`F(u,0) = u`$.
- **Main table (Theorem of §6).** All PR functions are obtained from the identity, zero and successor functions with substitution and the given scheme, if one adjoins:

  | | one param., recursion | one param., iteration | no parameter (also with $`a = 0`$) |
  |---|---|---|---|
  | mixed | nothing | nothing | $`u+x, Q`$  or  $`\\vert u-x\\vert`$ |
  | pure  | $`P`$ | $`Q`$ | $`u+x, E`$  or  $`\\vert u-x\\vert , Q`$ |
- **§3.** Parameters can be reduced to one using pairing. Iteration with one parameter is enough. This extends Péter's result that one-parameter recursion is enough.
- **§4.** The last parameter can be eliminated. With the special pairing $`J(u,v) = ((u+v)^2+u)^2+v`$ (so $`K = E\lfloor \sqrt{\cdot}\rfloor`$, $`L = E`$), pure recursion without parameter $`B^x 0`$ suffices if $`u+x, u-x, x^2, 0^x, \lfloor x/2\rfloor , \lfloor \sqrt{x}\rfloor`$ are adjoined.
- **§5 Lemma.** This is a weaker table: mixed/no parameter needs $`u+x, u-x`$, and pure needs $`P, Q`$ with one parameter, or $`u+x, u-x, Q`$ with no parameter.
- **§7 Thm 1.** Unary functions obtainable by substitution and $`B^x a`$ can be obtained using substitution only to define unary functions.
- **§7 Thm 2.** If $`u+x`$ is the only multi-argument initial function besides identities and zeros, the unary functions are generated by $`Ax+Bx`$, $`B(Ax)`$, $`B^x a`$. The same holds with $`a = 0`$ only.
- **§7 Thm 3 (Robinson's unary characterisation).** All unary PR functions come from **$`S`$ and $`E`$** by $`Fx = Ax + Bx`$, $`Fx = B(Ax)`$, $`Fx = B^x 0`$. Remark: $`\vert u-x\vert`$, $`\vert Ax - Bx\vert`$ and $`Q`$ can be used in place of $`u+x`$, $`Ax+Bx`$ and $`E`$.
- **§8 (necessity).**
  - Open problems: can $`P`$ be defined by substitution and pure recursion from the identity, zero and successor functions? Can $`Q`$ be defined by pure iteration?
  - Without parameters, *some* function of $`\ge 2`$ variables must be adjoined. It is open whether all *unary* PR functions are obtainable with no adjunction. If $`Q`$ were definable from $`u+x`$ alone, adjoining $`u+x`$ would suffice.
- **§8 Theorem.** Start from the identity, zero and successor functions, $`u+x`$, and any unary functions that are either $`\ge x`$ or bounded. Then pure recursion without parameter yields only functions that are $`\ge x`$ or bounded. So $`u+x, Q`$ is **not** enough; in particular $`P`$ is not definable that way.

### [16] R. M. Robinson 1955 — *Primitive recursive functions II*
Uses the **Cantor** pairing $`2J(u,v) = (u+v)^2 + 3u + v`$, where $`K`$ is the excess over a triangular number.
- **Thm 1.** All unary PR functions come from **$`S`$ and $`K`$** (or **$`S`$ and $`L`$**) by $`Fx = Ax + Bx`$, $`Fx = B(Ax)`$, $`Fx = B^x 0`$. This improves [15] Thm 3 by replacing $`E`$.
  - Proof: define $`I = S^x 0`$, $`0`$, $`\mathrm{sgn}`$, differences via $`K`$, then $`x^2`$.
  - $`Fx = 2x - \lfloor \sqrt{x}\rfloor`$ is the iterate of $`By = Sy + \mathrm{sgn} K S y`$.
  - This gives $`\lfloor \sqrt{x}\rfloor = 2x - Fx`$ and $`E`$.
  - $`K = L(x + 2Lx + 2)`$.
- **Thm 2.** The same holds with $`Fx = J(Ax, Bx)`$ in place of $`Fx = Ax + Bx`$. $`x+y`$ is obtained by substitution from $`J, K, S`$ and $`2x`$.
- **Remark.** In the table of [15], $`(u+x, K)`$, $`(u+x, L)`$, $`(J, K)`$, $`(J, L)`$ can be added as adjunctions for the no-parameter case. J. Robinson [14] removes $`Ax + Bx`$ entirely, at the cost of complicated initial functions.

### [17] Szalkai 1985 — *On the algebraic structure of primitive recursive functions* (Z. Math. Logik 31)
Studies the algebra $`(PR, \circ , \square)`$ of unary PR functions with composition and iteration from 0, $`f^\square (n) = f^n(0)`$.
- **Thm 1.** The only endomorphisms of $`(PR, \circ , \square)`$ are the identity and the constant-zero map. A corollary extends this to richer signatures that can express $`\circ`$ and $`\square`$, e.g. $`(PR, \circ , \square (m))`$ with $`s`$, $`p`$ fixed, and J. Robinson's $`(PR, \circ , +,^{-1})`$.
- **Thms 1A, 1B.** Abstract versions for any structure satisfying axioms (a)–(f).
- **Lemmas 3–6, Thm 2.** For any single function $`a`$, the closure $`\langle a\rangle`$ under $`\circ`$ and $`\square`$ either contains no bijection, or every member is injective or has finite range.
- **Thm 3.** No single PR function generates all monotone increasing PR functions under $`\circ`$ and $`\square`$. In particular **no single function generates PR** ($`id`$ and $`p`$ cannot both be in $`\langle a\rangle`$). This complements J. Robinson's result [14] that two functions suffice.
- Cites Mazur–Robinson, Problem 143 of the Scottish Book (see $`others/`$).

### Thread through the references (relevant to Severin's paper)
- [15] §7 Thm 3 $`\to`$ [16] Thm 1–2 $`\to`$ Severin §6 is the line of **unary bases with $`+`$/$`J`$, composition and $`B^x 0`$**.
- [13] §4 Thms 4–6 $`\to`$ [14] Thms 1–3 is the line **without $`+`$**: two initial functions suffice, and one never does.
- [15] §8 states the open problems on pure recursion / pure iteration ($`P`$, $`Q`$) that Severin's §4–5 revisit (mixed/pure iteration without parameters, $`a`$ fixed vs. variable).
- [6] $`\to`$ [7] $`\to`$ [3] answer Robinson's questions in [15]. [6] needs nothing for one-parameter pure recursion. [7] needs nothing for one-parameter pure iteration, $`x+y`$ for mixed and $`\vert x-y\vert`$ for pure iteration without parameter, and contributes $`Q`$ via a Conway-type map. [3] needs $`\mathbin{\dot-}`$ for pure iteration without parameter, unary case. These are the sources of Severin §4–5 (Lemma 5.5 is [7] Lemma 11, Lemma 5.6 is [7] Lemma 13, Lemma 5.2 is [3] Lemma 7).
- [5] and [10] (Germano–Mazzanti, Mazzanti) are the "programming" line: for-loop iteration $`f \vert g`$ instead of $`F^\square`$, and pairings built from increasing functions.
- [4] and [11] are unary hierarchies built on these schemes (Grzegorczyk-like and Axt-like). [17] is the algebraic side ($`(PR, \circ , \square)`$ has no nontrivial endomorphisms, and no single generator exists).
- [9] and [12] are the growth-rate side: the Grzegorczyk classes and their unary characterisation ($`\mathcal{G}^n`$) via pure iteration, with each iteration climbing one level ([12] Thm 2.3).
