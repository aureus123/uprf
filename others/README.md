# Other references (from the bibliography of Severin's Tesina, UNR 2006)

These are the Tesina references by Axt, Calude, Tatarâm, Georgieva, Gladstone, Mazzanti, Grzegorczyk,
Kleene (1936 only), Mauldin, Naumović, Péter and Szalkai. Keys are the Tesina's own.
Papers that are also references of the 2008 UPRF paper are summarized in [`references/README.md`](../references/README.md).

| Key | Reference | DOI / notes |
|---|---|---|
| Axt65 | P. Axt, *Iteration of primitive recursion*, Z. Math. Logik Grundlagen Math. 11 (1965) 253–255 | doi:10.1002/malq.19650110310 |
| Axt66 | P. Axt, *Iteration of relative primitive recursion*, Math. Ann. 167 (1966) 53–55 | summarized in [references](../references/README.md), ref. [1] |
| Cal81 | C. Calude, *Darboux property and primitive recursive functions*, Rev. Roumaine Math. Pures Appl. 26 (1981) 1187–1192 |  |
| Cal82 | C. Calude, *Note on a hierarchy of primitive recursive functions*, Rev. Roumaine Math. Pures Appl. 27 (1982) 935–936 |  |
| CMT79 | C. Calude, S. Marcus, I. Tevy, *The first example of a recursive function which is not primitive recursive*, Historia Math. 6 (1979) 380–384 (the Tesina says vol. 9) |  |
| CT83 | C. Calude, M. Tatarâm, *Universal sequences of primitive recursive functions*, Rev. Roumaine Math. Pures Appl. 28 (1983) 381–389 |  |
| Geo76a | N. Georgieva, *Another simplification of the recursion scheme*, Arch. Math. Logik 18 (1976) 1–3 | summarized in [references](../references/README.md), ref. [3] |
| Geo76b | N. Georgieva, *Classes of one-argument recursive functions*, Z. Math. Logik Grundlagen Math. 22 (1976) 127–130 | summarized in [references](../references/README.md), ref. [4] |
| Gla67 | M. D. Gladstone, *A reduction of the recursion scheme*, JSL 32 (1967) 505–508 | summarized in [references](../references/README.md), ref. [6] |
| Gla71 | M. D. Gladstone, *Simplifications of the recursion scheme*, JSL 36 (1971) 653–665 | summarized in [references](../references/README.md), ref. [7] |
| GM88 | G. Germano, S. Mazzanti, *Primitive iteration and unary functions*, APAL 40 (1988) 217–256 | summarized in [references](../references/README.md), ref. [5] |
| GM91 | G. Germano, S. Mazzanti, *General iteration and unary functions*, APAL 54 (1991) 137–178 | doi:10.1016/0168-0072(91)90029-L |
| Grz53 | A. Grzegorczyk, *Some classes of recursive functions*, Rozprawy Mat. 4 (1953) 1–44 | summarized in [references](../references/README.md), ref. [9] |
| Kle36a | S. C. Kleene, *General recursive functions of natural numbers*, Math. Ann. 112 (1936) 727–742 |  |
| Kle36b | S. C. Kleene, *A note on recursive functions*, Bull. AMS 42 (1936) 544–546 |  |
| Liu60 | S.-C. Liu, *A theorem on general recursive functions*, Proc. AMS 11 (1960) 184–187 (not in the Tesina's bibliography) | doi:10.1090/S0002-9939-1960-0130175-8 |
| Mau81 | R. D. Mauldin (ed.), *The Scottish Book: Mathematics from the Scottish Café*, Birkhäuser 1981 | 2nd edition: Birkhäuser 2015. Relevant item: Problem 143 (Mazur), with R. M. Robinson's commentary |
| Maz97 | S. Mazzanti, *Iterative characterizations of computable unary functions: a general method*, MLQ 43 (1997) 29–38 | doi:10.1002/malq.19970430104 |
| Maz05 | S. Mazzanti, *Bounded iteration and unary functions*, MLQ 51 (2005) 89–94 | summarized in [references](../references/README.md), ref. [10] |
| Nau83 | J. Naumović, *A classification of the one-argument primitive recursive functions*, Arch. Math. Logik 23 (1983) 161–174 | summarized in [references](../references/README.md), ref. [11] |
| Pét34 | R. Péter, *Über den Zusammenhang der verschiedenen Begriffe der rekursiven Funktion*, Math. Ann. 110 (1934) 612–632 |  |
| Pét35 | R. Péter, *Konstruktion nichtrekursiver Funktionen*, Math. Ann. 111 (1935) 42–60 |  |
| Pét36 | R. Péter, *Über die mehrfache Rekursion*, Math. Ann. 113 (1936) 489–527 |  |
| Sza85 | I. Szalkai, *On the algebraic structure of primitive recursive functions*, Z. Math. Logik Grundlagen Math. 31 (1985) 551–556 | summarized in [references](../references/README.md), ref. [17] |
| Tat03 | M. Tatarâm, *An extension of the double recursion theorem of R. M. Robinson*, Rev. Roumaine Math. Pures Appl. 48 (2003) 105–111 |  |

## Results per paper

Statements only (proofs not checked). Notation as in [`references/README.md`](../references/README.md).

### Axt 1965 — *Iteration of primitive recursion* (Z. Math. Logik 11)
The **Axt hierarchy**: $`K_n`$ = functions needing at most $`n`$ nested applications of the primitive recursion schema. Kleene's schemata (I)–(V); recursion is allowed only on functions from $`K_{n-1}`$.
- **Thm 1.** The Grzegorczyk functions satisfy $`f_n \in K_n`$ ($`f_0 = a+1`$, $`f_1 = b+a`$, $`f_2 = (b+1)(a+1)`$, ...).
- **Thm 2.** $`K_0 \subseteq \mathcal{E}^0`$ and $`K_1 \subseteq \mathcal{E}^1`$; for $`n \ge 2`$, $`K_n \subseteq \mathcal{E}^{n+1}`$ and $`K_n \not\subseteq \mathcal{E}^n`$. The proof constructs a unary $`\gamma_n \in K_n`$ that majorizes $`\lambda a.f_n(k,a)`$ for every $`k`$.
- **Cor.** $`K_n \subsetneq K_{n+1}`$ (proper hierarchy).
- **Thm 3.** For every $`n`$ there is $`m`$ with $`\mathcal{E}^n \subseteq K_m`$.

(The later result $`K_n = \mathcal{E}^{n+1}`$ for $`n \ge 2`$ is due to Müller and Schwichtenberg; see Naumović [11].)

### Calude, Marcus, Tevy 1979 — *The first example of a recursive function which is not primitive recursive* (Historia Math. 6)
A historical note.
- The first recursive but not primitive recursive function is usually credited to Ackermann (1928). The authors show that **G. Sudan** (1927) gave one at the same time.
- Sudan's function arose from Hilbert's continuum programme ("variables of type n"). It is defined by nested recursion over ordinals: $`\psi (a,b,0) = a+b`$, $`\psi (a,b,n+1) = t_c(a, \lambda_m \psi (c,m,n), b)`$, with $`t_c`$ an iteration operator.
- Sudan showed that every ordinal $`< \omega^\omega`$ is reachable with ordinary induction (type 1), while $`\omega^\omega`$ needs a type-2 variable (transfinite induction).
- Sudan and Ackermann were both with Hilbert in Göttingen (1922–25), and Ackermann's paper mentions Sudan's forthcoming work. Hilbert cited only Ackermann, probably because he preferred number-theoretic over ordinal functions.
- Both functions are compared in a common notation. Sudan's restricted to finite arguments is the "Sudan function" (cf. Dima, ref. [2] of the UPRF paper).

### Calude 1981 — *Darboux property and primitive recursive functions* (Rev. Roumaine Math. Pures Appl. 26, 1187–1192)
Transfers the **Darboux (intermediate value) property** to hierarchies of PR functions. The idea comes from Marcus's version for formal languages [8].
- **Definitions.**
  - For a hierarchy $`C_1 \subseteq C_2 \subseteq \dots`$, $`f`$ has *type m* if $`f \in C_m \setminus  C_{m-1}`$.
  - The hierarchy has the *Darboux property (a.e.)* if, whenever $`g \le f`$ a.e. with $`g`$, $`f`$ of types $`m < n - 1`$, every type $`j`$ strictly between $`m`$ and $`n`$ contains some $`h`$ with $`g \le h \le f`$ a.e.
- **The four unary hierarchies compared.**
  - Ackermann–Péter $`A_n = [{S, a_n}; unary composition, \mathbin{\dot-}, limited iteration]`$, with $`a_0 = x+1`$, $`a_{n+1}(0) = a_n(1)`$, $`a_{n+1}(x+1) = a_n(a_{n+1}(x))`$. This is Georgieva's hierarchy, ref. [4] of the UPRF paper.
  - Grzegorczyk $`G_n`$, Ritchie $`R_n`$, and the Sudan hierarchy $`S_n`$ (Dima, ref. [2] of the UPRF paper).
- **Thm 1** (from [1–3]). $`G_{k+1} = R_{k+1} = S_k`$, and for unary functions $`A_{k+1} = G^1_{k+1} = R^1_{k+1} = S^1_k`$. $`A_3`$ is the Kalmár elementary functions.
- **Prop 1.** $`S^1_2`$ is the smallest class containing $`S`$, $`E`$ and $`s_2(x,x)`$ that is closed under $`+`$, $`\cdot`$, composition and limited iteration.
- **Prop 2.** In the Ackermann–Péter hierarchy:
  - the inclusions are proper;
  - $`f \in A_n`$ implies $`f < a_{n+1}`$ a.e.;
  - $`\bigcup A_n`$ = the unary PR functions.
- **Lemma 1 / Cors 1–2.** For $`m \ge 3`$, $`A_m`$ is closed under definition by cases, $`f = u`$ if $`v(x) = 1`$ else $`0`$. The construction is $`f = \lfloor h((2u+2) \mathbin{\dot-} \overline{\mathrm{sg}}(v))/4\rfloor`$ with $`h(x) = 2x \mathbin{\dot-} (2^{x+rm(x,2)+1} \mathbin{\dot-} 2^{x+1})`$, Georgieva's trick with $`\mathbin{\dot-}`$. Finite modifications stay in $`A_m`$.
- **Thm 2.** The Ackermann–Péter hierarchy has the Darboux property a.e. (Lemma 2 interpolates with $`\mathrm{min}(a_{i+m}, h_{i+1})`$.) **Remark 3:** the property fails with strict inequalities.
- **Thm 3 / Cor 4.** Via unary associates $`f*(x) = f(M_1^k(x), \dots , M_k^k(x))`$ (Cantor pairing), the Ritchie, Grzegorczyk and Sudan hierarchies also have the Darboux property a.e.
- **Open problems (§4).**
  - Do the hierarchies have the plain (everywhere) Darboux property?
  - Left and right Darboux properties for the initial classes.
  - Darboux property of the structural hierarchies under i.o. majorization.
  - Hierarchies of recursive functions under majorization in a Blum complexity measure.
- Dima's paper [2] is cited here as N. Dima, *Funcţia lui Sudan este universală pentru clasa funcţiilor primitiv recursive*, St. cerc. mat. 33 (1981) 59–67 (in Romanian).

### Calude 1982 — *Note on a hierarchy of primitive recursive functions* (Rev. Roumaine Math. Pures Appl. 27, 935–936)
A two-page correction note to Ritchie 1965 ([12] in [`references/`](../references/README.md)) and Georgieva 1976 ([4]).
- **Ritchie's Thm 2.3** (iterating a function of $`R*_n`$ lands in $`R*_{n+1}`$). The proof only shows that the iterate is *bounded* by a function of $`R_{n+1}`$. Membership would need $`R*_n \subseteq R*_{n+1}`$, which is not established at that point.
  - **Fix.** Redefine $`R*_n`$ cumulatively, with $`S`$, $`E`$, $`\lfloor \sqrt{x}\rfloor`$ and $`r_i(x,x)`$ for all $`i = 2, \dots , n`$. Then Ritchie's Thms 2.3, 3.3 and 3.4 go through.
  - **Open problem:** is the original $`R*_n`$ equal to the new one?
- **Georgieva's Thm 3.1** ($`G^1_{n+1} = R^1_{n+1}`$). The inclusion $`G \subseteq R`$ is fine. The converse relies on $`r_n(x,x) = p_{n-1}(x)`$, which fails ($`n = 3`$: $`x^x`$ vs $`2^x`$). The real difficulty is to obtain the diagonal $`r_n(x,x)`$ in $`G_n`$, since it cannot be reached directly by iterating $`r_{n-1}`$. Calude suggests restating Ritchie's Thms 3.3–3.4 for the classes $`G_n`$.

### Calude, Tatarâm 1983 — *Universal sequences of primitive recursive functions* (Rev. Roumaine Math. Pures Appl. 28, 381–389)
Shows that there are infinitely many **universal sequences**, i.e. sequences of functions whose hierarchies generate Grzegorczyk's hierarchy. This answers, in Ritchie's setting, a theme of Verbeek.
- **Setup.**
  - Ritchie's two-argument functions are read as a double sequence of unary functions $`f_{n;x}(y) = f_n(x, y)`$ ($`f_{0;x} = x+1`$, $`f_{1;x} = x+y`$, $`f_{2;x} = xy`$, $`f_{n+1;x}(0) = 1`$, ...). Monotonicity facts 1)–6) are restated.
  - $`R_n`$ is Ritchie's class and $`R^1_n`$ its unary part. $`G_n`$ is Georgieva's class $`[S, g_n; \mathbin{\dot-}, \circ , limited iteration]`$, and $`R^1_n = G_n`$ for $`n \ge 3`$.
- **$`C_{n,m}`$** = the smallest class of unary functions containing $`S`$, $`E`$, $`\lfloor \sqrt{x}\rfloor`$ and $`f_{n;m}`$, closed under $`+`$, $`\cdot`$, composition and (pure) limited iteration.
- **Thm 1.** $`C_{n,m}`$ contains:
  - $`I`$, the constants, $`M_i^p`$, $`\mathrm{sg}`$, $`\overline{\mathrm{sg}}`$ and small $`f_{i;j}`$;
  - Robinson's pairing $`J(x,y) = ((x+y)^2 + x)^2 + y`$, $`K = E\lfloor \sqrt{\cdot}\rfloor`$, $`L = E`$.
  It is closed under pairing and conditional expressions.
- **Lemma 1, Thm 2.** $`(f_{m;n}(x))^2 < f_{m+1;n}(x)`$, and each $`f \in C_{m,n}`$ is bounded a.e. by some $`f_{m;n}^l`$.
- **Props 1–5, Cors 1–2.** $`f_{m+1;n} \notin C_{m,n}`$, so $`C_{m,n} \subsetneq C_{m+1,n}`$. Also $`C_{m,n} \subseteq C_{m,n+1}`$ and $`C_{m,n} \subseteq R^1_m`$. Unlimited iteration climbs one level.
- **Thm 3.** For $`n \ge 3`$: $`R^1_n = G_n = C_{n,2}`$. The proof shows $`C_{n,2}`$ is closed under arithmetic difference and contains $`g_n`$. This completes the proof Calude 1982 found missing.
- **Cor 3.** $`C_{n,m} = R^1_n`$ for all $`n \ge 3`$ and $`m \ge 2`$. So every row $`(f_{n;m})_n`$ of Ritchie's double sequence is universal. Remark: $`G_2 = G_1 = C_{0,2} = C_{1,3}`$.
- **Open problems.**
  - Conjecture: the same holds for Grzegorczyk's and Sudan's sequences, and for word functions.
  - The topological size of the set of universal sequences.
  - A double sequence refining Grzegorczyk's hierarchy.
  - The closure of $`S`$, $`\lfloor \sqrt{x}\rfloor`$, $`E`$, $`f_{n;m}`$ under composition and pure *limited* iteration only, without $`+`$ and $`\cdot`$.

### Tatarâm 2003 — *An extension of the double recursion theorem of R. M. Robinson* (Rev. Roumaine Math. Pures Appl. 48, 105–111)
R. M. Robinson (1948, *Recursion and double recursion*) defined, by double recursion, a binary non-PR function that generates all **unary** PR functions. Tatarâm extends this to $`m`$-ary PR functions.
- **Pairings (Def 1).** $`J(u, v, w_1\dots w_m) = ((\dots ((u+v+w_1+\dots +w_m)^2 + w_m)^2 + \dots + w_1)^2 + u)^2 + v`$, with inverses $`K`$, $`L`$, $`H_i`$ built from $`E`$ and $`e(z) = \lfloor \sqrt{z}\rfloor`$. Lemma 1 gives their basic properties.
- **Def 2, Thm 1.** An explicit sequence $`F_n(\bar{x})`$ of PR functions generates $`PR^{(m)}`$. It starts with $`F_0 = 0`$, $`F_1 = x_1`$, $`F_2 = x_1+1`$, $`F_3 = E(x_1)`$, and then sums, differences, compositions and pure iteration $`F*`$. The proof uses Robinson's result that unary PR functions come from successor, excess over a square, sum, composition and pure iteration ([15] §7 Thm 3).
- **Lemma 2.** $`F_n(\bar{x}) = D(2I(n, \bar{x}))`$ for a single unary PR function $`D`$ defined by course-of-values-like recursion (Defs 3–6, Prop 1: $`D(z+1) = D(B(z, Dz))`$).
- **§3 (Robinson's theorem revisited).**
  - A binary function $`G(n, x)`$ is defined by **double recursion** (Def 5): $`G(0,x) = Ax`$, $`G(n+1,0) = 0`$, $`G(n+1,x+1) = G(n, B(x, G(n+1,x)))`$.
  - Prop 2: $`G(n, x)`$ approximates $`Dx`$ as $`n`$ grows ($`G(n,x) = Dx`$ for $`x \le n`$-ish).
- **Thm 2.** For every $`f \in PR^{(m)}`$ there is $`n`$ with $`f(\bar{x}) = G(n, T(n, \bar{x}))`$, where $`T`$ is a fixed PR function. So **$`G`$ generates all PR functions of any arity by double recursion**.

### Germano, Mazzanti 1991 — *General iteration and unary functions* (APAL 54)
The analogue of [5] (the 1988 paper) for **general computable** unary functions $`\mathrm{comp}(\mathbb{N},\mathbb{N})`$. It uses the *while-do* operator $`f / g`$ ("while $`f(x) \ne 0`$ do $`x := g(x)`$") instead of the for-loop $`f \vert g`$.
- **Method.** Sequence functions are simulated by unary functions relative to a pairing (Thm 0.12).
- **Thm 2.1–2.3.** For any pairing $`J`$: $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(O_J, S, P*_J, K_J, L_J, *^jf, f\circ g, f / g)`$ and variants (pairing / star / composition only).
- **Thm 3.1 (Cantor-like pairing $`R`$).** $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E, f + g, f\circ g, f / g)`$. This improves J. Robinson's famous $`\mathrm{clos}(S, E, f+g, f\circ g, f^{-1})`$ ([13]) by replacing inversion, which has no programming counterpart, with while-do.
- **Thm 3.2.** $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(C, S, \mathrm{quad},^+f, f\circ g, f / g)`$.
- **Thm 3.3.** A version with composition only.
- **Gödel-like pairing $`G(n,m) = 2^n3^m`$.**
  - **Thm 4.1:** $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(\mathrm{pow}[2], \mathrm{exp}[2], \mathrm{div}[2], \mathrm{div}[3], f\cdot g, f\circ g, f / g)`$.
  - **Thm 4.2:** the same with a "times" operator $`*f`$.
  - **Thm 4.3:** $`\mathrm{clos}(\mathrm{pow}[2], \mathrm{exp}[2], \mathrm{mult}[2], \mathrm{mult}[3], \mathrm{div}[2], \mathrm{div}[3], f\circ g, f / g)`$.
- **Thm 5.1.** $`\mathrm{comp}(\mathbb{N},\mathbb{N}) \setminus  \mathrm{prim}(\mathbb{N},\mathbb{N}) \ne \emptyset`$, via an enumeration built on $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(I, S, P, I(f,g,h))`$ from [5].
- **Thm 5.3.** A programming-oriented **Kleene normal form** for unary functions: $`f = \mathrm{init}[\varphi f] \circ (K / \mathrm{step}_\varphi) \circ L`$, with $`\mathrm{init}`$, $`\mathrm{step}`$, $`L`$ primitive computable. In words, a single while-loop suffices.
- **Errata.** Corrects Theorem 0.6 of [5] (the 1988 paper).

### Kleene 1936a — *General recursive functions of natural numbers* (Math. Ann. 112)
The foundational paper on Herbrand–Gödel **general recursive** functions (definitions by systems of equations).
- **Equivalent definitions.** Def. 2a/2b of general recursiveness are shown to be equivalent (Thms VI, IX). Gödel numbering of systems of equations and primitive recursive predicates for derivations are used.
- **Thm IV (normal form).** Every general recursive function can be written $`\psi (\varepsilon y[R(x,y)])`$, where $`\psi`$ is primitive recursive, $`R`$ is a primitive recursive relation, and $`\forall x \exists y R(x,y)`$.
- **Thm V.** If $`R`$ is recursive and $`\forall x \exists y R(x,y)`$, then $`\varepsilon y[R(x,y)]`$ is recursive. So the general recursive functions are the closure of the primitive recursive ones under substitution and the (regular) $`\mu`$-operator.
- **Thm X (diagonalization).** For any recursive $`\theta`$ whose values are all indices of total recursive functions, there is an index $`f`$ of a total recursive function that is not in the range of $`\theta`$. So diagonalizing a recursively listed sequence of recursive functions stays inside the class.
- **Thm XI.** The indices of total recursive functions ($`\forall x \exists y T_1(z,x,y)`$) are not recursively enumerable.
- **Thm XII.** That set of indices is not recursive.

### Kleene 1936b — *A note on recursive functions* (Bull. AMS 42)
- **Theorem.** The general recursive functions are exactly the functions obtained from **$`x + y`$, $`x \cdot y`$ and the Kronecker delta $`\delta_x^y`$** by substitution and the (regular) operator $`\varepsilon y[p(x,y) = 0]`$. No primitive recursion is needed.
- **Proof.** It adapts Gödel's argument that every primitive recursive relation is arithmetic, using Gödel's $`\beta`$-function and the Chinese remainder theorem. The normal form theorem of Kleene 1936a then gives the result.

### Liu 1960 — *A theorem on general recursive functions* (Proc. AMS 11, 184–187)
A normal form for general recursive functions using **ordinal recursion of type $`\omega *`$* with no outer function. It improves Myhill (1953) and Routledge (1953, Thm 4).
- **Theorem.** Every general recursive $`f(n)`$ can be written $`f(n) = g(2^n)`$, where $`g`$ is defined by $`g(0) = 0`$, $`g(n') = \theta (n', g(\delta (n')))`$. Here $`\theta`$ and $`\delta`$ are primitive recursive, and $`\delta (n') \prec n'`$ for a **primitive recursive** well-ordering $`\prec`$ of $`\mathbb{N}`$ of order type $`\omega`$.
- **Comparison with earlier results.**
  - Routledge's version needs a well-ordering defined by general recursive processes.
  - Kleene's sharpening of Myhill gives $`f(n) = U(g(2^n))`$ with an outer function $`U`$; Liu removes $`U`$.
  - By Routledge (§§8–9) the form is best possible: the $`2^n`$ cannot be dropped to get $`f(n) = g(n)`$.
- **Proof.**
  - Start from Kleene's normal form $`f(n) = K(\mu y[T(n,y) = 0])`$ with $`\forall x \exists y T(x,y) = 0`$ (here $`K`$, $`T`$ are Liu's names for Kleene's primitive recursive $`U`$, $`T`$).
  - Define $`g`$ on codes $`2^x3^y`$. If $`T(x,i) \ne 0`$ for all $`i \le y`$, then $`g(2^x3^y) = g(2^x3^{y+1})`$; at the first zero of $`T`$, $`g(2^x3^y) = K(y)`$; otherwise $`g = 0`$. So $`g(2^n) = g(2^n\cdot 3) = \dots = K(q_n)`$ with $`q_n = \mu y[T(n,y) = 0]`$.
  - Recast with primitive recursive predicates $`A`$, $`B`$ as $`g(n') = \overline{\mathrm{sg}}(A(n'))\cdot g(\overline{\mathrm{sg}}(A(n'))\cdot 2^{(n')_0}3^{(n')_1+1}) + \overline{\mathrm{sg}}(B(n'))\cdot K((n')_1)`$.
  - The "search runs" $`2^n, 2^n\cdot 3, \dots , 2^n\cdot 3^{q_n}`$ are arranged in a primitive recursive order $`\prec`$ (via a function $`H(x)`$ = the nearest run head below $`x`$). Each run is placed *before* its head, in reverse. This makes the search step $`\delta (n') = 2^{(n')_0}3^{(n')_1+1}`$ decreasing in $`\prec`$, and $`\prec`$ has type $`\omega`$.
- **Relevance to UPRF.** None directly; it is about general (not primitive) recursion. It belongs to the same "simplest schema plus one fixed coding" tradition: compare $`f(n) = g(2^n)`$ with Kleene's normal form, Kleene 1936a above, and Germano–Mazzanti 1991's single while-loop normal form.

### Mauldin (ed.) — *The Scottish Book*, 2nd ed. (2015): Problem 143 (Mazur)
- **The problem.** Let $`K`$ be the least class of two-variable functions containing $`x, y, 0, x+1, xy`$, closed under substitution and under the one-variable recursion $`f(0,y) = 1`$, $`f(x+1,y) = a(x, f(x,y))`$. Does $`K`$ contain $`d(x,y) = \mathrm{sgn}\vert x - y\vert`$?
- **R. M. Robinson's commentary (in this edition): yes.** In fact $`K`$ is exactly the PR functions of two variables.
  - Constructions:
    - with start value $`a = 1`$, products give $`c^x`$, $`\mathrm{sgn}`$ and $`P`$;
    - addition of functions with disjoint supports gives definition by cases;
    - the "distance to the next power of 6" function $`R`$ gives $`x = y`$ iff $`2^x\cdot 3^y`$ is a power of 6;
    - this yields $`\lfloor \sqrt{x}\rfloor`$, $`Q`$, $`\lfloor \mathrm{log}_2 x\rfloor`$, and $`x + y = \lfloor \mathrm{log}_2(2^x\cdot 2^y)\rfloor`$.
  - With $`a = 0`$ only monotone functions arise, unless $`0^x`$ is adjoined.
  - Gladstone's [7] §4 needs only $`a \in {0, 1, 2}`$, and $`a = 1`$ alone suffices.
- Cited by Szalkai [17].

### Mazzanti 1997 — *Iterative characterizations of computable unary functions: a general method* (MLQ 43)
Generalizes [5] (the 1988 paper) and Germano–Mazzanti 1991 to an infinite family of pairings built from any **positively increasing** $`h \in \mathrm{prim}(\mathbb{N},\mathbb{N})`$.
- **Definitions.**
  - $`h_\Sigma (n) = \Sigma_{r<n} h(r)`$, $`\mathrm{rad}_h`$, $`E_h`$ = excess over the preceding $`h_\Sigma`$-value, $`next_h`$, $`prec_h`$.
  - $`h = 2x+1`$ gives $`x^2`$, $`\lfloor \sqrt{x}\rfloor`$ and $`E`$.
  - $`h = S`$ gives triangular numbers, the triangular root and the excess over triangles.
- **Lemma 2.2.** $`G_h(n,m) = h_\Sigma (n+m) + n`$ and $`J_h(n,m) = h_\Sigma (G_h(n,m)) + m`$ are pairings. $`G_{S+I}`$ is Robinson's $`(m+n)^2 + n`$; $`G_S`$ is the Cantor pairing.
- **Thm 2.3.** A test for "$`m`$ is an $`h_\Sigma`$-value", via $`F_h(n,m) = E_h m + E_h(m + hn) + E_h(m + hn + h(\mathrm{rad} m + 1))`$. This avoids Euler's four-squares theorem, which earlier proofs used.
- **Thm 3.3 / Cors 3.1–3.3.** $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E_h, h, f+g, f\circ g, f / g)`$. In particular:
  - $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E_S, f+g, f\circ g, f / g)`$ (excess over triangles);
  - $`\mathrm{comp}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E_{S+I}, f+g, f\circ g, f / g)`$ (excess over squares).
- **Thm 4.3 / Cors 4.1–4.3.** The primitive analogue with the for-loop $`f \vert g`$. In particular $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E_h, h, f+g, f\circ g, f \vert g)`$, and so $`\mathrm{prim}(\mathbb{N},\mathbb{N}) = \mathrm{clos}(S, E_S, f+g, f\circ g, f \vert g) = \mathrm{clos}(S, E_{S+I}, f+g, f\circ g, f \vert g)`$. These are Robinson-type bases ([15] §7) with the for-loop operator.

### Péter 1934 — *Über den Zusammenhang der verschiedenen Begriffe der rekursiven Funktion* (Math. Ann. 110) ("I")
Compares several notions of **one-variable ("simple") recursion** with primitive recursion (in Gödel's sense).
- **Main theorem.** Adding **course-of-values recursion** ($`\varphi (n+1)`$ built from $`\varphi (0), \dots , \varphi (n)`$) and **nested simple recursion** does not enlarge the class of primitive recursive functions. In nested recursion the parameters are substituted, possibly with nested occurrences of $`\varphi (n, \dots)`$, as in Hilbert's scheme.
- **Parameter elimination.** The same class is obtained with the simplest parameter-free recursion $`\varphi (0) = k`$, $`\varphi (n+1) = \beta (n, \varphi (n))`$, provided some two-variable functions are taken as initial functions.
- **Contrast.** Multiple recursion (on several variables at once) leads outside the class (Ackermann). This is treated in the sequels II and III.

### Péter 1935 — *Konstruktion nichtrekursiver Funktionen* (Math. Ann. 111) ("II")
- **§1.** By I, nested recursion reduces to primitive recursion of the form $`\varphi (0,a) = \alpha (a)`$, $`\varphi (n+1,a) = \beta (n, a, \varphi (n,a))`$. Using prime-exponent coding ($`2^r\cdot 3^s`$), this in turn reduces to recursions **without parameters**, $`\psi (0) = k`$, $`\psi (n+1) = \beta (n, \psi (n))`$, plus some two-place initial functions.
- **§2.** Using this parameter-free form, the (primitive) recursive functions are **enumerated** by a function defined by a single **double recursion**. Diagonalization then gives an explicitly defined non-primitive-recursive function, a new proof that multiple recursion leads outside the class.
- **§3.** A simplified, smoothed version of **Ackermann's example**, with a direct proof that it is not primitive recursive. This is the origin of the modern Ackermann–Péter function.

### Péter 1936 — *Über die mehrfache Rekursion* (Math. Ann. 113) ("III")
Studies **k-fold (multiple) recursion**, recursion on $`k`$ variables at once in lexicographic order.
- Multiple recursions reduce to simple ones if Hilbert's second level (recursion on functionals) is allowed.
- Every k-fold recursion reduces to a normal ("primitive") form with no parameters and only two-level nesting (§§1–2; Kalmár's prime-factor ordering simplifies I's combinatorics).
- **§3.** A k-fold recursion **without nesting** does not lead outside the primitive recursive (1-recursive) functions. Hence nesting cannot be eliminated for any $`k \ge 2`$ (Ackermann).
- **§4.** **Hierarchy theorem:** (k+1)-fold recursion leads outside the k-recursive functions for every $`k`$. The proof enumerates the k-recursive functions by a single (k+1)-fold recursion and diagonalizes, generalizing Ackermann's theorem.
