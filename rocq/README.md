# Rocq + MathComp/ssreflect formalization

Formalization of Section 6 of D. E. Severin, *Unary primitive recursive functions*
(J. Symbolic Logic 73(4), 2008), including R. M. Robinson's theorem and Lemma 3.3, and of the
open questions answered in the root README (§2, including §2.3 on general recursive functions).

**Naming:**
- `funX` is the function X of the paper, and `opX` an operator;
- `exprX` is the expression that the paper writes as `X ≡ …`;
- `X_expr` / `exprX_val` / `X_in` are the lemmas saying, respectively, what an expression
  computes, its value at a point, and membership in the closure.

## Requirements

- **Rocq 9.3** (the Rocq Prover): <https://rocq-prover.org>.
- **MathComp 2.6** (`rocq-mathcomp-ssreflect`).
- **mczify** (`coq-mathcomp-zify`), so that `lia` and `nia` work on ssreflect's natural numbers.

## Installation and build

With opam (<https://opam.ocaml.org>):

```sh
opam switch create uprf ocaml-base-compiler.5.3.0     # optional: a dedicated switch
eval $(opam env --switch=uprf)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-mathcomp-ssreflect coq-mathcomp-zify
```

Then build (about 1 min):

```sh
./build.sh
```

## Files

| File | Lines | Content |
|---|---|---|
| `theories/Basic.v` | 221 | Section 2 functions and operators; Cantor A, V, K, L, J; bases; `Clos` (inductive); Prim(ℕ,ℕ) (`PrimNN`, inductive); `suitable`; simulation and soundness lemmas; arithmetic facts |
| `theories/Prim.v` | 175 | the functions and operators of the paper are primitive recursive (bootstrapping +, ∸, ×, the equality test, √, E, Hf, iteration) |
| `theories/Tactics.v` | 160 | Ltac2 automation: `clos_solve`, `sound`, `simulate` (see below) |
| `theories/Sec6.v` | 353 | the basis ⟨1, E, F⁺, FG, F^□⟩, first functions, Definition 6.1, Lemmas 6.2–6.6 |
| `theories/Robinson.v` | 232 | `PrimNN_sub_C6`; Robinson's basis generates the closure |
| `theories/Thm67.v` | 62 | `Theorem_6_7`, `Robinson_1947_sec7_thm3`, `Lemma_3_3`, `Theorem_6_7_via_L33` |
| `theories/Thm68.v` | 192 | `Theorem_6_8` |
| `theories/Rem69.v` | 161 | `Remark_6_9_I`, `_II`, `_III` |
| `theories/ExtA.v` | 359 | open question of Remark 6.9: ⟨X, F^+, FG, F^□(a)⟩ is suitable for every a ≥ 1 and X ∈ {E, K, L} (`Ext_a_E`, `Ext_a_K`, `Ext_a_L`, `Ext_a_all`) |
| `theories/ExtVb.v` | 154 | ⟨E, F^+b, FG, F^□⟩ with F^+b(x) = F(x) + x + b is suitable iff b ≥ 1 (`Ext_Vb`, `Ext_Vb_0`, `Ext_Vb_iff`) |
| `theories/ExtGR.v` | 957 | README §2.3: the inversion `opInv`, the tactics `inv_eq` and `eval_at`, the generic lemmas `sub_inv_surj` and `sub_inv_val` (see below); ⟨1, X, F^+, FG, F^-1⟩ generates J. Robinson's closure ⟨S, E, F + G, FG, F^-1⟩ (`GR_E_eq_JR`, `GR_K_eq_JR`, `GR_L_eq_JR`, `Ext_GR`); without 1 it does not (`Ext_GR0`); 1 and S are interchangeable (`GRS_eq_GR`, `Ext_GRS`) |
| `theories/ExtGRb.v` | 567 | ⟨X, F^+b, FG, F^-1⟩ generates the general recursive functions iff b ≥ 1 (`Ext_GRb_iff`) |
| `theories/ExtCn.v` | 252 | any constant n̄ in place of 1: ⟨n̄, X, F^+, FG, F^□⟩ is suitable iff n ≥ 1 (`Ext_Cn_suitable`), and ⟨n̄, X, F^+, FG, F^-1⟩ generates the general recursive functions iff n ≥ 1 (`Ext_GRCn`) |

## Status

Complete, with no `Admitted`. Section 6 and the questions of §2.1–2.2 use only functional
extensionality (checked with `Print Assumptions`).

For §2.3:
- The inversion `opInv` must decide whether a function is onto. So it uses the classical axioms
  of `ClassicalEpsilon`: excluded middle and indefinite description.
- J. Robinson's theorem (1950, §4, Theorem 3) is a hypothesis `Robinson_1950_sec4_thm3` of the
  section `Robinson_1950`, used by `Ext_GR`, `Ext_GRS`, `Ext_GRb_iff` and `Ext_GRCn`.

## Proof automation (`Tactics.v`, Ltac2)

Three mechanisms recur throughout the proofs. Each one is a generic Ltac2 tactic, callable
from ssreflect scripts through a Ltac1 wrapper.

- **`clos_solve`** proves a membership `Clos B F` for any basis `B`. It decomposes `F` by its
  syntactic head and tries, in order:
  1. a hypothesis;
  2. a hypothesis or registered lemma used as a rule (for example `exprMinusI_in`);
  3. an initial function of `B`;
  4. a binary operator of `B`;
  5. a unary operator of `B`.

  Membership in the basis is decided by syntactic comparison, so no conversion between
  function terms is attempted (such conversions can be very slow here). Lemmas are registered
  with `Ltac2 Set clos_hints as prev := fun () => constr:(lemma) :: prev ()`.
- **`sound`** proves the soundness of a closure: `clos_sound`, a case analysis of the basis,
  and the hint database `prim`. It leaves open the cases it cannot solve.
- **`simulate S`** proves `suitable B` from a suitable basis `S`. It applies
  `suitable_by_simulation`, solves every case with `clos_solve`, and closes soundness with
  `sound`.

For §2.3, `ExtGR.v` adds:

- **`inv_eq h`** (Ltac2) proves `opInv F x = v`, where `h : surj F`, through `opInv_eqI`. It
  leaves two goals: `F v = x`, and the minimality `forall y, F y = x -> v <= y`. Each is tried
  with `reflexivity` and `lia`, and is left to the user if these fail. For `opInv F = G`, apply
  `functional_extensionality` first. Example: `Kinv_eq_Z`.
- **`eval_at`** (Ltac2) unfolds the operators and the basic functions, then tries `lia` and
  `nia`. (`eval` is a reserved word in Rocq.)
- **Subtraction by inversion** is the generic pair `sub_inv_surj` / `sub_inv_val`, from a
  decomposition y = base(t) + X(y) with X(y) ≤ bound(t). `E_sub_inv` and `K_sub_inv` are
  instances of it.

With them, most membership lemmas and all simulation proofs take one line. For example,
Remark 6.9 (III) is `by simulate Remark_6_9_II` once `K` and `1` are known to be in the
closure.

## Notes

- **Prim(ℕ,ℕ) is defined here.** Neither the Rocq standard library nor MathComp has primitive
  recursive functions. `PrimNN` is therefore defined as the standard characterization of the
  unary primitive recursive functions through Cantor's pairing: $`0`$, $`S`$, $`K`$, $`L`$,
  closed under composition, pairing $`J(F,G)`$ and the unary recursion operator.
  - Robinson's theorem is then an induction on `PrimNN`.
  - The soundness direction needs the bootstrapping in `Prim.v`.
- **Pitfalls:**
  - `\o` associates to the left.
  - ssreflect's `//` and `/=`, applied to goals that mention √ or the Cantor functions, make
    Rocq try to compute and effectively hang. Use explicit `rewrite /f` + `cbv beta`, and pass
    side conditions as arguments.
  - `have := lemma` pushes the fact onto the goal; use `have ? := lemma` to put it in the
    context.
  - `have ... by tac1; tac2` makes `tac2` part of the `by`.
