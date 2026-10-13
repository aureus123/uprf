(* Theorem 6.8: the bases <1, K, F^+, FG, F^box> and <1, L, F^+, FG, F^box> are suitable
   (K and L are the inverses of the Cantor pairing function). *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* a basis <1, G, F^+, FG, F^box> *)
Definition basis1 (G : ufun) : basis :=
  Basis (fun F => F = cst 1 \/ F = G) (fun u => u = opPlusI \/ u = opBox) (fun b => b = comp).

Section Basis1.
Variable G : ufun.
Notation C := (Clos (basis1 G)).

Lemma C1_S : C funS. Proof. by rewrite -S_expr; clos_solve. Qed.
Lemma C1_Sgn : C funSgn. Proof. by rewrite -Sgn_expr; clos_solve. Qed.

(* the closure is sound when G is primitive recursive *)
Lemma C1_sound : PrimNN G -> forall F, C F -> PrimNN F.
Proof. by move=> hG; sound. Qed.

(* it is suitable as soon as it simulates F *)
Lemma suitable1 : PrimNN G -> C funE -> suitable (basis1 G).
Proof. by move=> hG hE; simulate Theorem_6_7. Qed.

End Basis1.

(** * The basis F' = <1, K, F^+, FG, F^box> *)

(* auxiliary functions of the proof (Robinson [16, p. 664]):
   Y(x) = 2x - Rt(x) and Z(x) = x(x+3)/2 = A(x) + x *)
Definition funY : ufun := fun x => 2 * x - funRt x.
Definition funZ : ufun := fun x => funA x + x.

Lemma funA1 : funA 1 = 1. Proof. by have := two_funA 1; lia. Qed.
Lemma funA0 : funA 0 = 0. Proof. by have := two_funA 0; lia. Qed.

Lemma funK1 : funK 1 = 0.
Proof. by have := funK_diag (k := 0) (t := 1) isT; rewrite funA1. Qed.

(* Z == (S S K^+)^box *)
Lemma Z_expr : opBox (funS \o funS \o opPlusI funK) = funZ.
Proof.
apply: functional_extensionality; elim=> [|n ih]; first by rewrite /funZ funA0.
rewrite opBoxS ih /comp /funS /opPlusI /funZ.
by rewrite (funK_diag (k := n) (t := n)) // funA_succ; lia.
Qed.

(* Robinson's formula: K((a + b)(a + b + 3)/2 + 2a + 3) = a - b if a >= b *)
Lemma robinson_diff_K a b : b <= a -> funK (funZ (a + b) + 2 * a + 3) = a - b.
Proof.
move=> h; have e : funZ (a + b) + 2 * a + 3 = funA (a + b).+2 + (a - b).
  by rewrite /funZ !funA_succ; lia.
by rewrite e funK_diag //; lia.
Qed.

(* I - F == K S S S ((Z F^+)^+)^+ (if x >= F(x)) and
   D - F == K S S S ((((Z (F^+)^+)^+)^+)^+)^+ (if 2x >= F(x)) *)
Definition exprIminusF (F : ufun) : ufun :=
  funK \o funS \o funS \o funS \o opPlusI (opPlusI (funZ \o opPlusI F)).

Definition exprDminusF (F : ufun) : ufun :=
  funK \o funS \o funS \o funS \o
    opPlusI (opPlusI (opPlusI (opPlusI (funZ \o opPlusI (opPlusI F))))).

Lemma exprIminusF_val F x : F x <= x -> exprIminusF F x = x - F x.
Proof.
move=> h; rewrite -robinson_diff_K // /exprIminusF /comp /funS /opPlusI.
by rewrite (addnC (F x)); congr funK; lia.
Qed.

Lemma exprDminusF_val F x : F x <= 2 * x -> exprDminusF F x = 2 * x - F x.
Proof.
move=> h; rewrite -robinson_diff_K // /exprDminusF /comp /funS /opPlusI.
have -> : F x + x + x = 2 * x + F x by lia.
by congr funK; lia.
Qed.

(* Y == ((Sgn K)^+ S)^box; the key fact is that Y(n) + 1 is triangular iff n + 1 is a square *)
Lemma funRt_le n : funRt n <= n.
Proof. by have := funRt_sq_le n; nia. Qed.

Lemma Y_add n : funY n + funRt n = 2 * n.
Proof. by have := funRt_le n; rewrite /funY; lia. Qed.

Lemma Y_step_square n : (funRt n).+1 * (funRt n).+1 = n.+1 -> funK (funY n).+1 = 0.
Proof.
set r := funRt n => h; have ya := Y_add n; have a := two_funA (2 * r + 1).
have -> : (funY n).+1 = funA (2 * r + 1) + 0 by rewrite -/r in ya; nia.
by rewrite funK_diag.
Qed.

Lemma Y_step_nonsquare n : (funRt n).+1 * (funRt n).+1 <> n.+1 -> funK (funY n).+1 <> 0.
Proof.
set r := funRt n => h hK.
have lo := funRt_sq_le n; have hi := funRt_lt n; rewrite -/r in lo hi.
have hi' : n.+1 < r.+1 * r.+1 by lia.
have ya := Y_add n; rewrite -/r in ya.
case: r => [|s] in h hK lo hi hi' ya *; first by lia.
set m := (funY n).+1 in hK *.
have [hd _] := decomp m; set u := funV m in hd.
have mu : m = funA u by rewrite hK addn0 in hd.
have a1 := two_funA (2 * s + 1); have a2 := two_funA (2 * s + 3); have a3 := two_funA u.
have l1 : funA (2 * s + 1) < funA u by rewrite -mu; nia.
have l2 : funA u < funA (2 * s + 3) by rewrite -mu; nia.
have u2 : u = 2 * s + 2 by have := funA_lt_imp l1; have := funA_lt_imp l2; lia.
rewrite -mu u2 in a3.
have e : 2 * n = 2 * (s * s + 3 * s + 1) + 1 by nia.
by move: e; move: (s * s + 3 * s + 1) => q; lia.
Qed.

Lemma Y_step n : opPlusI (funSgn \o funK) (funS (funY n)) = funY n.+1.
Proof.
set r := funRt n; have lo := funRt_sq_le n; have hi := funRt_lt n; rewrite -/r in lo hi.
have y1 := Y_add n; have y2 := Y_add n.+1; rewrite -/r in y1.
rewrite /opPlusI /comp /funS /funSgn.
case: (eqVneq (r.+1 * r.+1) n.+1) => h.
- have rt : funRt n.+1 = r.+1 by apply: funRt_unique; nia.
  by rewrite Y_step_square // eqxx; lia.
- have rt : funRt n.+1 = r by apply: funRt_unique; nia.
  have hn : funK (funY n).+1 <> 0 by apply: Y_step_nonsquare; apply/eqP.
  by case: eqP => [/hn []|_]; lia.
Qed.

Lemma Y_expr : opBox (opPlusI (funSgn \o funK) \o funS) = funY.
Proof.
apply: functional_extensionality; elim=> [|n ih].
  by rewrite /funY (funRt_unique (r := 0) (n := 0)).
by rewrite opBoxS ih -Y_step.
Qed.

(* Rt == D - Y, Sq == (((1^+)^+ Rt)^+)^box, E == I - Sq Rt *)
Lemma Rt_expr_K : exprDminusF funY = funRt.
Proof.
apply: functional_extensionality => x; have := funRt_le x.
by rewrite exprDminusF_val /funY; lia.
Qed.

Lemma Sq_expr_K : opBox (opPlusI (opPlusI (opPlusI (cst 1)) \o funRt)) = funSq.
Proof.
apply: functional_extensionality; elim=> [//|n ih].
by rewrite opBoxS ih /opPlusI /comp /funSq funRt_sq /cst; lia.
Qed.

Lemma E_expr_K : exprIminusF (funSq \o funRt) = funE.
Proof. by apply: functional_extensionality => x; rewrite exprIminusF_val //; apply: funRt_sq_le. Qed.

Lemma E_in_K : Clos (basis1 funK) funE.
Proof.
have S := C1_S funK; have Sgn := C1_Sgn funK.
have Z : Clos (basis1 funK) funZ by rewrite -Z_expr; clos_solve.
have IF : forall F, Clos (basis1 funK) F -> Clos (basis1 funK) (exprIminusF F).
  by move=> F hF; rewrite /exprIminusF; clos_solve.
have DF : forall F, Clos (basis1 funK) F -> Clos (basis1 funK) (exprDminusF F).
  by move=> F hF; rewrite /exprDminusF; clos_solve.
have Y : Clos (basis1 funK) funY by rewrite -Y_expr; clos_solve.
have Rt : Clos (basis1 funK) funRt by rewrite -Rt_expr_K; clos_solve.
have Sq : Clos (basis1 funK) funSq by rewrite -Sq_expr_K; clos_solve.
by rewrite -E_expr_K; clos_solve.
Qed.

Theorem Theorem_6_8_K : suitable (basis1 funK).
Proof. exact: suitable1 pr_fst E_in_K. Qed.

(** * The basis F'' = <1, L, F^+, FG, F^box> *)

(* K == L 1^+ ((1^+)^+ L)^+, i.e. K(x) = L(x + 2L(x) + 2) (Robinson [16, p. 664]) *)
Lemma K_expr_L : funL \o opPlusI (cst 1) \o opPlusI (opPlusI (opPlusI (cst 1)) \o funL) = funK.
Proof.
apply: functional_extensionality => x; have [hx hk] := decomp x.
have Lx := funL_eq x.
have e : 1 + (1 + funL x + funL x + x) = funA (funV x).+1 + (funV x - funK x + 1).
  by rewrite Lx funA_succ; lia.
rewrite /comp /opPlusI /cst e funL_diag; lia.
Qed.

Lemma K_in_L : Clos (basis1 funL) funK.
Proof. by rewrite -K_expr_L; clos_solve. Qed.

Theorem Theorem_6_8_L : suitable (basis1 funL).
Proof. by have ? := K_in_L; simulate Theorem_6_8_K. Qed.

(* Theorem 6.8 *)
Theorem Theorem_6_8 : suitable (basis1 funK) /\ suitable (basis1 funL).
Proof. by split; [exact: Theorem_6_8_K | exact: Theorem_6_8_L]. Qed.
