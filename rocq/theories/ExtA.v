(* Extension of Remark 6.9 to iteration from any fixed a >= 2, answering the question left
   open at the end of Section 6:
     <X, F^+, FG, F^box(a)> is suitable for every a >= 2 and X in {E, K, L}.
   Together with Remark 6.9 (a = 1) this covers every a >= 1. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67 Thm68 Rem69.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * General facts *)

(* the basis <X, F^+, FG, F^box(a)> *)
Definition basisA (X : ufun) (a : nat) : basis :=
  Basis (fun F => F = X) (fun u => u = opPlusI \/ u = opBoxA a) (fun b => b = comp).

Lemma basis69_eq X : basis69 X = basisA X 1. Proof. by []. Qed.

(* finite powers F^k G (composition) stay in any closure containing (\o) *)
Lemma clos_powcomp B F G : binops B comp -> Clos B F -> Clos B G ->
  forall k, Clos B (iter k F \o G).
Proof.
move=> hc hF hG; elim=> [|k ih].
  by have -> : iter 0 F \o G = G by apply: functional_extensionality.
have -> : iter k.+1 F \o G = F \o (iter k F \o G) by apply: functional_extensionality.
exact: (clos_binop (b := comp)).
Qed.

Lemma Ca_iter X a F k : Clos (basisA X a) funI -> Clos (basisA X a) F ->
  Clos (basisA X a) (iter k F).
Proof. by move=> hI hF; exact: (clos_powcomp (B := basisA X a) (erefl comp) hF hI k). Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Ca_iter) :: prev ().

Lemma funS_pow k x : iter k funS x = x + k.
Proof. by elim: k => [|k ih]; rewrite ?addn0 // iterS ih /funS addnS. Qed.

Lemma shift_pow F c : (forall y, F y = y + c) -> forall k x, iter k F x = x + k * c.
Proof. by move=> h; elim=> [|k ih] x; rewrite ?mul0n ?addn0 // iterS ih h mulSn; lia. Qed.

(* a predecessor (P(x + 1) = x) undoes k successors *)
Lemma pred_pow P : (forall x, P x.+1 = x) -> forall k x, iter k P (x + k) = x.
Proof. by move=> h; elim=> [|k ih] x; rewrite ?addn0 // iterSr addnS h ih. Qed.

Lemma funE_at m k y : k <= 2 * m -> y = m * m + k -> funE y = k.
Proof. by move=> h ->; exact: funE_sq_add. Qed.

Lemma funE0 : funE 0 = 0. Proof. by case: funE_small. Qed.

(* recovering iteration from 0 out of iteration from a (as in Remark 5.10 of the paper):
   F^box == P^a (S^a F P^a)^box(a) *)
Lemma box_from_boxA P a F : (forall x, P x.+1 = x) ->
  iter a P \o opBoxA a (iter a funS \o F \o iter a P) = opBox F.
Proof.
move=> hP; have aux : forall n, opBoxA a (iter a funS \o F \o iter a P) n = opBox F n + a.
  by elim=> [|n ih]; rewrite ?add0n // opBoxAS ih opBoxS /comp pred_pow // funS_pow.
by apply: functional_extensionality => n; rewrite /comp aux pred_pow.
Qed.

(* M_r == (...(0^+)^+...)^+ (r times), i.e. M_r(x) = rx *)
Definition funM (r : nat) : ufun := iter r opPlusI (cst 0).

Lemma funM_apply r x : funM r x = r * x.
Proof. by elim: r => [|r ih]; rewrite ?mul0n // /funM iterS -/(funM r) /opPlusI ih mulSn addnC. Qed.

(* the chain N = T_2 T_3 ... T_(k+1) *)
Fixpoint Nchain (T : nat -> ufun) (k : nat) : ufun :=
  if k is k'.+1 then Nchain T k' \o T k'.+2 else funI.

Lemma Nchain_val T : (forall j, 1 < j -> T j j = j.-1) -> (forall j, T j 0 = 0) ->
  forall k, Nchain T k k.+1 = 1 /\ Nchain T k 0 = 0.
Proof.
move=> h1 h0; elim=> [//|k [ih1 ih0]].
by rewrite /= /comp h1 // h0.
Qed.

(** * The common part of the three cases

   Data: the initial function X, the starting value a >= 2, and multipliers m with
   X(m(j) j) = j - 1, so that T_j == X M_m(j) maps j to j - 1. *)

Record extA (X : ufun) (a : nat) (m : nat -> nat) : Prop := ExtA {
  ea_two : 1 < a;
  ea_zero : Clos (basisA X a) (cst 0);
  ea_X0 : X 0 = 0;
  ea_Xm : forall j, 1 < j -> X (m j * j) = j.-1 }.

Definition funT (X : ufun) (m : nat -> nat) (j : nat) : ufun := X \o funM (m j).

Section ExtA.
Variables (X : ufun) (a : nat) (m : nat -> nat).
Hypothesis h : extA X a m.
Notation C := (Clos (basisA X a)).
Notation N := (Nchain (funT X m)).

Lemma M_in r : C (funM r).
Proof.
elim: r => [|r ih]; first exact: (ea_zero h).
by rewrite /funM iterS; rewrite /funM in ih; clos_solve.
Qed.

Lemma I_in : C funI.
Proof.
have -> : funI = funM 1 by apply: functional_extensionality => x; rewrite funM_apply mul1n.
exact: M_in.
Qed.

Lemma D_in : C funD.
Proof.
have -> : funD = funM 2 by apply: functional_extensionality => x; rewrite funM_apply.
exact: M_in.
Qed.

Lemma T_in j : C (funT X m j).
Proof. by have M := M_in (m j); rewrite /funT; clos_solve. Qed.

Lemma N_val k : N k k.+1 = 1 /\ N k 0 = 0.
Proof.
apply: Nchain_val => j; last by rewrite /funT /comp funM_apply muln0 (ea_X0 h).
by move=> hj; rewrite /funT /comp funM_apply (ea_Xm h).
Qed.

Lemma N_in k : C (N k).
Proof. by elim: k => [|k ih]; [exact: I_in | have T := T_in k.+2; rewrite /=; clos_solve]. Qed.

Lemma Na : N a.-1 a = 1.
Proof. by have [+ _] := N_val a.-1; rewrite prednK // (ltnW (ea_two h)). Qed.

(* the constant a is I^box(a), and 1 == N a with N = T_2 ... T_a *)
Lemma one_expr : N a.-1 \o opBoxA a funI = cst 1.
Proof.
have e : forall n, opBoxA a funI n = a by elim=> [//|n ih]; rewrite opBoxAS ih.
by apply: functional_extensionality => x; rewrite /comp e Na.
Qed.

(* cosignum: O == N 0^box(a) (the iteration of 0 from a has values a, 0, 0, ...) *)
Lemma O_expr_a : N a.-1 \o opBoxA a (cst 0) = funO.
Proof.
apply: functional_extensionality => -[|n]; rewrite /comp /funO; first by rewrite opBoxA0 Na.
by rewrite opBoxAS /cst; case: (N_val a.-1).
Qed.

Lemma one_in : C (cst 1).
Proof. by have N := N_in a.-1; have I := I_in; rewrite -one_expr; clos_solve. Qed.

Lemma S_in : C funS.
Proof. by have one := one_in; rewrite -S_expr; clos_solve. Qed.

Lemma O_in : C funO.
Proof. by have N := N_in a.-1; have zero := ea_zero h; rewrite -O_expr_a; clos_solve. Qed.

(* with any predecessor in the closure, iteration from 0 is available *)
Lemma box_in P F : C P -> (forall x, P x.+1 = x) -> C F -> C (opBox F).
Proof.
move=> hPin hP hF; have I := I_in; have S := S_in.
by rewrite -(box_from_boxA a F hP); clos_solve.
Qed.

End ExtA.

(* for X with X(0) = 0 and X(y) < y for y > 0: 0 == X^a X^box(a) *)
Lemma decreasing_zero X : X 0 = 0 -> (forall y, 0 < y -> X y < y) ->
  forall a, iter a X \o opBoxA a X = cst 0.
Proof.
move=> X0 Xlt a.
have le : forall n, opBoxA a X n <= a.
  elim=> [//|n ih]; rewrite opBoxAS; case: (posnP (opBoxA a X n)) => [->|hp].
    by rewrite X0.
  exact: leq_trans (ltnW (Xlt _ hp)) ih.
have pow : forall k y, y <= k -> iter k X y = 0.
  elim=> [|k ih] y hy; first by move: hy; rewrite leqn0 => /eqP ->.
  rewrite iterSr; apply: ih; case: (posnP y) => [->|hp]; first by rewrite X0.
  by have := Xlt _ hp; lia.
by apply: functional_extensionality => n; rewrite /comp (pow a _ (le n)).
Qed.

Lemma zero_in_dec X a : X 0 = 0 -> (forall y, 0 < y -> X y < y) -> Clos (basisA X a) (cst 0).
Proof.
move=> X0 Xlt; rewrite -(decreasing_zero X0 Xlt a).
have hX : Clos (basisA X a) X by clos_solve.
have hB : Clos (basisA X a) (opBoxA a X) by clos_solve.
exact: (clos_powcomp (B := basisA X a) (erefl comp) hX hB a).
Qed.

(** * The case X = E *)

Lemma funE_lt y : 0 < y -> funE y < y.
Proof.
move=> hy; have := funRt_lt y; have := funRt_sq_le y; rewrite /funE.
case: (posnP (funRt y)) => [->|rp]; first by lia.
have : 0 < funRt y * funRt y by rewrite muln_gt0 rp.
lia.
Qed.

Lemma Xm_E j : 1 < j -> funE (j.-1 * j) = j.-1.
Proof. by case: j => // i _; apply: (@funE_at i); rewrite succnK; nia. Qed.

Lemma locE a : 1 < a -> extA funE a (fun j => j.-1).
Proof. by move=> ha; split; [done | exact: zero_in_dec funE0 funE_lt | exact: funE0 | exact: Xm_E]. Qed.

(* the construction for E: with c = a^2 + a + 4,
   B == (S (D Q S^c)^+)^box(a) satisfies B(n) + a^2 + a = R(n + a^2), i.e.
   B(n) = n + 2 Rt(n + a^2) - a; G == (S^(a+1) B)^box(a) satisfies G(n) = n^2 + 2an + a;
   and P^ == E S^d G^+, d = a^2 - a - 1, is a predecessor. *)
Definition funHE (a : nat) : ufun := funS \o opPlusI (funD \o funQ \o iter (a * a + a + 4) funS).
Definition funBE (a : nat) : ufun := opBoxA a (funHE a).
Definition funGE (a : nat) : ufun := opBoxA a (iter a.+1 funS \o funBE a).
Definition exprPE (a : nat) : ufun := funE \o iter (a * a - a - 1) funS \o opPlusI (funGE a).

Lemma R_rec t : funR t.+1 = 2 * funQ (funR t + 4) + funR t + 1.
Proof.
rewrite -R_step /opPlusI /comp /funD /funS.
have -> : funR t + 4 = (funR t).+4 by lia.
lia.
Qed.

Lemma HE_val a y : funHE a y = 2 * funQ (y + (a * a + a + 4)) + y + 1.
Proof. by rewrite /funHE /comp /opPlusI funS_pow /funD /funS; lia. Qed.

Lemma BE_val a n : funBE a n + a * a + a = funR (n + a * a).
Proof.
elim: n => [|n ih]; first by rewrite /funBE opBoxA0 add0n /funR funRt_sq; lia.
have arg : funBE a n + (a * a + a + 4) = funR (n + a * a) + 4 by lia.
rewrite /funBE opBoxAS -/(funBE a) HE_val arg.
have -> : n.+1 + a * a = (n + a * a).+1 by lia.
by rewrite R_rec; lia.
Qed.

Lemma GE_val a n : funGE a n = n * n + 2 * a * n + a.
Proof.
elim: n => [|n ih]; first by rewrite /funGE opBoxA0 !muln0.
have rt : funRt (n * n + 2 * a * n + a + a * a) = n + a.
  have -> : n * n + 2 * a * n + a + a * a = (n + a) * (n + a) + a by nia.
  by apply: funRt_sq_add; lia.
have b := BE_val a (n * n + 2 * a * n + a); rewrite /funR rt in b.
by rewrite /funGE opBoxAS -/(funGE a) ih /comp funS_pow; nia.
Qed.

Lemma PE_succ a : 1 < a -> forall k, exprPE a k.+1 = k.
Proof.
move=> ha k; rewrite /exprPE /comp /opPlusI funS_pow GE_val.
by apply: (@funE_at (k.+1 + a)); nia.
Qed.

Lemma PE_in a : 1 < a -> Clos (basisA funE a) (exprPE a).
Proof.
move=> ha; have L := locE ha.
have S := S_in L; have I := I_in L; have D := D_in L; have O := O_in L.
have Q : Clos (basisA funE a) funQ by rewrite -Q_expr; clos_solve.
by rewrite /exprPE /funGE /funBE /funHE; clos_solve.
Qed.

Theorem Ext_a_E a : 1 < a -> suitable (basisA funE a).
Proof.
move=> ha; have L := locE ha; have one := one_in L.
have box : forall F, Clos (basisA funE a) F -> Clos (basisA funE a) (opBox F).
  by move=> F hF; exact: (box_in L (PE_in ha) (PE_succ ha) hF).
by simulate Theorem_6_7.
Qed.

(** * The case X = K *)

Lemma funK_lt y : 0 < y -> funK y < y.
Proof.
move=> hy; have [hx hk] := decomp y.
case: (posnP (funV y)) => [v0|vp]; first by rewrite v0 funA0 in hx; lia.
by have := funA_mono vp; rewrite funA1; lia.
Qed.

Lemma Xm_K j : 1 < j -> funK ((2 * j - 2) * j) = j.-1.
Proof.
case: j => // i _; have hA := two_funA (2 * i).
have -> : (2 * i.+1 - 2) * i.+1 = funA (2 * i) + i by nia.
by rewrite funK_diag //; lia.
Qed.

Lemma locK a : 1 < a -> extA funK a (fun j => 2 * j - 2).
Proof. by move=> ha; split; [done | exact: zero_in_dec funK0 funK_lt | exact: funK0 | exact: Xm_K]. Qed.

(* the construction for K: with c = A(a), B == (S^2 (K S^c)^+)^box(a) satisfies
   B(n) + A(a) + 1 = A(n + a + 1), and P^ == K S^c B^+ is a predecessor. *)
Definition funBK (a : nat) : ufun := opBoxA a (iter 2 funS \o opPlusI (funK \o iter (funA a) funS)).
Definition exprPK (a : nat) : ufun := funK \o iter (funA a) funS \o opPlusI (funBK a).

Lemma BK_val a n : funBK a n + funA a + 1 = funA (n + a).+1.
Proof.
elim: n => [|n ih]; first by rewrite /funBK opBoxA0 add0n funA_succ; lia.
have arg : funBK a n + funA a = funA (n + a) + (n + a) by have := funA_succ (n + a); lia.
have k : funK (funBK a n + funA a) = n + a by rewrite arg funK_diag.
rewrite /funBK opBoxAS -/(funBK a) /comp /opPlusI !funS_pow k.
have -> : (n.+1 + a).+1 = (n + a).+2 by lia.
by rewrite funA_succ; lia.
Qed.

Lemma PK_succ a k : exprPK a k.+1 = k.
Proof.
have := BK_val a k.+1; rewrite /exprPK /comp /opPlusI funS_pow => b.
have -> : funBK a k.+1 + k.+1 + funA a = funA (k.+1 + a).+1 + k by lia.
by rewrite funK_diag //; lia.
Qed.

Lemma PK_in a : 1 < a -> Clos (basisA funK a) (exprPK a).
Proof.
move=> ha; have L := locK ha; have S := S_in L; have I := I_in L.
by rewrite /exprPK /funBK; clos_solve.
Qed.

Theorem Ext_a_K a : 1 < a -> suitable (basisA funK a).
Proof.
move=> ha; have L := locK ha; have one := one_in L.
have box : forall F, Clos (basisA funK a) F -> Clos (basisA funK a) (opBox F).
  by move=> F hF; exact: (box_in L (PK_in ha) (PK_succ a) hF).
by simulate Theorem_6_8_K.
Qed.

(** * The case X = L *)

(* 0 == L L^+, because L(x + L(x)) = 0 *)
Lemma zero_expr_L : funL \o opPlusI funL = cst 0.
Proof.
apply: functional_extensionality => x; have [hx hk] := decomp x; have Lx := funL_eq x.
rewrite /comp /opPlusI /cst.
have -> : funL x + x = funA (funV x) + funV x by lia.
by rewrite funL_diag // subnn.
Qed.

Lemma Xm_L j : 1 < j -> funL (2 * j * j) = j.-1.
Proof.
case: j => // i _; have hA := two_funA (2 * i + 1).
have -> : 2 * i.+1 * i.+1 = funA (2 * i + 1) + i.+1 by nia.
by rewrite funL_diag; lia.
Qed.

Lemma locL a : 1 < a -> extA funL a (fun j => 2 * j).
Proof.
move=> ha; split; [done | | exact: funL0 | exact: Xm_L].
by rewrite -zero_expr_L; clos_solve.
Qed.

(* K == L 1^+ ((1^+)^+ L)^+ as in Theorem 6.8, so the case of L reduces to that of K *)
Lemma K_in_La a : 1 < a -> Clos (basisA funL a) funK.
Proof. by move=> ha; have one := one_in (locL ha); rewrite -K_expr_L; clos_solve. Qed.

Theorem Ext_a_L a : 1 < a -> suitable (basisA funL a).
Proof. by move=> ha; have K := K_in_La ha; simulate (Ext_a_K ha). Qed.

(** * Every starting value a >= 1 *)

Theorem Ext_a_all a X : 0 < a -> X = funE \/ X = funK \/ X = funL -> suitable (basisA X a).
Proof.
move=> ha hX; have [->|h] : a = 1 \/ 1 < a by lia.
  by rewrite -basis69_eq; case: hX => [->|[->|->]];
     [exact: Remark_6_9_I | exact: Remark_6_9_II | exact: Remark_6_9_III].
by case: hX => [->|[->|->]]; [exact: Ext_a_E | exact: Ext_a_K | exact: Ext_a_L].
Qed.
