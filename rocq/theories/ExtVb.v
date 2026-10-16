(* Removing the constant 1 from the basis of Theorem 6.7 by shifting the unary operator:
   for every fixed b >= 1,
     <E, F^+b, FG, F^box>   with   F^+b(x) = F(x) + x + b
   is a suitable basis, whereas for b = 0 (the basis of Theorem 6.7 without 1) it is not.

   The construction works uniformly for every b >= 1:
     0 == E^box,  A == 0^+b (A(x) = x + b),  C == E A^(b-1) 0 (the constant b - 1),
     B == C^+b (B(x) = x + 2b - 1),  T == B^(2b-2) A A (T(x) = x + 4b^2 - 4b + 2),
     G == (A^3 (E T)^+b)^box (G(n) = n^2 + 4bn),
     P^ == E A^(4b+1) ((G^+b)^+b)^+b (P^(n) = n - 1 for n >= 1),
     S == P^^(b-1) A,  1 == S 0,  F^+ == P^^b F^+b.
   Here A^k etc. are powers under composition (finitely many compositions); they are
   written iter k A \o G, so that the power is always the left factor of a composition. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67 Thm68 Rem69 ExtA.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* F^+b(x) = F(x) + x + b *)
Definition opPlusIb (b : nat) (F : ufun) : ufun := fun x => F x + x + b.

Lemma opPlusIb0 : opPlusIb 0 = opPlusI.
Proof.
apply: functional_extensionality => F; apply: functional_extensionality => x.
by rewrite /opPlusIb /opPlusI addn0.
Qed.

Lemma pr_opPlusIb b F : PrimNN F -> PrimNN (opPlusIb b F).
Proof. by move=> h; apply: PrimNN_ext (pr_plus (pr_opPlusI h) (pr_cst b)) _ => x. Qed.
#[export] Hint Resolve pr_opPlusIb : prim.

(* the basis <E, F^+b, FG, F^box> *)
Definition basisVb (b : nat) : basis :=
  Basis (fun F => F = funE) (fun u => u = opPlusIb b \/ u = opBox) (fun c => c = comp).

Lemma Cb_powcomp b F G k : Clos (basisVb b) F -> Clos (basisVb b) G ->
  Clos (basisVb b) (iter k F \o G).
Proof. by move=> hF hG; exact: (clos_powcomp (B := basisVb b) (erefl comp) hF hG k). Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Cb_powcomp) :: prev ().

(** * The construction *)

Definition zeroB : ufun := opBox funE.
Definition funAb (b : nat) : ufun := opPlusIb b zeroB.
Definition constBm1 (b : nat) : ufun := funE \o (iter b.-1 (funAb b) \o zeroB).
Definition funBb (b : nat) : ufun := opPlusIb b (constBm1 b).
Definition funTb (b : nat) : ufun := iter (2 * b - 2) (funBb b) \o (funAb b \o funAb b).
Definition funHb (b : nat) : ufun := iter 3 (funAb b) \o opPlusIb b (funE \o funTb b).
Definition funGb (b : nat) : ufun := opBox (funHb b).
Definition exprPb (b : nat) : ufun :=
  funE \o (iter (4 * b + 1) (funAb b) \o opPlusIb b (opPlusIb b (opPlusIb b (funGb b)))).
Definition exprSb (b : nat) : ufun := iter b.-1 (exprPb b) \o funAb b.
Definition exprPlusIb (b : nat) (F : ufun) : ufun := iter b (exprPb b) \o opPlusIb b F.

Lemma zeroB_val x : zeroB x = 0.
Proof. by elim: x => [//|x ih]; rewrite /zeroB opBoxS -/zeroB ih funE0. Qed.

Lemma funAb_val b x : funAb b x = x + b.
Proof. by rewrite /funAb /opPlusIb zeroB_val add0n. Qed.

Lemma constBm1_val b x : constBm1 b x = b.-1.
Proof.
rewrite /constBm1 /comp zeroB_val (shift_pow (funAb_val b)) add0n.
case: b => [|c]; first by rewrite muln0 funE0.
by apply: (@funE_at c); rewrite succnK; nia.
Qed.

Lemma funBb_val b x : funBb b x = x + (b.-1 + b).
Proof. by rewrite /funBb /opPlusIb constBm1_val; lia. Qed.

(* with b = c + 1: T(x) = x + d where d = 4c^2 + 4c + 2 = 4b^2 - 4b + 2 *)
Lemma funTb_val c x : funTb c.+1 x = x + (4 * c * c + 4 * c + 2).
Proof.
rewrite /funTb /comp !funAb_val (shift_pow (funBb_val c.+1)) succnK.
have -> : 2 * c.+1 - 2 = 2 * c by lia.
nia.
Qed.

Lemma funHb_val b y : funHb b y = funE (funTb b y) + y + 4 * b.
Proof. by rewrite /funHb /comp /opPlusIb (shift_pow (funAb_val b)); lia. Qed.

Lemma funGb_val c n : funGb c.+1 n = n * n + 4 * c.+1 * n.
Proof.
elim: n => [|n ih]; first by rewrite /funGb opBox0 !muln0.
have e : funE (funTb c.+1 (n * n + 4 * c.+1 * n)) = 2 * n + 1.
  by rewrite funTb_val; apply: (@funE_at (n + 2 * c + 1)); nia.
by rewrite /funGb opBoxS -/(funGb c.+1) ih funHb_val e; nia.
Qed.

(* the predecessor: P^(n) = E((n + 2b + 1)^2 + n - 1) *)
Lemma exprPb_succ c k : exprPb c.+1 k.+1 = k.
Proof.
rewrite /exprPb /comp /opPlusIb (shift_pow (funAb_val c.+1)) funGb_val.
by apply: (@funE_at (k + 2 * c.+1 + 2)); nia.
Qed.

Lemma exprSb_val b : 0 < b -> forall x, exprSb b x = x.+1.
Proof.
case: b => // c _ x; rewrite /exprSb /comp funAb_val.
have -> : x + c.+1 = x.+1 + c by lia.
exact: (pred_pow (exprPb_succ c)).
Qed.

Lemma exprPlusIb_eq b : 0 < b -> forall F, exprPlusIb b F = opPlusI F.
Proof.
case: b => // c _ F; apply: functional_extensionality => x.
rewrite /exprPlusIb /comp /opPlusIb /opPlusI.
exact: (pred_pow (exprPb_succ c)).
Qed.

(** * Suitability for every b >= 1 *)

Theorem Ext_Vb b : 0 < b -> suitable (basisVb b).
Proof.
move=> hb.
have zero : Clos (basisVb b) zeroB by rewrite /zeroB; clos_solve.
have A : Clos (basisVb b) (funAb b) by rewrite /funAb; clos_solve.
have T : Clos (basisVb b) (funTb b) by rewrite /funTb /funBb /constBm1; clos_solve.
have P : Clos (basisVb b) (exprPb b) by rewrite /exprPb /funGb /funHb; clos_solve.
have one : Clos (basisVb b) (cst 1).
  have -> : cst 1 = exprSb b \o zeroB.
    by apply: functional_extensionality => x; rewrite /comp exprSb_val // zeroB_val.
  by rewrite /exprSb; clos_solve.
have plusI : forall F, Clos (basisVb b) F -> Clos (basisVb b) (opPlusI F).
  by move=> F hF; rewrite -(exprPlusIb_eq hb) /exprPlusIb; clos_solve.
by simulate Theorem_6_7.
Qed.

(** * b = 0: the constant 1 cannot be dropped *)

(* every function generated by <E, F^+, FG, F^box> fixes 0, so 1 is not generated *)
Lemma Vb0_fixes_zero F : Clos (basisVb 0) F -> F 0 = 0.
Proof.
elim=> [G hG|u G hu _ ih|c G H hc _ ih1 _ ih2].
- by rewrite /= in hG; rewrite hG funE0.
- by case: hu => ->; rewrite // /opPlusIb ih.
- by rewrite hc /comp ih2 ih1.
Qed.

Theorem Ext_Vb_0 : ~ suitable (basisVb 0).
Proof. by move=> S; have := Vb0_fixes_zero ((S (cst 1)).2 (pr_cst 1)). Qed.

(* <E, F -> F + I + b, FG, F^box> is suitable iff b >= 1 *)
Corollary Ext_Vb_iff b : suitable (basisVb b) <-> 0 < b.
Proof.
split=> [|]; last exact: Ext_Vb.
by case: b => [S|//]; case: (Ext_Vb_0 S).
Qed.
