(* Replacing the constant 1 by any constant n: for X in {E, K, L} and a set U of unary operators
   containing F^+, the bases <n, X, U, FG> and <1, X, U, FG> generate the same closure whenever
   n >= 1.  For U = {F^+, F^box} (Theorems 6.7, 6.8) this gives suitable bases, and for
   U = {F^+, F^-1} (ExtGR) the unary general recursive functions.  For n = 0 every generated
   function fixes 0, so 1 is missing.

   Only F^+ and X are used.  Since n^+(x) = x + n, every constant c + kn is generated from c;
   X then steps down from c to c - 1:
   - E: c + kn = (nc + 1)^2 + (c - 1) for k = nc^2 + 2c;
   - K: c + kn = A(2nc + 1) + (c - 1) for k = 2nc^2 + 3c;
   - L: two steps, c |-> nc - c |-> c - 1, since
        c + n(2nc^2 + 2c) = A(2nc) + (nc + c)   and   (nc - c) + n(2nc^2) = A(2nc - 1) + (2nc - c). *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67 Thm68 Rem69 ExtA ExtVb ExtGR ExtGRb.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The bases <n, X, U, FG> *)

Definition basisC (X : ufun) (U : (ufun -> ufun) -> Prop) (n : nat) : basis :=
  Basis (fun F => F = cst n \/ F = X) U (fun b => b = comp).

Definition Ubox : (ufun -> ufun) -> Prop := fun u => u = opPlusI \/ u = opBox.
Definition Uinv : (ufun -> ufun) -> Prop := fun u => u = opPlusI \/ u = opInv.

Lemma basis6_C : basis6 = basisC funE Ubox 1. Proof. by []. Qed.
Lemma basis1_C X : basis1 X = basisC X Ubox 1. Proof. by []. Qed.
Lemma basisGR_C X : basisGR X = basisC X Uinv 1. Proof. by []. Qed.

(** * Shifting constants *)

Lemma shift_cst n k c : iter k (opPlusI (cst n)) \o cst c = cst (c + k * n).
Proof.
apply: functional_extensionality => x; rewrite /comp /cst.
by apply: shift_pow => y; rewrite /opPlusI /cst addnC.
Qed.

Section Shift.
Variables (X : ufun) (U : (ufun -> ufun) -> Prop) (n : nat).
Hypothesis P : U opPlusI.
Notation C := (Clos (basisC X U n)).

Lemma cst_shift_in c : C (cst c) -> forall k, C (cst (c + k * n)).
Proof.
move=> hc k; rewrite -shift_cst.
have nC : C (cst n) by apply: clos_init; left.
have pn : C (opPlusI (cst n)) by apply: clos_unop.
exact: (clos_powcomp (B := basisC X U n) (erefl comp) pn hc).
Qed.

Lemma X_cst_in c : C (cst c) -> forall k, C (cst (X (c + k * n))).
Proof.
move=> hc k; have XC : C X by apply: clos_init; right.
have -> : cst (X (c + k * n)) = X \o cst (c + k * n) by [].
exact: (clos_binop (b := comp)) XC (cst_shift_in hc k).
Qed.

(* if X steps down from every constant c >= 1, then 1 is generated from n >= 1 *)
Lemma one_by_descent : 0 < n -> (forall c, C (cst c) -> 0 < c -> C (cst c.-1)) -> C (cst 1).
Proof.
move=> hn step.
have h j : j < n -> C (cst (n - j)).
  elim: j => [_|j ih hj]; first by rewrite subn0; apply: clos_init; left.
  have := step _ (ih (ltnW hj)) ltac:(lia).
  by have -> : (n - j).-1 = n - j.+1 by lia.
by have := h n.-1 ltac:(lia); have -> : n - n.-1 = 1 by lia.
Qed.

End Shift.

(* with 1 in the closure the two bases are equivalent *)
Lemma C_eq_C1 X U n : U opPlusI -> Clos (basisC X U n) (cst 1) -> 0 < n ->
  forall F, Clos (basisC X U n) F <-> Clos (basisC X U 1) F.
Proof.
move=> P one hn F; split.
- have one1 : Clos (basisC X U 1) (cst 1) by apply: clos_init; left.
  have nC : Clos (basisC X U 1) (cst n).
    have := @cst_shift_in X U 1 P 1 one1 n.-1.
    by have -> : 1 + n.-1 * 1 = n by lia.
  apply: clos_subset.
  + by move=> G [->|->]; [exact: nC | apply: clos_init; right].
  + by move=> u G hu hG; apply: clos_unop.
  + by move=> b G H hb hG hH; apply: clos_binop.
- apply: clos_subset.
  + by move=> G [->|->]; [exact: one | apply: clos_init; right].
  + by move=> u G hu hG; apply: clos_unop.
  + by move=> b G H hb hG hH; apply: clos_binop.
Qed.



(** * The descent for E, K, L *)

Lemma E_desc n c : 0 < n -> 0 < c -> funE (c + (n * c * c + 2 * c) * n) = c.-1.
Proof. by move=> hn hc; rewrite (@funE_at (n * c).+1 c.-1) //; nia. Qed.

Lemma K_desc n c : 0 < n -> 0 < c -> funK (c + (2 * n * c * c + 3 * c) * n) = c.-1.
Proof.
move=> hn hc.
have st : funA (2 * n * c).+1 = 2 * n * n * c * c + 3 * n * c + 1.
  by have ? := two_funA (2 * n * c).+1; nia.
have -> : c + (2 * n * c * c + 3 * c) * n = funA (2 * n * c).+1 + c.-1 by rewrite st; nia.
by rewrite funK_diag //; nia.
Qed.

(* for L, two steps: c |-> nc - c |-> c - 1 *)
Lemma L_desc1 n c : 0 < n -> funL (c + (2 * n * c * c + 2 * c) * n) = n * c - c.
Proof.
move=> hn; have cN : c <= n * c by nia.
have s : funA (2 * (n * c)) = 2 * (n * c) * (n * c) + n * c.
  by have ? := two_funA (2 * (n * c)); nia.
have -> : c + (2 * n * c * c + 2 * c) * n = funA (2 * (n * c)) + (n * c + c) by rewrite s; nia.
by rewrite funL_diag; lia.
Qed.

Lemma L_desc2 n c : 0 < n -> 0 < c -> funL ((n * c - c) + (2 * n * c * c) * n) = c.-1.
Proof.
move=> hn hc; have cN : c <= n * c by nia.
have s : funA (2 * (n * c)).-1 + n * c = 2 * (n * c) * (n * c).
  by have ? := two_funA (2 * (n * c)).-1; nia.
have -> : (n * c - c) + (2 * n * c * c) * n = funA (2 * (n * c)).-1 + (2 * (n * c) - c) by nia.
by rewrite funL_diag; nia.
Qed.

Section ELK.
Variables (U : (ufun -> ufun) -> Prop) (n : nat).
Hypotheses (P : U opPlusI) (hn : 0 < n).

Lemma one_in_E : Clos (basisC funE U n) (cst 1).
Proof.
apply: (one_by_descent (X := funE) (U := U) hn) => c hc c1.
have h := X_cst_in P hc (n * c * c + 2 * c).
by rewrite E_desc // in h.
Qed.

Lemma one_in_K : Clos (basisC funK U n) (cst 1).
Proof.
apply: (one_by_descent (X := funK) (U := U) hn) => c hc c1.
have h := X_cst_in P hc (2 * n * c * c + 3 * c).
by rewrite K_desc // in h.
Qed.

Lemma one_in_L : Clos (basisC funL U n) (cst 1).
Proof.
apply: (one_by_descent (X := funL) (U := U) hn) => c hc c1.
have w := X_cst_in P hc (2 * n * c * c + 2 * c); rewrite L_desc1 // in w.
have h := X_cst_in P w (2 * n * c * c).
by rewrite L_desc2 // in h.
Qed.

Theorem C_eq_C1_ELK F :
  [/\ Clos (basisC funE U n) F <-> Clos (basisC funE U 1) F,
      Clos (basisC funK U n) F <-> Clos (basisC funK U 1) F
    & Clos (basisC funL U n) F <-> Clos (basisC funL U 1) F].
Proof.
by split; apply: C_eq_C1 => //; [exact: one_in_E | exact: one_in_K | exact: one_in_L].
Qed.

End ELK.

(** * The constant 0: every function of <0, X, U, FG> fixes 0 when X(0) = 0 and every operator
   of U preserves F(0) = 0 *)

Lemma C0_fix0 X U : X 0 = 0 -> (forall u F, U u -> F 0 = 0 -> u F 0 = 0) ->
  forall F, Clos (basisC X U 0) F -> F 0 = 0.
Proof.
move=> X0 hU F; elim=> [G hG|u G hu _ ih|c G H hc _ ih1 _ ih2].
- by case: hG => ->.
- exact: hU.
- by rewrite /= in hc; rewrite hc /comp ih2 ih1.
Qed.

Lemma Ubox_fix0 u F : Ubox u -> F 0 = 0 -> u F 0 = 0.
Proof. by case=> -> h; rewrite // /opPlusI h. Qed.

Lemma Uinv_fix0 u F : Uinv u -> F 0 = 0 -> u F 0 = 0.
Proof. by case=> -> h; [rewrite /opPlusI h | exact: opInv0]. Qed.

Lemma one_notin_C0 X U : X 0 = 0 -> (forall u F, U u -> F 0 = 0 -> u F 0 = 0) ->
  ~ Clos (basisC X U 0) (cst 1).
Proof. by move=> X0 hU h; have := C0_fix0 X0 hU h. Qed.

(** * Primitive recursive functions *)

Lemma Ext_Cn_aux X : X 0 = 0 -> suitable (basisC X Ubox 1) ->
  (forall m, 0 < m -> forall F, Clos (basisC X Ubox m) F <-> Clos (basisC X Ubox 1) F) ->
  forall n, suitable (basisC X Ubox n) <-> 0 < n.
Proof.
move=> X0 S1 eq [|n].
- split=> // S; case: (one_notin_C0 X0 Ubox_fix0); apply/(S (cst 1)); exact: pr_cst.
- by split=> // _ F; rewrite (eq n.+1 isT F); exact: S1.
Qed.

Theorem Ext_Cn_suitable n :
  [/\ suitable (basisC funE Ubox n) <-> 0 < n, suitable (basisC funK Ubox n) <-> 0 < n
    & suitable (basisC funL Ubox n) <-> 0 < n].
Proof.
have P : Ubox opPlusI by left.
split; apply: Ext_Cn_aux.
- exact: funE0.
- exact: Theorem_6_7.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
- exact: funK0.
- exact: Theorem_6_8_K.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
- exact: funL0.
- exact: Theorem_6_8_L.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
Qed.

(** * General recursive functions, assuming Robinson's theorem *)

Section Robinson_1950.
Variable GR : ufun -> Prop.
Hypothesis Robinson_1950_sec4_thm3 : forall F, CJR F <-> GR F.

Lemma Ext_GRCn_aux X : X 0 = 0 -> (forall F, Clos (basisC X Uinv 1) F <-> GR F) ->
  (forall m, 0 < m -> forall F, Clos (basisC X Uinv m) F <-> Clos (basisC X Uinv 1) F) ->
  forall n, (forall F, Clos (basisC X Uinv n) F <-> GR F) <-> 0 < n.
Proof.
move=> X0 S1 eq [|n].
- split=> // S; case: (one_notin_C0 X0 Uinv_fix0); apply/(S (cst 1)).
  by apply/Robinson_1950_sec4_thm3; exact: one_in_JR.
- by split=> // _ F; rewrite (eq n.+1 isT F); exact: S1.
Qed.

Theorem Ext_GRCn n :
  [/\ (forall F, Clos (basisC funE Uinv n) F <-> GR F) <-> 0 < n,
      (forall F, Clos (basisC funK Uinv n) F <-> GR F) <-> 0 < n
    & (forall F, Clos (basisC funL Uinv n) F <-> GR F) <-> 0 < n].
Proof.
have P : Uinv opPlusI by left.
case: (Ext_GR Robinson_1950_sec4_thm3) => hE hK hL.
split; apply: Ext_GRCn_aux.
- exact: funE0.
- exact: hE.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
- exact: funK0.
- exact: hK.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
- exact: funL0.
- exact: hL.
- by move=> m hm F; case: (C_eq_C1_ELK P hm F).
Qed.

End Robinson_1950.
