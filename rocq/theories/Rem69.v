(* Remark 6.9: with iteration starting from a = 1, the constant 1 can be dropped:
     (I)   <E, F^+, FG, F^box(1)>
     (II)  <K, F^+, FG, F^box(1)>
     (III) <L, F^+, FG, F^box(1)>
   are suitable bases. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From UPRF Require Import Basic Prim Sec6 Robinson Thm67 Thm68.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* recovering F^box from F^box(1) with a predecessor P^ (P^(x+1) = x): F^box == P^ (S F P^)^box(1) *)
Lemma box_from_box1 (P F : ufun) : (forall x, P x.+1 = x) ->
  P \o opBoxA 1 (funS \o F \o P) = opBox F.
Proof.
move=> hP; have aux : forall n, opBoxA 1 (funS \o F \o P) n = (opBox F n).+1.
  by elim=> [//|n ih]; rewrite opBoxAS ih opBoxS /comp /funS hP.
by apply: functional_extensionality => n; rewrite /comp aux hP.
Qed.

(* a basis <G, F^+, FG, F^box(1)> *)
Definition basis69 (G : ufun) : basis :=
  Basis (fun F => F = G) (fun u => u = opPlusI \/ u = opBoxA 1) (fun b => b = comp).

Section Basis69.
Variable G : ufun.
Notation C := (Clos (basis69 G)).

Lemma CB_G : C G. Proof. by apply: clos_init. Qed.
Lemma CB_plusI F : C F -> C (opPlusI F). Proof. by apply: clos_unop; left. Qed.
Lemma CB_box1 F : C F -> C (opBoxA 1 F). Proof. by apply: clos_unop; right. Qed.
Lemma CB_comp F H : C F -> C H -> C (F \o H).
Proof. by move=> hF hH; apply: (clos_binop (b := comp)). Qed.

(* <G, F^+, FG, F^box(1)> is suitable when it generates 1 and a predecessor P^, the basis
   <1, G, F^+, FG, F^box> is suitable and G is primitive recursive *)
Lemma suitable69 P : suitable (basis1 G) -> PrimNN G -> (forall x, P x.+1 = x) -> C P ->
  C (cst 1) -> suitable (basis69 G).
Proof.
move=> S hG hP hPin one; have hS : C funS by rewrite -S_expr; apply: CB_plusI.
apply: (suitable_by_simulation S).
- by move=> F [->|->]; [exact: one | exact: CB_G].
- move=> u F [->|->] hF; first exact: CB_plusI.
  have e := box_from_box1 F hP.
  have h1 : C (opBoxA 1 (funS \o F \o P)).
    by apply: CB_box1; exact: CB_comp (CB_comp hS hF) hPin.
  by rewrite -e; exact: CB_comp hPin h1.
- by move=> b F H ->; exact: CB_comp.
- apply: clos_sound.
  + by move=> F ->.
  + by move=> u F [->|->]; [exact: pr_opPlusI | exact: pr_opBoxA].
  + by move=> b F H ->; exact: pr_comp.
Qed.

End Basis69.

(* O == G^box(1), 0 == G O and 1 == O 0 whenever G(0) = G(1) = 0 *)
Lemma O_expr_box1 G : G 0 = 0 -> G 1 = 0 -> opBoxA 1 G = funO.
Proof.
move=> h0 h1; have aux : forall m, opBoxA 1 G m.+1 = 0.
  by elim=> [|m ih]; rewrite opBoxAS ?ih.
by apply: functional_extensionality => -[|m]; rewrite ?aux.
Qed.

Lemma zero_expr_O G : G 0 = 0 -> G 1 = 0 -> G \o funO = cst 0.
Proof. by move=> h0 h1; apply: functional_extensionality => x; rewrite /comp /funO; case: eqP. Qed.

Lemma one_expr_O : funO \o cst 0 = cst 1. Proof. by []. Qed.

Lemma one_in69 G : G 0 = 0 -> G 1 = 0 -> Clos (basis69 G) (cst 1).
Proof.
move=> h0 h1; have O : Clos (basis69 G) funO by rewrite -(O_expr_box1 h0 h1); apply: CB_box1 (CB_G G).
by rewrite -one_expr_O -(zero_expr_O h0 h1); apply: CB_comp O (CB_comp (CB_G G) O).
Qed.

(** * (I) <E, F^+, FG, F^box(1)> *)

(* G(x) = (x + 1)^2, G == (((D Q S S)^+ S)^box(1))^box(1); the inner iteration computes R(x) + 1 *)
Definition funG : ufun := fun x => x.+1 * x.+1.

Lemma G_inner n : opBoxA 1 (opPlusI (funD \o funQ \o funS \o funS) \o funS) n = funS (funR n).
Proof.
elim: n => [|n ih]; first by rewrite /funS /funR -[0]/(0 * 0) funRt_sq.
rewrite opBoxAS ih -R_step /comp /opPlusI /funS; lia.
Qed.

Lemma G_expr : opBoxA 1 (opBoxA 1 (opPlusI (funD \o funQ \o funS \o funS) \o funS)) = funG.
Proof.
apply: functional_extensionality; elim=> [//|n ih].
by rewrite opBoxAS ih G_inner /funG /funS /funR funRt_sq; lia.
Qed.

(* P^ == E S S ((G^+)^+)^+ *)
Definition exprPhatI : ufun := funE \o funS \o funS \o opPlusI (opPlusI (opPlusI funG)).

Lemma PhatI_succ x : exprPhatI x.+1 = x.
Proof.
rewrite /exprPhatI /comp /funS /opPlusI /funG.
have -> : (x.+2 * x.+2 + x.+1 + x.+1 + x.+1).+2 = x.+3 * x.+3 + x by nia.
by rewrite funE_sq_add //; lia.
Qed.

Theorem Remark_6_9_I : suitable (basis69 funE).
Proof.
case: funE_small => h0 h1 _ _ _.
have one := one_in69 h0 h1; have E := CB_G funE.
have S : Clos (basis69 funE) funS by rewrite -S_expr; apply: CB_plusI.
have O : Clos (basis69 funE) funO by rewrite -(O_expr_box1 h0 h1); apply: CB_box1.
have zero : Clos (basis69 funE) (cst 0) by rewrite -(zero_expr_O h0 h1); apply: CB_comp.
have D : Clos (basis69 funE) funD by rewrite -D_expr; do 2 apply: CB_plusI.
have Q : Clos (basis69 funE) funQ by rewrite -Q_expr; apply: CB_comp.
have G : Clos (basis69 funE) funG.
  rewrite -G_expr; do 2 apply: CB_box1.
  exact: CB_comp (CB_plusI (CB_comp (CB_comp (CB_comp D Q) S) S)) S.
have P : Clos (basis69 funE) exprPhatI.
  exact: CB_comp (CB_comp (CB_comp E S) S) (CB_plusI (CB_plusI (CB_plusI G))).
have S1 : suitable (basis1 funE).
  apply: (suitable_by_simulation Theorem_6_7); last exact: C1_sound pr_E.
  + by move=> F [->|->]; [exact: C1_one | exact: C1_G].
  + by move=> u F [->|->]; [exact: C1_plusI | exact: C1_box].
  + by move=> b F H ->; exact: C1_comp.
exact: suitable69 S1 pr_E PhatI_succ P one.
Qed.

(** * (II) <K, F^+, FG, F^box(1)> *)

(* H(x) = (x + 1)(x + 4)/2 = A(x+1) + x + 1, H == S (S K^+ S)^box(1) *)
Definition funH : ufun := fun x => funA x.+1 + x + 1.

Lemma two_funH x : 2 * funH x = x.+1 * (x + 4).
Proof. by have := two_funA x.+1; rewrite /funH; nia. Qed.

Lemma H_inner n : opBoxA 1 (funS \o opPlusI funK \o funS) n = funA n.+1 + n.
Proof.
elim: n => [|n ih]; first by rewrite funA1.
rewrite opBoxAS ih /comp /funS /opPlusI.
have -> : (funA n.+1 + n).+1 = funA n.+1 + n.+1 by lia.
rewrite (funK_diag (k := n.+1) (t := n.+1)) // (funA_succ n.+1); lia.
Qed.

Lemma H_expr : funS \o opBoxA 1 (funS \o opPlusI funK \o funS) = funH.
Proof. by apply: functional_extensionality => x; rewrite /comp H_inner /funS /funH; lia. Qed.

(* P^ == K S S S (H^+)^+ *)
Definition exprPhatII : ufun := funK \o funS \o funS \o funS \o opPlusI (opPlusI funH).

Lemma PhatII_succ x : exprPhatII x.+1 = x.
Proof.
rewrite /exprPhatII /comp /funS /opPlusI /funH.
have e4 : x + 4 = x.+4 by lia.
have -> : (funA x.+2 + x.+1 + 1 + x.+1 + x.+1).+3 = funA (x + 4) + x.
  by rewrite e4 !funA_succ; lia.
by rewrite funK_diag //; lia.
Qed.

Theorem Remark_6_9_II : suitable (basis69 funK).
Proof.
have one := one_in69 funK0 funK1; have K := CB_G funK.
have S : Clos (basis69 funK) funS by rewrite -S_expr; apply: CB_plusI.
have H : Clos (basis69 funK) funH.
  by rewrite -H_expr; exact: CB_comp S (CB_box1 (CB_comp (CB_comp S (CB_plusI K)) S)).
have P : Clos (basis69 funK) exprPhatII.
  exact: CB_comp (CB_comp (CB_comp (CB_comp K S) S) S) (CB_plusI (CB_plusI H)).
exact: suitable69 Theorem_6_8_K pr_fst PhatII_succ P one.
Qed.

(** * (III) <L, F^+, FG, F^box(1)>: 1 == L^box(1) (since L(1) = 1) and K == L 1^+ ((1^+)^+ L)^+ *)

Lemma funL1 : funL 1 = 1.
Proof. by have := funL_diag (k := 0) (t := 1) isT; rewrite funA1. Qed.

Lemma one_expr_III : opBoxA 1 funL = cst 1.
Proof. by apply: functional_extensionality; elim=> [//|n ih]; rewrite opBoxAS ih funL1. Qed.

Theorem Remark_6_9_III : suitable (basis69 funL).
Proof.
have L := CB_G funL.
have one : Clos (basis69 funL) (cst 1) by rewrite -one_expr_III; apply: CB_box1.
have K : Clos (basis69 funL) funK.
  rewrite -K_expr_L; apply: CB_comp (CB_comp L (CB_plusI one)) _.
  exact: CB_plusI (CB_comp (CB_plusI (CB_plusI one)) L).
apply: (suitable_by_simulation Remark_6_9_II).
- by move=> F ->.
- by move=> u F [->|->]; [exact: CB_plusI | exact: CB_box1].
- by move=> b F H ->; exact: CB_comp.
- apply: clos_sound.
  + by move=> F ->; exact: pr_snd.
  + by move=> u F [->|->]; [exact: pr_opPlusI | exact: pr_opBoxA].
  + by move=> b F H ->; exact: pr_comp.
Qed.
