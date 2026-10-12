(* Primitive recursiveness of the functions and operators of the paper
   (needed for clos F ⊆ Prim(N,N), which the paper leaves implicit).
   Rocq has no library for this, so the usual bootstrapping is done here:
   identity, constants, +, -, *, the equality test, Rt, E, Hf and iteration. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From UPRF Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma PrimNN_ext f g : PrimNN f -> (forall x, f x = g x) -> PrimNN g.
Proof. by move=> h e; rewrite -(functional_extensionality _ _ e). Qed.

Lemma pr_I : PrimNN funI.
Proof. by apply: PrimNN_ext (pr_pair pr_fst pr_snd) _ => x; rewrite funJ_KL. Qed.

Lemma pr_cst n : PrimNN (cst n).
Proof.
elim: n => [|n ih]; first exact: pr_zero.
exact: PrimNN_ext (pr_comp pr_succ ih) _.
Qed.

(* a function of two arguments defined by recursion on the first one *)
Lemma pr_rec2 g h F G : PrimNN g -> PrimNN h -> PrimNN F -> PrimNN G ->
  PrimNN (fun x => recF g h (F x) (G x)).
Proof.
move=> hg hh hF hG; apply: PrimNN_ext (pr_comp (pr_rec hg hh) (pr_pair hF hG)) _ => x.
by rewrite /= /unaryRec funK_J funL_J.
Qed.

Lemma recF_step g h y x : recF g h y.+1 x = h (funJ (funJ y (recF g h y x)) x).
Proof. by []. Qed.

(* x + y *)
Lemma recF_add y x : recF funI (funS \o funL \o funK) y x = x + y.
Proof. by elim: y => [|y ih] /=; rewrite ?addn0 // funK_J funL_J ih /funS addnS. Qed.

Lemma pr_plus F G : PrimNN F -> PrimNN G -> PrimNN (fun x => F x + G x).
Proof.
move=> hF hG; apply: PrimNN_ext (pr_rec2 pr_I (pr_comp pr_succ (pr_comp pr_snd pr_fst)) hG hF) _.
by move=> x; rewrite recF_add.
Qed.

(* y - 1 *)
Lemma recF_pred y x : recF (cst 0) (funK \o funK) y x = y.-1.
Proof. by case: y => //= y; rewrite !funK_J. Qed.

Lemma pr_pred F : PrimNN F -> PrimNN (fun x => (F x).-1).
Proof.
move=> hF; apply: PrimNN_ext (pr_rec2 (pr_cst 0) (pr_comp pr_fst pr_fst) hF (pr_cst 0)) _.
by move=> x; rewrite recF_pred.
Qed.

(* x - y *)
Definition hPred : ufun := fun w => (funL (funK w)).-1.

Lemma recF_sub y x : recF funI hPred y x = x - y.
Proof. by elim: y => [|y ih] /=; rewrite ?subn0 // /hPred funK_J funL_J ih subnS. Qed.

Lemma pr_minus F G : PrimNN F -> PrimNN G -> PrimNN (fun x => F x - G x).
Proof.
move=> hF hG; have hp : PrimNN hPred := pr_pred (pr_comp pr_snd pr_fst).
by apply: PrimNN_ext (pr_rec2 pr_I hp hG hF) _ => x; rewrite recF_sub.
Qed.

(* x * y *)
Definition hMul : ufun := fun w => funL (funK w) + funL w.

Lemma recF_mul y x : recF (cst 0) hMul y x = x * y.
Proof. by elim: y => [|y ih] /=; rewrite ?muln0 // /hMul funK_J !funL_J ih mulnS addnC. Qed.

Lemma pr_mult F G : PrimNN F -> PrimNN G -> PrimNN (fun x => F x * G x).
Proof.
move=> hF hG; have hm : PrimNN hMul := pr_plus (pr_comp pr_snd pr_fst) pr_snd.
by apply: PrimNN_ext (pr_rec2 (pr_cst 0) hm hG hF) _ => x; rewrite recF_mul.
Qed.

Lemma pr_O : PrimNN funO.
Proof.
apply: PrimNN_ext (pr_minus (pr_cst 1) pr_I) _ => x.
by rewrite /funO /cst /funI; case: x.
Qed.

(* the equality test [F x == G x] *)
Lemma pr_eq F G : PrimNN F -> PrimNN G -> PrimNN (fun x => (F x == G x) : nat).
Proof.
move=> hF hG.
apply: PrimNN_ext (pr_comp pr_O (pr_plus (pr_minus hF hG) (pr_minus hG hF))) _ => x.
by rewrite /= /funO; do 2 case: eqP; lia.
Qed.

(* Rt(y+1) = Rt(y) + [(Rt(y)+1)^2 = y+1] *)
Lemma funRt_succ y :
  funRt y.+1 = funRt y + ((funRt y).+1 * (funRt y).+1 == y.+1).
Proof.
have := funRt_sq_le y; have := funRt_lt y.
case: eqP => h a b.
- by rewrite addn1; apply: funRt_unique; nia.
- by rewrite addn0; apply: funRt_unique; lia.
Qed.

Definition hRt : ufun := fun w =>
  funL (funK w) + ((funL (funK w)).+1 * (funL (funK w)).+1 == (funK (funK w)).+1).

Lemma recF_Rt y x : recF (cst 0) hRt y x = funRt y.
Proof.
elim: y => [|y ih] /=; first by rewrite -[0]/(0 * 0) funRt_sq.
by rewrite /hRt !funK_J funL_J ih funRt_succ.
Qed.

Lemma pr_Rt : PrimNN funRt.
Proof.
have LK := pr_comp pr_snd pr_fst; have KK := pr_comp pr_fst pr_fst.
have hr : PrimNN hRt.
  apply: PrimNN_ext (pr_plus LK (pr_eq (pr_mult (pr_comp pr_succ LK) (pr_comp pr_succ LK))
    (pr_comp pr_succ KK))) _ => w; by [].
by apply: PrimNN_ext (pr_rec2 (pr_cst 0) hr pr_I (pr_cst 0)) _ => x; rewrite recF_Rt.
Qed.

Lemma pr_E : PrimNN funE.
Proof. exact: pr_minus pr_I (pr_mult pr_Rt pr_Rt). Qed.

Lemma pr_Sq : PrimNN funSq.
Proof. exact: pr_mult pr_I pr_I. Qed.

(* Hf(y+1) = Hf(y) + (y - 2 Hf(y)) *)
Definition hHf : ufun := fun w => funL (funK w) + (funK (funK w) - 2 * funL (funK w)).

Lemma recF_Hf y x : recF (cst 0) hHf y x = y %/ 2.
Proof.
elim: y => [|y ih] //=; rewrite /hHf !funK_J funL_J ih.
have := divn_eq y 2; have := ltn_pmod y (isT : 0 < 2).
have := divn_eq y.+1 2; have := ltn_pmod y.+1 (isT : 0 < 2); lia.
Qed.

Lemma pr_Hf : PrimNN funHf.
Proof.
have LK := pr_comp pr_snd pr_fst; have KK := pr_comp pr_fst pr_fst.
have hh : PrimNN hHf := pr_plus LK (pr_minus KK (pr_mult (pr_cst 2) LK)).
by apply: PrimNN_ext (pr_rec2 (pr_cst 0) hh pr_I (pr_cst 0)) _ => x; rewrite recF_Hf.
Qed.

Lemma pr_comp' F G : PrimNN F -> PrimNN G -> PrimNN (F \o G).
Proof. exact: pr_comp. Qed.

Lemma pr_opPlus F G : PrimNN F -> PrimNN G -> PrimNN (opPlus F G).
Proof. exact: pr_plus. Qed.

Lemma pr_opPlusI F : PrimNN F -> PrimNN (opPlusI F).
Proof. by move=> h; apply: pr_plus h pr_I. Qed.

(* F^box(a)(y) = recF a (F L K) y x *)
Lemma recF_box a F y x : recF (cst a) (F \o funL \o funK) y x = opBoxA a F y.
Proof. by elim: y => [|y ih] //=; rewrite funK_J funL_J ih. Qed.

Lemma pr_opBoxA a F : PrimNN F -> PrimNN (opBoxA a F).
Proof.
move=> h; have hh := pr_comp h (pr_comp pr_snd pr_fst).
by apply: PrimNN_ext (pr_rec2 (pr_cst a) hh pr_I (pr_cst 0)) _ => x; rewrite recF_box.
Qed.

Lemma pr_opBox F : PrimNN F -> PrimNN (opBox F).
Proof. exact: pr_opBoxA. Qed.

(* two-argument functions are primitive recursive when they are so on Cantor pairs *)
Definition PrimNN2 (d : nat -> nat -> nat) : Prop := PrimNN (fun z => d (funK z) (funL z)).

Lemma pr_app2 d F G : PrimNN2 d -> PrimNN F -> PrimNN G -> PrimNN (fun x => d (F x) (G x)).
Proof.
move=> hd hF hG; apply: PrimNN_ext (pr_comp hd (pr_pair hF hG)) _ => x.
by rewrite /= funK_J funL_J.
Qed.
