(* Robinson [15] (R. M. Robinson, Primitive recursive functions, Bull. AMS 53 (1947)),
   Section 7, Theorem 3: <S, E, F + G, FG, F^box> is suitable.

   This is not Robinson's proof.  We induct on the unary characterization PrimNN
   (0, S, K, L, composition, pairing J(F, G), unary recursion) and show that clos F
   contains it, using only Lemmas 6.2-6.6.  The recursion operator is obtained from
   F^box by iterating one step function along the rows of a triangle. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From UPRF Require Import Basic Prim Sec6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * More functions and operators in clos F *)

Lemma funI_eq_box_S : opBox funS = funI.
Proof. by apply: functional_extensionality; elim=> // n ih; rewrite opBoxS ih. Qed.

Lemma I_in : C6 funI. Proof. by rewrite -funI_eq_box_S; have ? := S_in; c6. Qed.

Lemma plus_in F G : C6 F -> C6 G -> C6 (opPlus F G).
Proof. by move=> hF hG; case: (Lemma_6_6 hF hG). Qed.

Lemma diffE_in F G : C6 F -> C6 G -> C6 (opDiffE F G).
Proof. by move=> hF hG; case: (Lemma_6_6 hF hG). Qed.

Lemma minus_le_in F G : C6 F -> C6 G -> (forall x, G x <= F x) -> C6 (opMinus F G).
Proof. by move=> hF hG; case: (Lemma_6_6 hF hG). Qed.

(* product without restrictions: FG = Hf((F + G)^2 - (F^2 + G^2)) *)
Lemma times_in F G : C6 F -> C6 G -> C6 (opOtimes F G).
Proof.
move=> hF hG.
have hX : C6 (opMinus (funSq \o opPlus F G) (opPlus (funSq \o F) (funSq \o G))).
  apply: minus_le_in; first by have ? := Sq_in; have ? := plus_in hF hG; c6.
    by apply: plus_in; have ? := Sq_in; c6.
  by move=> x; rewrite /opPlus /funSq /=; move: (F x) (G x) => a b; nia.
apply: C6_eq (C6_comp Hf_in hX); apply: functional_extensionality => x.
rewrite /opMinus /opPlus /funSq /funHf /opOtimes /=.
have -> : (F x + G x) * (F x + G x) = F x * F x + G x * G x + 2 * (F x * G x) by nia.
by rewrite addKn mulKn.
Qed.

(* definition by cases: F(x) if C(x) <> 0, G(x) otherwise; it is Sgn C . F + O C . G *)
Definition opCond (C F G : ufun) : ufun := fun x => if C x == 0 then G x else F x.

Lemma cond_in C F G : C6 C -> C6 F -> C6 G -> C6 (opCond C F G).
Proof.
move=> hC hF hG.
have h := plus_in (times_in (C6_comp Sgn_in hC) hF) (times_in (C6_comp O_in hC) hG).
apply: C6_eq h; apply: functional_extensionality => x.
by rewrite /opPlus /opOtimes /= /funSgn /funO /opCond; case: eqP; lia.
Qed.

(** * The Cantor functions A, V, K, L and J(F, G) *)

Lemma A_in : C6 funA.
Proof. by apply: C6_eq (C6_comp Hf_in (C6_plusI Sq_in)); apply: functional_extensionality. Qed.

Lemma Phat_pos n : 0 < n -> exprPhat n = n - 1.
Proof. by case: n => // n _; rewrite Phat_succ subn1. Qed.

Lemma V_in : C6 funV.
Proof.
have ? := Hf_in; have ? := Phat_in; have ? := Rt_in; have ? := S_in; have ? := D_in.
have h : C6 (funHf \o exprPhat \o funRt \o funS \o funD \o funD \o funD) by c6.
apply: C6_eq h; apply: functional_extensionality => x.
have pos : 0 < funRt (8 * x + 1).
  by have := funRt_lt (8 * x + 1); case: (funRt _) => //=; lia.
rewrite /= /funS /funD /funV /funHf.
have -> : (2 * (2 * (2 * x))).+1 = 8 * x + 1 by lia.
by rewrite Phat_pos.
Qed.

Lemma K_in : C6 funK.
Proof.
apply: C6_eq (minus_le_in I_in (C6_comp A_in V_in) _) => [|x].
  by apply: functional_extensionality.
by have [h _] := decomp x; rewrite /= /funI; lia.
Qed.

Lemma L_in : C6 funL.
Proof.
apply: C6_eq (minus_le_in V_in K_in _) => [|x].
  by apply: functional_extensionality => x; rewrite funL_eq.
by case: (decomp x).
Qed.

(* J(F, G)(x) = J(F(x), G(x)) = A(F(x) + G(x)) + F(x) *)
Definition opJ (F G : ufun) : ufun := fun x => funJ (F x) (G x).

Lemma J_in F G : C6 F -> C6 G -> C6 (opJ F G).
Proof.
move=> hF hG; apply: C6_eq (plus_in (C6_comp A_in (plus_in hF hG)) hF).
by apply: functional_extensionality.
Qed.

(** * Recursion from iteration *)

Section Rec.
Variables g h : ufun.

(* A state J(J(N, y), v) stands for row N, column y <= N, value v = f(y, L(N - 1)).
   The step function T moves to the next column, or to the start of the next row:
   T(J(J(N, y), v)) = J(J(N, y + 1), h(J(J(y, v), L(N - 1)))) if y < N, and
   T(J(J(N, N), v)) = J(J(N + 1, 0), g(L(N))).
   The condition y < N is tested with the difference N - y of Lemma 6.6. *)
Definition stepT : ufun :=
  opCond (exprMinus (funK \o funK) (funL \o funK))
    (opJ (opJ (funK \o funK) (funS \o funL \o funK))
         (h \o opJ (opJ (funL \o funK) funL) (funL \o exprPhat \o funK \o funK)))
    (opJ (opJ (funS \o funK \o funK) (cst 0)) (g \o funL \o funK \o funK)).

Lemma stepT_test : C6 (exprMinus (funK \o funK) (funL \o funK)).
Proof. exact: exprMinus_in (C6_comp K_in K_in) (C6_comp L_in K_in). Qed.

Lemma stepT_next : C6 h ->
  C6 (opJ (opJ (funK \o funK) (funS \o funL \o funK))
          (h \o opJ (opJ (funL \o funK) funL) (funL \o exprPhat \o funK \o funK))).
Proof.
move=> hh; apply: J_in; first exact: J_in (C6_comp K_in K_in) (C6_comp (C6_comp S_in L_in) K_in).
apply: C6_comp hh _; apply: J_in; first exact: J_in (C6_comp L_in K_in) L_in.
exact: C6_comp (C6_comp (C6_comp L_in Phat_in) K_in) K_in.
Qed.

Lemma stepT_row : C6 g ->
  C6 (opJ (opJ (funS \o funK \o funK) (cst 0)) (g \o funL \o funK \o funK)).
Proof.
move=> hg; apply: J_in; first exact: J_in (C6_comp (C6_comp S_in K_in) K_in) zero_in.
exact: C6_comp (C6_comp (C6_comp hg L_in) K_in) K_in.
Qed.

Lemma stepT_in : C6 g -> C6 h -> C6 stepT.
Proof. by move=> hg hh; apply: cond_in stepT_test (stepT_next hh) (stepT_row hg). Qed.

Lemma stepT_val N y v : y <= N ->
  stepT (funJ (funJ N y) v) =
    if y < N then funJ (funJ N y.+1) (h (funJ (funJ y v) (funL (N - 1))))
    else funJ (funJ N.+1 0) (g (funL N)).
Proof.
move=> hy; rewrite /stepT /opCond exprMinus_eq /opDiffE /opJ /comp; cbv beta.
rewrite !funK_J !funL_J dE_diff //.
case: ltnP => hl.
- have -> : (N - y == 0) = false by lia.
  by rewrite Phat_pos ?subn1 //; lia.
- have -> : (N - y == 0) = true by lia.
  by have -> : y = N by lia.
Qed.

Definition stT (N y : nat) : nat := funJ (funJ N y) (recF g h y (funL (N - 1))).

Lemma funK0 : funK 0 = 0. Proof. by have := funK_diag (k := 0) (t := 0) (leqnn 0). Qed.
Lemma funL0 : funL 0 = 0. Proof. by have := funL_diag (k := 0) (t := 0) (leqnn 0). Qed.

Lemma step_start : stepT 0 = stT 1 0.
Proof. by have := stepT_val 0 (leqnn 0); rewrite /= /stT /= funL0 => <-. Qed.

Lemma step_in_row N y : y < N -> stepT (stT N y) = stT N y.+1.
Proof. by move=> hy; rewrite /stT stepT_val ?hy //; apply: ltnW. Qed.

Lemma step_row_end N : stepT (stT N N) = stT N.+1 0.
Proof. by rewrite /stT stepT_val // ltnn subn1. Qed.

Lemma in_row N : iter (funA N) stepT 0 = stT N 0 ->
  forall y, y <= N -> iter (funA N + y) stepT 0 = stT N y.
Proof.
move=> start; elim=> [|y ih] hy; first by rewrite addn0.
by rewrite addnS iterS ih ?step_in_row //; apply: ltnW.
Qed.

Lemma row_start1 : iter (funA 1) stepT 0 = stT 1 0.
Proof.
have a1 : funA 1 = 1 by have := two_funA 1; lia.
have i0 : iter 0 stepT 0 = 0 by [].
by rewrite a1 iterS i0 step_start.
Qed.

Lemma row_startS N : iter (funA N.+1) stepT 0 = stT N.+1 0 ->
  iter (funA N.+2) stepT 0 = stT N.+2 0.
Proof.
move=> ih; rewrite funA_succ addn1 iterS (in_row ih (leqnn N.+1)).
exact: step_row_end.
Qed.

Lemma row_start N : 0 < N -> iter (funA N) stepT 0 = stT N 0.
Proof.
case: N => // N _; elim: N => [|N ih]; first exact: row_start1.
exact: row_startS.
Qed.

(* f(K z, L z) = L(T^box(A(z + 1) + K z)): the pair z is computed in row z + 1 *)
Lemma unaryRec_expr :
  unaryRec g h = funL \o opBox stepT \o opPlus (funA \o funS) funK.
Proof.
apply: functional_extensionality => z.
have hk : funK z <= z.+1 by have [e _] := decomp z; lia.
rewrite /= /opBox /opBoxA /opPlus /funS in_row ?row_start // /stT funL_J.
by rewrite /unaryRec subn1.
Qed.

Lemma unaryRec_in : C6 g -> C6 h -> C6 (unaryRec g h).
Proof.
move=> hg hh; rewrite unaryRec_expr.
exact: C6_comp (C6_comp L_in (C6_box (stepT_in hg hh)))
  (plus_in (C6_comp A_in S_in) K_in).
Qed.

End Rec.

(** * Every primitive recursive function is in clos F *)

Theorem PrimNN_sub_C6 F : PrimNN F -> C6 F.
Proof.
elim=> {F}.
- exact: zero_in.
- exact: S_in.
- exact: K_in.
- exact: L_in.
- by move=> f g _ hf _ hg; apply: C6_comp.
- by move=> f g _ hf _ hg; apply: (J_in hf hg).
- by move=> g h _ hg _ hh; apply: unaryRec_in.
Qed.

(** * Robinson's basis <S, E, F + G, FG, F^box> *)

Definition basisRobinson : basis :=
  Basis (fun F => F = funS \/ F = funE) (fun u => u = opBox)
        (fun b => b = opPlus \/ b = comp).

Lemma Robinson_sound F : Clos basisRobinson F -> PrimNN F.
Proof.
apply: clos_sound => [? [->|->]|? ? ->|? ? ? [->|->]]; auto using pr_succ, pr_E, pr_opBox,
  pr_opPlus, pr_comp.
Qed.

Lemma C6_sub_CR F : C6 F -> Clos basisRobinson F.
Proof.
have S : Clos basisRobinson funS by apply: clos_init; left.
have E : Clos basisRobinson funE by apply: clos_init; right.
have box : forall F, Clos basisRobinson F -> Clos basisRobinson (opBox F)
  by move=> ? ?; apply: clos_unop.
have plus : forall F G, Clos basisRobinson F -> Clos basisRobinson G ->
    Clos basisRobinson (opPlus F G) by move=> ? ? ? ?; apply: (clos_binop (b := opPlus)); [left|..].
have comp : forall F G, Clos basisRobinson F -> Clos basisRobinson G ->
    Clos basisRobinson (F \o G) by move=> ? ? ? ?; apply: (clos_binop (b := comp)); [right|..].
have I : Clos basisRobinson funI by rewrite -funI_eq_box_S; apply: box.
have boxE : opBox funE = cst 0.
  apply: functional_extensionality; elim=> // n ih; rewrite opBoxS ih.
  by case: funE_small.
have one : funS \o opBox funE = cst 1.
  by rewrite boxE; apply: functional_extensionality.
apply: clos_subset.
- move=> F' [->|->]; last exact: E.
  by rewrite -one; apply: comp S (box _ E).
- move=> u F' [->|->] hF'; last exact: box _ hF'.
  have -> : opPlusI F' = opPlus F' funI by [].
  exact: plus _ _ hF' I.
- by move=> b F' G' -> hF' hG'; apply: comp.
Qed.
