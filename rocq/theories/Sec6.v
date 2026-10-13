(* Section 6: iteration and the unary operator F^+.  The basis is <1, E, F^+, FG, F^box>.

   Convention: for a function or operator defined in the paper by a formula
   "X == expression", exprX is the expression (built only with the operators of the
   basis) and X_expr / exprX_val state that it computes X. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition basis6 : basis :=
  Basis (fun F => F = cst 1 \/ F = funE) (fun u => u = opPlusI \/ u = opBox)
        (fun b => b = comp).

(* clos F *)
Definition C6 := Clos basis6.

Lemma C6_one : C6 (cst 1). Proof. by apply: clos_init; left. Qed.
Lemma C6_E : C6 funE. Proof. by apply: clos_init; right. Qed.
Lemma C6_plusI F : C6 F -> C6 (opPlusI F). Proof. by apply: clos_unop; left. Qed.
Lemma C6_box F : C6 F -> C6 (opBox F). Proof. by apply: clos_unop; right. Qed.
Lemma C6_comp F G : C6 F -> C6 G -> C6 (F \o G).
Proof. by move=> hF hG; apply: (clos_binop (b := comp)). Qed.

Lemma C6_eq F G : F = G -> C6 F -> C6 G. Proof. by move->. Qed.

(** * First functions in clos F *)

Definition funMod3 : ufun := fun x => x %% 3.
Definition funM3 : ufun := fun x => 3 * x.
Definition funQ : ufun := fun x => if funE x == 0 then 1 else 0.
(* R(x) = x + 2 Rt(x), as in Lemma 5.7 *)
Definition funR : ufun := fun x => x + 2 * funRt x.

Lemma funE_small : [/\ funE 0 = 0, funE 1 = 0, funE 2 = 1, funE 3 = 2 & funE 4 = 0].
Proof.
split; [exact: (funE_sq_add (m := 0) (k := 0)) | exact: (funE_sq_add (m := 1) (k := 0))
  | exact: (funE_sq_add (m := 1) (k := 1)) | exact: (funE_sq_add (m := 1) (k := 2))
  | exact: (funE_sq_add (m := 2) (k := 0))].
Qed.

Lemma S_expr : opPlusI (cst 1) = funS. Proof. by apply: functional_extensionality => x; rewrite /opPlusI /cst /funS add1n. Qed.

Lemma Sgn_expr : opBox (cst 1) = funSgn. Proof. by apply: functional_extensionality => -[]. Qed.

Lemma zero_expr : funE \o cst 1 = cst 0.
Proof. by apply: functional_extensionality => x; case: funE_small. Qed.

Lemma D_expr : opPlusI (opPlusI (cst 0)) = funD.
Proof. by apply: functional_extensionality => x; rewrite /opPlusI /cst /funD; lia. Qed.

Lemma M3_expr : opPlusI funD = funM3.
Proof. by apply: functional_extensionality => x; rewrite /opPlusI /funD /funM3; lia. Qed.

Lemma O_expr : funE \o funD \o funS \o funSgn = funO.
Proof. by apply: functional_extensionality => x; case: funE_small => ? ? ? ? h4; rewrite /funO /funSgn /=; case: eqP. Qed.

Lemma Q_expr : funO \o funE = funQ. Proof. by []. Qed.

Lemma Mod3_expr : opBox (funE \o funS \o funS) = funMod3.
Proof.
apply: functional_extensionality => n; elim: n => [//|n ih]; rewrite opBoxS ih /funMod3 /= /funS.
case: funE_small => _ _ h2 h3 h4.
have := divn_eq n 3; have := ltn_pmod n (isT : 0 < 3).
have := divn_eq n.+1 3; have := ltn_pmod n.+1 (isT : 0 < 3).
case E: (n %% 3) => [|[|[|k]]] /=; [rewrite h2 | rewrite h3 | rewrite h4 | ]; lia.
Qed.

(* the step of R: R(n+1) = (D Q S S S)^+ (S (R n)) *)
Lemma R_step n : opPlusI (funD \o funQ \o funS \o funS \o funS) (funS (funR n)) = funR n.+1.
Proof.
rewrite /opPlusI /= /funD /funS /funR.
set r := funRt n; have lo := funRt_sq_le n; have hi := funRt_lt n; rewrite -/r in lo hi.
case: (boolP (r.+1 * r.+1 == n.+1)) => /eqP hsq.
- have rt : funRt n.+1 = r.+1 by apply: funRt_unique; nia.
  have : funQ (n + 2 * r).+1.+1.+1.+1 = 1.
    have -> : (n + 2 * r).+1.+1.+1.+1 = r.+2 * r.+2 + 0 by nia.
    by rewrite /funQ funE_sq_add //; lia.
  by move->; rewrite rt; lia.
- have rt : funRt n.+1 = r by apply: funRt_unique; nia.
  have : funQ (n + 2 * r).+1.+1.+1.+1 = 0.
    have e : r.+1 * r.+1 = r * r + 2 * r + 1 by nia.
    have -> : (n + 2 * r).+1.+1.+1.+1 = r.+1 * r.+1 + (n - r * r + 3) by rewrite e; lia.
    rewrite /funQ funE_sq_add ?addn3 //.
    have : n.+2 <= r.+1 * r.+1 by lia.
    by rewrite e; lia.
  by move->; rewrite rt; lia.
Qed.

Lemma R_expr : opBox (opPlusI (funD \o funQ \o funS \o funS \o funS) \o funS) = funR.
Proof.
apply: functional_extensionality => n; elim: n => [|n ih]; first by rewrite /funR -[0]/(0 * 0) funRt_sq.
by rewrite opBoxS ih /= R_step.
Qed.

Lemma Sq_expr : opBox (funS \o funR) = funSq.
Proof.
apply: functional_extensionality => n; elim: n => [//|n ih].
by rewrite opBoxS ih /= /funS /funR /funSq funRt_sq; lia.
Qed.

(* membership in clos F: clos_solve (Tactics.v) decomposes the expression; the lemmas
   proved so far are registered as hints *)
Lemma S_in : C6 funS. Proof. by rewrite -S_expr; clos_solve. Qed.
Lemma Sgn_in : C6 funSgn. Proof. by rewrite -Sgn_expr; clos_solve. Qed.
Lemma zero_in : C6 (cst 0). Proof. by rewrite -zero_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(S_in) :: constr:(Sgn_in) :: constr:(zero_in) :: prev ().
Lemma D_in : C6 funD. Proof. by rewrite -D_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(D_in) :: prev ().
Lemma M3_in : C6 funM3. Proof. by rewrite -M3_expr; clos_solve. Qed.
Lemma O_in : C6 funO. Proof. by rewrite -O_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(M3_in) :: constr:(O_in) :: prev ().
Lemma Q_in : C6 funQ. Proof. by rewrite -Q_expr; clos_solve. Qed.
Lemma Mod3_in : C6 funMod3. Proof. by rewrite -Mod3_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Q_in) :: constr:(Mod3_in) :: prev ().
Lemma R_in : C6 funR. Proof. by rewrite -R_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(R_in) :: prev ().
Lemma Sq_in : C6 funSq. Proof. by rewrite -Sq_expr; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Sq_in) :: prev ().

(** * Definition 6.1 (meaningful when F(x) >= x, G(x) >= x and, for (-), F(x) >= G(x)^2) *)

Definition opMinusI (F : ufun) : ufun := fun x => F x - x.
Definition opOplus (F G : ufun) : ufun := fun x => F x + G x * G x.
Definition opOminus (F G : ufun) : ufun := fun x => F x - G x * G x.
Definition opOtimes (F G : ufun) : ufun := fun x => F x * G x.

(** * Lemma 6.2: F^- == E S (M3 F E)^+ (Sq F^+)^+ *)

Definition exprMinusI (F : ufun) : ufun :=
  funE \o funS \o opPlusI (funM3 \o F \o funE) \o opPlusI (funSq \o opPlusI F).

Lemma exprMinusI_in F : C6 F -> C6 (exprMinusI F).
Proof. by move=> h; rewrite /exprMinusI; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(exprMinusI_in) :: prev ().

(* pointwise correctness: only F(x) >= x at the point x is needed *)
Lemma exprMinusI_val F x : x <= F x -> exprMinusI F x = F x - x.
Proof.
move=> h; rewrite /exprMinusI /= /opPlusI /funSq /funM3 /funS /=.
have -> : funE ((F x + x) * (F x + x) + x) = x by rewrite funE_sq_add //; lia.
rewrite -robinson_diff_E //; congr funE; lia.
Qed.

Theorem Lemma_6_2 F : C6 F -> (forall x, x <= F x) -> C6 (opMinusI F).
Proof.
move=> hF h; apply: C6_eq (exprMinusI_in hF).
by apply: functional_extensionality => x; rewrite exprMinusI_val.
Qed.

(** * Lemma 6.3: Hf == ((S Mod3^+)^box)^- and Rt == Hf R^- *)

Lemma Hf_aux n : opBox (funS \o opPlusI funMod3) n = n + n %/ 2.
Proof.
elim: n => [//|n ih]; rewrite opBoxS ih /= /funS /opPlusI /funMod3.
have := divn_eq n 2; have := ltn_pmod n (isT : 0 < 2).
have := divn_eq n.+1 2; have := ltn_pmod n.+1 (isT : 0 < 2).
have := divn_eq (n + n %/ 2) 3; have := ltn_pmod (n + n %/ 2) (isT : 0 < 3); lia.
Qed.

Definition exprHf : ufun := exprMinusI (opBox (funS \o opPlusI funMod3)).
Definition exprRt : ufun := funHf \o exprMinusI funR.

Lemma Hf_expr : exprHf = funHf.
Proof. by apply: functional_extensionality => x; rewrite /exprHf exprMinusI_val Hf_aux /funHf; lia. Qed.

Lemma Rt_expr : exprRt = funRt.
Proof.
apply: functional_extensionality => x; rewrite /exprRt /= exprMinusI_val /funR ?leq_addr //.
by rewrite /funHf addKn mulKn.
Qed.

Theorem Lemma_6_3 : C6 funHf /\ C6 funRt.
Proof.
have Hf : C6 funHf by rewrite -Hf_expr /exprHf; clos_solve.
by split=> //; rewrite -Rt_expr /exprRt; clos_solve.
Qed.

Lemma Hf_in : C6 funHf. Proof. by case: Lemma_6_3. Qed.
Lemma Rt_in : C6 funRt. Proof. by case: Lemma_6_3. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Hf_in) :: constr:(Rt_in) :: prev ().

(** * Lemma 6.4: F (+) G == (F^- E)^+ (Sq G)^+ and F (-) G == (F^+ E)^- (Sq G)^+ *)

Definition exprOplus (F G : ufun) : ufun := opPlusI (exprMinusI F \o funE) \o opPlusI (funSq \o G).
Definition exprOminus (F G : ufun) : ufun := exprMinusI (opPlusI F \o funE) \o opPlusI (funSq \o G).

Lemma exprOplus_in F G : C6 F -> C6 G -> C6 (exprOplus F G).
Proof. by move=> hF hG; rewrite /exprOplus; clos_solve. Qed.

Lemma exprOminus_in F G : C6 F -> C6 G -> C6 (exprOminus F G).
Proof.
by move=> hF hG; rewrite /exprOminus; clos_solve.
Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(exprOplus_in) :: constr:(exprOminus_in) :: prev ().

Lemma E_SqG (G : ufun) x : x <= G x -> funE (G x * G x + x) = x.
Proof. by move=> h; rewrite funE_sq_add //; lia. Qed.

Lemma exprOplus_val F G x : x <= F x -> x <= G x -> exprOplus F G x = F x + G x * G x.
Proof.
move=> hF hG; rewrite /exprOplus /= /opPlusI /funSq /= E_SqG // exprMinusI_val //; lia.
Qed.

Lemma exprOminus_val F G x : x <= G x -> G x * G x <= F x ->
  exprOminus F G x = F x - G x * G x.
Proof.
move=> hG h; set y := G x * G x + x.
have e1 : opPlusI (funSq \o G) x = y by [].
have e2 : funE y = x by apply: E_SqG.
rewrite /exprOminus /= e1 exprMinusI_val /= /opPlusI e2; lia.
Qed.

Theorem Lemma_6_4 F G : C6 F -> C6 G -> (forall x, x <= F x) -> (forall x, x <= G x) ->
  C6 (opOplus F G) /\ ((forall x, G x * G x <= F x) -> C6 (opOminus F G)).
Proof.
move=> hF hG hFx hGx; split=> [|h].
- by apply: C6_eq (exprOplus_in hF hG); apply: functional_extensionality => x; rewrite exprOplus_val.
- by apply: C6_eq (exprOminus_in hF hG); apply: functional_extensionality => x; rewrite exprOminus_val.
Qed.

(** * Lemma 6.5: P^ == ((Sq^+)^+)^+ (-) S, i.e. P^(x + 1) = x, and
      F (x) G == Rt((Hf Hf (Sq P^((Sq S Sq F (+) G) (-) Sq F) (-) Sq G)) (-) Sq F) *)

Definition exprPhat : ufun := exprOminus (opPlusI (opPlusI (opPlusI funSq))) funS.

Lemma Phat_in : C6 exprPhat.
Proof. by rewrite /exprPhat; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(Phat_in) :: prev ().

Lemma Phat_succ x : exprPhat x.+1 = x.
Proof.
rewrite /exprPhat exprOminus_val /opPlusI /funSq /funS; nia.
Qed.

Definition exprOtimes (F G : ufun) : ufun :=
  funRt \o exprOminus
    (funHf \o funHf \o exprOminus (funSq \o exprPhat \o
      exprOminus (exprOplus (funSq \o funS \o funSq \o F) G) (funSq \o F)) (funSq \o G))
    (funSq \o F).

Lemma exprOtimes_in F G : C6 F -> C6 G -> C6 (exprOtimes F G).
Proof. by move=> hF hG; rewrite /exprOtimes; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(exprOtimes_in) :: prev ().

Lemma exprOtimes_val F G x : x <= F x -> x <= G x -> exprOtimes F G x = F x * G x.
Proof.
move=> hF hG; set a := F x; set b := G x.
have xaa : x <= a * a by nia.
have xbb : x <= b * b by nia.
have SqF : (funSq \o F) x = a * a by [].
have SqG : (funSq \o G) x = b * b by [].
(* (Sq S Sq F (+) G)(x) = (a^2 + 1)^2 + b^2 *)
have v1 : exprOplus (funSq \o funS \o funSq \o F) G x = (a * a).+1 * (a * a).+1 + b * b.
  by rewrite exprOplus_val //= /funSq /funS -/a; nia.
(* (-) Sq F gives 2a^2 + 1 + b^2 *)
have v2 : exprOminus (exprOplus (funSq \o funS \o funSq \o F) G) (funSq \o F) x
          = (2 * (a * a) + b * b).+1.
  by rewrite exprOminus_val SqF ?v1 //; nia.
set c := 2 * (a * a) + b * b.
(* Sq P^ gives c^2;  (-) Sq G gives 4a^4 + 4a^2b^2;  Hf Hf gives a^4 + a^2b^2 *)
have v3 : (funSq \o exprPhat \o exprOminus (exprOplus (funSq \o funS \o funSq \o F) G)
           (funSq \o F)) x = c * c by rewrite /= v2 Phat_succ.
set w := a * a * (a * a) + a * a * (b * b).
have v4 : exprOminus (funSq \o exprPhat \o exprOminus (exprOplus (funSq \o funS \o funSq \o F) G)
            (funSq \o F)) (funSq \o G) x = 2 * (2 * w).
  by rewrite exprOminus_val SqG ?v3 /c /w //; nia.
have v5 : (funHf \o funHf \o exprOminus (funSq \o exprPhat \o
            exprOminus (exprOplus (funSq \o funS \o funSq \o F) G) (funSq \o F)) (funSq \o G)) x = w.
  by rewrite /= v4 /funHf !mulKn.
(* (-) Sq F gives a^2b^2, and Rt gives ab *)
have xF : x <= (funSq \o F) x by rewrite SqF.
have hle : (funSq \o F) x * (funSq \o F) x <= (funHf \o funHf \o exprOminus (funSq \o exprPhat \o
            exprOminus (exprOplus (funSq \o funS \o funSq \o F) G) (funSq \o F)) (funSq \o G)) x.
  by rewrite SqF v5 /w; lia.
rewrite /exprOtimes /= (exprOminus_val xF hle) SqF v5 /w.
have -> : a * a * (a * a) + a * a * (b * b) - a * a * (a * a) = a * b * (a * b) by nia.
by rewrite funRt_sq.
Qed.

Theorem Lemma_6_5 F G : C6 F -> C6 G -> (forall x, x <= F x) -> (forall x, x <= G x) ->
  C6 (opOtimes F G).
Proof. by move=> hF hG hFx hGx; apply: C6_eq (exprOtimes_in hF hG); apply: functional_extensionality => x; rewrite exprOtimes_val. Qed.

(** * Lemma 6.6: F + G == ((Rt((D(F^+ (x) G^+) (+) F^+) (+) G^+))^-)^- and
      F - G == E S (Sq(F + G) + M3 F + G) *)

Definition exprPlus (F G : ufun) : ufun :=
  exprMinusI (exprMinusI (funRt \o exprOplus (exprOplus
    (funD \o exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F)) (opPlusI G))).

Definition exprMinus (F G : ufun) : ufun :=
  funE \o funS \o exprPlus (exprPlus (funSq \o exprPlus F G) (funM3 \o F)) G.

Lemma exprPlus_in F G : C6 F -> C6 G -> C6 (exprPlus F G).
Proof. by move=> hF hG; rewrite /exprPlus; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(exprPlus_in) :: prev ().

Lemma exprMinus_in F G : C6 F -> C6 G -> C6 (exprMinus F G).
Proof. by move=> hF hG; rewrite /exprMinus; clos_solve. Qed.
Ltac2 Set clos_hints as prev := fun () => constr:(exprMinus_in) :: prev ().

Lemma exprPlus_val F G x : exprPlus F G x = F x + G x.
Proof.
set a := F x + x; set b := G x + x.
have t : exprOtimes (opPlusI F) (opPlusI G) x = a * b by rewrite exprOtimes_val /opPlusI ?leq_addl.
have x2ab : x <= 2 * (a * b) by rewrite /a /b; nia.
have o1 : exprOplus (funD \o exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F) x = 2 * (a * b) + a * a.
  by rewrite exprOplus_val /= ?t /funD /opPlusI -/a //; lia.
have o2 : exprOplus (exprOplus (funD \o exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F))
            (opPlusI G) x = (a + b) * (a + b).
  have s1 : x <= exprOplus (funD \o exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F) x
    by rewrite o1; lia.
  have s2 : x <= opPlusI G x by rewrite /opPlusI; lia.
  by rewrite (exprOplus_val s1 s2) o1 /opPlusI -/b; nia.
have rH : (funRt \o exprOplus (exprOplus (funD \o exprOtimes (opPlusI F) (opPlusI G))
            (opPlusI F)) (opPlusI G)) x = a + b by rewrite /= o2 funRt_sq.
rewrite /exprPlus exprMinusI_val exprMinusI_val ?rH /a /b //; lia.
Qed.

Lemma exprPlus_eq F G : exprPlus F G = opPlus F G.
Proof. by apply: functional_extensionality => x; rewrite exprPlus_val. Qed.

(* the difference function computed by F - G (footnote 8): it is F - G where F >= G,
   and some other value elsewhere *)
Definition dE (a b : nat) : nat := funE ((a + b) * (a + b) + 3 * a + b + 1).

Lemma dE_diff a b : b <= a -> dE a b = a - b.
Proof. exact: robinson_diff_E. Qed.

Definition opDiffE (F G : ufun) : ufun := fun x => dE (F x) (G x).

Lemma exprMinus_eq F G : exprMinus F G = opDiffE F G.
Proof.
apply: functional_extensionality => x; rewrite /exprMinus /= !exprPlus_val /= exprPlus_val /funSq /funM3 /funS /opDiffE /dE.
by congr funE; lia.
Qed.

Theorem Lemma_6_6 F G : C6 F -> C6 G ->
  [/\ C6 (opPlus F G), C6 (opDiffE F G) & (forall x, G x <= F x) -> C6 (opMinus F G)].
Proof.
move=> hF hG; split.
- by rewrite -exprPlus_eq; exact: exprPlus_in.
- by rewrite -exprMinus_eq; exact: exprMinus_in.
- move=> h; apply: C6_eq (exprMinus_in hF hG).
  by apply: functional_extensionality => x; rewrite exprMinus_eq /opDiffE dE_diff.
Qed.
