(* The general recursive analogue of Section 6 (README, Section 2.3).

   J. Robinson (General recursive functions, Proc. AMS 1 (1950), Sec. 4, Thm. 3) proved that the
   unary general recursive functions are the closure of <S, E, F + G, FG, F^-1>, where
   F^-1(x) = mu y [F(y) = x] (F onto).  Here F + G is replaced by F^+(x) = F(x) + x: for
   X in {E, K, L},
     clos <1, X, F^+, FG, F^-1> = clos <S, E, F + G, FG, F^-1>,
   so, assuming Robinson's theorem, these bases generate the unary general recursive functions.
   Without 1 every generated function fixes 0.  The constant 1 can be replaced by S (Remark).

   The functions E, S, D, M3, Sq, Hf, Rt used by Lemmas 6.2-6.6 are generated with inversion in
   place of iteration; Lemma 6.6 then gives F + G.
   With E:  E^-1(x) = ceil(x/2)^2 + x,  F^- == E (S S S M3 F E)^+ S (E^-1 D F^+)^+,
            Sq == ((E^-1 D)^-)^-,  I - F == E (S (F^+)^+ E)^+ (Sq F^+)^+,
            W == E (S S D E E)^+ E^-1 (W(y) = 2E(y) + [y even]),  Hf == E W^-1,
            Rt == Hf Hf S S E (I - 1) (I - E) S M4.
   With K:  Z == K^-1,  A == Z - I,  F^- == K (S S S M3 F K)^+ (A F^+)^+,  Sq == (((D Z)^-)^-)^-,
            P == K (K S)^-1,  U == I - A K P (I - K) (U = V + K),  Hf == K U^-1,
            B == I - (I - Sq (I - Hf) U) (I - K) (B = K + ceil(V/2)^2),  E == K B^-1.
   With L:  K == L 1^+ ((1^+)^+ L)^+ (as in Theorem 6.8).

   Inversion needs to decide whether a function is onto: opInv is defined with the classical
   axioms of ClassicalEpsilon (excluded middle and indefinite description). *)

From Stdlib Require Import PeanoNat FunctionalExtensionality ClassicalEpsilon.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67 Thm68 Rem69 ExtA ExtVb.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Inversion *)

Definition surj (F : ufun) : Prop := forall x, exists y, F y = x.

Lemma surj_pred F (h : surj F) x : exists y, (fun y => F y == x) y.
Proof. by case: (h x) => y hy; exists y; apply/eqP. Qed.

(* F^-1(x) = mu y [F(y) = x].  Robinson applies inversion only to onto functions; as an
   operator on all functions, opInv leaves a function that is not onto unchanged, so a closure
   under opInv is exactly a closure under the restricted inversion. *)
Definition opInv (F : ufun) : ufun :=
  match excluded_middle_informative (surj F) with
  | left h => fun x => ex_minn (surj_pred h x)
  | right _ => F
  end.

Lemma opInv_right F : surj F -> forall x, F (opInv F x) = x.
Proof.
move=> h x; rewrite /opInv; case: excluded_middle_informative => [h'|n]; last by case: n.
by case: ex_minnP => m /eqP.
Qed.

Lemma opInv_least F : surj F -> forall x y, F y = x -> opInv F x <= y.
Proof.
move=> h x y hy; rewrite /opInv; case: excluded_middle_informative => [h'|n]; last by case: n.
by case: ex_minnP => m _ /(_ y); apply; apply/eqP.
Qed.

Lemma opInv_not F : ~ surj F -> opInv F = F.
Proof. by move=> n; rewrite /opInv; case: excluded_middle_informative. Qed.

Lemma opInv0 F : F 0 = 0 -> opInv F 0 = 0.
Proof.
move=> h0; case: (excluded_middle_informative (surj F)) => [h|n].
- by have ? := opInv_least h h0; lia.
- by rewrite opInv_not.
Qed.

(* F^-1(x) = v as soon as F is onto, v is a preimage of x and every preimage is at least v *)
Lemma opInv_eqI F x v : surj F -> F v = x -> (forall y, F y = x -> v <= y) -> opInv F x = v.
Proof.
move=> h hv hmin; apply/eqP; rewrite eqn_leq (opInv_least h hv) /=.
exact: hmin (opInv_right h x).
Qed.

(* inv_eq h proves opInv F x = v from h : surj F with opInv_eqI; the goals F v = x and
   forall y, F y = x -> v <= y are tried with reflexivity and lia, and left to the user
   otherwise.  For opInv F = G, use functional_extensionality first. *)
Ltac2 inv_eq0 (h : constr) :=
  refine open_constr:(opInv_eqI $h _ _);
  Control.enter (fun () => try (ltac1:(solve [reflexivity | lia]))).

Tactic Notation "inv_eq" constr(h) :=
  let f := ltac2:(h |- inv_eq0 (Option.get (Ltac1.to_constr h))) in f h.

(* eval_at computes the value of an expression at a point: the operators and the basic functions
   are unfolded, then the arithmetic goal is tried with lia and nia, and left to the user
   otherwise. *)
Ltac2 eval0 () :=
  ltac1:(cbv beta delta [comp opPlusI opPlus opPlusIb funI cst funS funD funSq funM3]);
  Control.enter (fun () => try (ltac1:(solve [reflexivity | lia | nia]))).

Ltac eval_at := ltac2:(eval0 ()).

(* Subtraction by inversion.  Let every y decompose as y = base(t) + X(y) with
   X(y) <= bound(t), where X(base(t) + k) = k for k <= bound(t) (for E: base(t) = t^2,
   bound(t) = 2t; for K: base = A, bound(t) = t).  If V(y) = y + c, then X (X V)^-1
   subtracts c. *)
Lemma sub_inv_surj (X V : ufun) (base bound : nat -> nat) c :
  (forall t k, k <= bound t -> X (base t + k) = k) ->
  (forall z, exists t, z <= bound t /\ c <= base t) ->
  (forall y, V y = y + c) -> surj (X \o V).
Proof.
move=> diag big hV z; case: (big z) => t [h1 h2]; exists (base t + z - c); rewrite /comp hV.
have -> : base t + z - c + c = base t + z by lia.
exact: diag.
Qed.

Lemma sub_inv_val (X V : ufun) (base bound : nat -> nat) c x :
  (forall y, exists t, y = base t + X y /\ X y <= bound t) ->
  (forall t k, k <= bound t -> X (base t + k) = k) ->
  (forall z, exists t, z <= bound t /\ c <= base t) ->
  (forall y, V y = y + c) -> c <= x -> X (opInv (X \o V) x) = x - c.
Proof.
move=> dec diag big hV hc.
have e := opInv_right (sub_inv_surj diag big hV) x; rewrite /comp hV in e.
case: (dec (opInv (X \o V) x + c)) => t [h1 h2]; rewrite e in h1 h2.
have -> : opInv (X \o V) x = base t + (x - c) by lia.
by rewrite diag //; lia.
Qed.

(** * The bases *)

(* J. Robinson's basis <S, E, F + G, FG, F^-1> *)
Definition basisJR : basis :=
  Basis (fun F => F = funS \/ F = funE) (fun u => u = opInv) (fun b => b = opPlus \/ b = comp).

(* <1, X, F^+, FG, F^-1> and <X, F^+, FG, F^-1> *)
Definition basisGR (X : ufun) : basis :=
  Basis (fun F => F = cst 1 \/ F = X) (fun u => u = opPlusI \/ u = opInv) (fun b => b = comp).
Definition basisGR0 (X : ufun) : basis :=
  Basis (fun F => F = X) (fun u => u = opPlusI \/ u = opInv) (fun b => b = comp).

Notation CJR := (Clos basisJR).
Notation CGE := (Clos (basisGR funE)).
Notation CGK := (Clos (basisGR funK)).
Notation CGL := (Clos (basisGR funL)).

(** * Arithmetic facts *)

Lemma funE_bound y : funE y <= 2 * funRt y.
Proof. by have ? := funRt_lt y; have ? := funRt_sq_le y; rewrite /funE; nia. Qed.

(* 2E(y) <= y + 1 *)
Lemma two_funE_le y : 2 * funE y <= y + 1.
Proof.
have h1 := funE_bound y; have h2 := funE_add y.
have h3 : 2 * funRt y <= funRt y * funRt y + 1 by nia.
lia.
Qed.

Lemma half_spec a : 2 * (a %/ 2) <= a < 2 * (a %/ 2) + 2.
Proof. by have ? := divn_eq a 2; have ? := ltn_pmod a (isT : 0 < 2); lia. Qed.

(* Rt(4x+1) / 2 = Rt(x) *)
Lemma funRt_4x1 x : funRt (4 * x + 1) %/ 2 = funRt x.
Proof.
have a := funRt_sq_le x; have b := funRt_lt x.
have c := funRt_sq_le (4 * x + 1); have d := funRt_lt (4 * x + 1).
have lo : 2 * funRt x <= funRt (4 * x + 1).
  by rewrite leqNgt; apply/negP => h; nia.
have hi : funRt (4 * x + 1) < 2 * funRt x + 2.
  by rewrite ltnNge; apply/negP => h; nia.
have ? := half_spec (funRt (4 * x + 1)); lia.
Qed.

(** * clos <1, E, F^+, FG, F^-1> is contained in clos <S, E, F + G, FG, F^-1> *)

Lemma surj_funE : surj funE.
Proof. by move=> x; exists (x * x + x); rewrite funE_sq_add //; lia. Qed.

(* E^-1(x) = ceil(x/2)^2 + x *)
Lemma Einv_val x : opInv funE x = (x.+1 %/ 2) * (x.+1 %/ 2) + x.
Proof.
have hs := half_spec x.+1.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply: (opInv_least surj_funE); rewrite funE_sq_add //; lia.
- have e := opInv_right surj_funE x.
  have b := funE_bound (opInv funE x); have d := funE_add (opInv funE x).
  rewrite e in b d.
  have h : x.+1 %/ 2 <= funRt (opInv funE x) by lia.
  have ? := leq_mul h h; lia.
Qed.

Lemma Einv_D z : opInv funE (funD z) = z * z + 2 * z.
Proof.
rewrite Einv_val /funD; have -> : (2 * z).+1 %/ 2 = z.
  by have ? := half_spec (2 * z).+1; lia.
by [].
Qed.

Lemma Einv_even m : opInv funE (2 * m) = m * m + 2 * m.
Proof. exact: Einv_D. Qed.

Lemma Einv_odd m : opInv funE (2 * m + 1) = m.+1 * m.+1 + (2 * m + 1).
Proof.
rewrite Einv_val; have -> : (2 * m + 1).+1 %/ 2 = m.+1.
  by have ? := half_spec (2 * m + 1).+1; lia.
by [].
Qed.

Lemma I_expr_inv : funE \o opInv funE = funI.
Proof. by apply: functional_extensionality => x; rewrite /comp opInv_right //; exact: surj_funE. Qed.

Lemma zero_expr_JR : funE \o funS \o opInv funE \o opPlus funI funI = cst 0.
Proof.
apply: functional_extensionality => x; rewrite /comp.
have -> : opPlus funI funI x = funD x by rewrite /opPlus /funI /funD; lia.
rewrite Einv_D /funS /cst.
by rewrite (@funE_at x.+1 0) //; lia.
Qed.

Lemma one_expr : funS \o cst 0 = cst 1. Proof. by []. Qed.

Lemma plusI_expr F : opPlus F funI = opPlusI F. Proof. by []. Qed.

Lemma I_in_JR : CJR funI. Proof. by rewrite -I_expr_inv; clos_solve. Qed.
Lemma zero_in_JR : CJR (cst 0).
Proof. by rewrite -zero_expr_JR; have ? := I_in_JR; clos_solve. Qed.
Lemma one_in_JR : CJR (cst 1).
Proof. by rewrite -one_expr; have ? := zero_in_JR; clos_solve. Qed.
Lemma plusI_in_JR F : CJR F -> CJR (opPlusI F).
Proof. by move=> h; rewrite -plusI_expr; have ? := I_in_JR; clos_solve. Qed.

Lemma GE_sub_JR F : CGE F -> CJR F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [exact: one_in_JR | clos_solve].
- by move=> u G [->|->] hG; [exact: plusI_in_JR | clos_solve].
- by move=> b G H -> hG hH; clos_solve.
Qed.

(** * Generating Sq, Hf, Rt in clos <1, E, F^+, FG, F^-1> *)

Lemma I_expr : opPlusI (cst 0) = funI.
Proof. by apply: functional_extensionality => x; eval_at. Qed.

Lemma one_in_GE : CGE (cst 1). Proof. by apply: clos_init; left. Qed.
Lemma S_in_GE : CGE funS. Proof. by rewrite -S_expr; clos_solve. Qed.
Lemma zero_in_GE : CGE (cst 0). Proof. by rewrite -zero_expr; clos_solve. Qed.
Lemma I_in_GE : CGE funI. Proof. by rewrite -I_expr; have ? := zero_in_GE; clos_solve. Qed.
Lemma D_in_GE : CGE funD. Proof. by rewrite -D_expr; have ? := zero_in_GE; clos_solve. Qed.
Lemma M3_in_GE : CGE funM3. Proof. by rewrite -M3_expr; have ? := D_in_GE; clos_solve. Qed.

(* F^- without Sq: F^- == E (S S S M3 F E)^+ S (E^-1 D F^+)^+ *)
Definition exprMinusIE (F : ufun) : ufun :=
  funE \o opPlusI (funS \o funS \o funS \o funM3 \o F \o funE) \o funS \o
    opPlusI (opInv funE \o funD \o opPlusI F).

Lemma exprMinusIE_in F : CGE F -> CGE (exprMinusIE F).
Proof.
by move=> h; rewrite /exprMinusIE; have ? := M3_in_GE; have ? := D_in_GE; have ? := S_in_GE;
  clos_solve.
Qed.

Lemma exprMinusIE_val F x : x <= F x -> exprMinusIE F x = F x - x.
Proof.
move=> h; rewrite /exprMinusIE /comp /opPlusI Einv_D /funS /funM3.
have -> : funE (((F x + x) * (F x + x) + 2 * (F x + x) + x).+1) = x.
  by rewrite (@funE_at (F x + x).+1 x) //; nia.
by rewrite (@funE_at (F x + x).+2 (F x - x)) //; nia.
Qed.

Lemma Sq_expr_GE : exprMinusIE (exprMinusIE (opInv funE \o funD)) = funSq.
Proof.
apply: functional_extensionality => x.
have a : (opInv funE \o funD) x = x * x + 2 * x by rewrite /comp Einv_D.
have b : exprMinusIE (opInv funE \o funD) x = x * x + x.
  by rewrite exprMinusIE_val a //; lia.
by rewrite exprMinusIE_val b /funSq //; lia.
Qed.

Lemma Sq_in_GE : CGE funSq.
Proof.
rewrite -Sq_expr_GE; apply: exprMinusIE_in; apply: exprMinusIE_in.
by have ? := D_in_GE; clos_solve.
Qed.

(* I - F == E (S (F^+)^+ E)^+ (Sq F^+)^+ (if F(x) <= x) *)
Definition exprIminusE (F : ufun) : ufun :=
  funE \o opPlusI (funS \o opPlusI (opPlusI F) \o funE) \o opPlusI (funSq \o opPlusI F).

Lemma exprIminusE_in F : CGE F -> CGE (exprIminusE F).
Proof. by move=> h; rewrite /exprIminusE; have ? := Sq_in_GE; have ? := S_in_GE; clos_solve. Qed.

Lemma exprIminusE_val F x : F x <= x -> exprIminusE F x = x - F x.
Proof.
move=> h; rewrite /exprIminusE /comp /opPlusI /funSq /funS.
have -> : funE ((F x + x) * (F x + x) + x) = x by rewrite funE_sq_add //; lia.
rewrite -robinson_diff_E //; congr funE; nia.
Qed.

(* W == E (S S D E E)^+ E^-1, W(y) = 2E(y) + [y even] (Robinson's W, 1950, Sec. 3) *)
Definition exprW : ufun := funE \o opPlusI (funS \o funS \o funD \o funE \o funE) \o opInv funE.

Lemma exprW_in : CGE exprW.
Proof. by rewrite /exprW; have ? := S_in_GE; have ? := D_in_GE; clos_solve. Qed.

Lemma exprW_val y : exprW y = 2 * funE y + (1 - y %% 2).
Proof.
have hs := half_spec y.+1; have hm := divn_eq y 2; have hm2 := ltn_pmod y (isT : 0 < 2).
have e2 := two_funE_le y.
rewrite /exprW /comp Einv_val /opPlusI.
have -> : funE (y.+1 %/ 2 * (y.+1 %/ 2) + y) = y by rewrite funE_sq_add //; lia.
rewrite /funS /funD.
by rewrite (@funE_at (y.+1 %/ 2).+1 (2 * funE y + (1 - y %% 2))) //; nia.
Qed.

Lemma sq_add_mod2 m k : (m * m + k) %% 2 = (m + k) %% 2.
Proof. by rewrite !modn2 !oddD oddM andbb. Qed.

Lemma surj_exprW : surj exprW.
Proof.
move=> x.
have [k [b [hb hx]]] : exists k b, b < 2 /\ x = k * 2 + b.
  by exists (x %/ 2), (x %% 2); split; [apply: ltn_pmod | apply: divn_eq].
exists ((k.+1 + b) * (k.+1 + b) + k).
have hk : k <= 2 * (k.+1 + b) by lia.
rewrite exprW_val (funE_sq_add hk).
rewrite sq_add_mod2.
have -> : (k.+1 + b + k) %% 2 = 1 - b.
  have -> : k.+1 + b + k = k * 2 + (1 + b) by lia.
  rewrite modnMDl; have : b = 0 \/ b = 1 by lia.
  by case=> ->.
lia.
Qed.

Lemma Hf_expr_GE : funE \o opInv exprW = funHf.
Proof.
apply: functional_extensionality => x; rewrite /comp /funHf.
have h := opInv_right surj_exprW x; rewrite exprW_val in h.
have hm := ltn_pmod (opInv exprW x) (isT : 0 < 2).
have ? := half_spec x; lia.
Qed.

Lemma Hf_in_GE : CGE funHf. Proof. by rewrite -Hf_expr_GE; have ? := exprW_in; clos_solve. Qed.

(* Rt == Hf Hf S S E (I - 1) (I - E) S M4, with M4(x) = 4x *)
Definition exprRtGE : ufun :=
  funHf \o funHf \o funS \o funS \o funE \o exprIminusE (cst 1) \o exprIminusE funE \o funS \o
    opPlusI funM3.

Lemma exprRtGE_in : CGE exprRtGE.
Proof.
rewrite /exprRtGE.
have ? := Hf_in_GE; have ? := S_in_GE; have ? := M3_in_GE.
have ? := exprIminusE_in one_in_GE.
have ? := exprIminusE_in (clos_init (B := basisGR funE) (or_intror (erefl funE))).
clos_solve.
Qed.

Lemma Rt_expr_GE : exprRtGE = funRt.
Proof.
apply: functional_extensionality => x.
have z : funS (opPlusI funM3 x) = 4 * x + 1 by rewrite /funS /opPlusI /funM3; lia.
move: (funRt_4x1 x); set n := funRt (4 * x + 1) => hn.
have n1 : 0 < n by have ? := funRt_lt (4 * x + 1); rewrite -/n; nia.
have ie : exprIminusE funE (4 * x + 1) = n * n.
  by rewrite exprIminusE_val; have ? := funE_add (4 * x + 1); rewrite -/n /funE; lia.
have i1 : exprIminusE (cst 1) (n * n) = n.-1 * n.-1 + 2 * n.-1.
  by rewrite exprIminusE_val /cst; nia.
have eE : funE (n.-1 * n.-1 + 2 * n.-1) = 2 * n.-1 by rewrite funE_sq_add.
rewrite /exprRtGE /comp z ie i1 eE -hn /funS /funHf.
have e2 : (2 * n.-1).+2 = 2 * n by lia.
by rewrite e2 mulKn.
Qed.

Lemma Rt_in_GE : CGE funRt. Proof. by rewrite -Rt_expr_GE; exact: exprRtGE_in. Qed.

(** * Lemmas 6.2-6.6 in clos <1, E, F^+, FG, F^-1>

   Their expressions only use E, S, D, M3, Sq, Hf, Rt, composition and F^+; their values were
   computed in Sec6. *)

Lemma exprMinusI_in_GE F : CGE F -> CGE (exprMinusI F).
Proof.
by move=> h; rewrite /exprMinusI; have ? := S_in_GE; have ? := M3_in_GE; have ? := Sq_in_GE;
  clos_solve.
Qed.
Lemma exprOplus_in_GE F G : CGE F -> CGE G -> CGE (exprOplus F G).
Proof.
by move=> hF hG; rewrite /exprOplus; have ? := exprMinusI_in_GE hF; have ? := Sq_in_GE; clos_solve.
Qed.
Lemma exprOminus_in_GE F G : CGE F -> CGE G -> CGE (exprOminus F G).
Proof.
move=> hF hG; rewrite /exprOminus; have sq := Sq_in_GE.
have h : CGE (opPlusI F \o funE) by clos_solve.
have ? := exprMinusI_in_GE h; clos_solve.
Qed.
Lemma Phat_in_GE : CGE exprPhat.
Proof.
rewrite /exprPhat; apply: exprOminus_in_GE; last exact: S_in_GE.
by have ? := Sq_in_GE; clos_solve.
Qed.
Lemma exprOtimes_in_GE F G : CGE F -> CGE G -> CGE (exprOtimes F G).
Proof.
move=> hF hG; rewrite /exprOtimes.
have sq := Sq_in_GE; have s := S_in_GE; have hf := Hf_in_GE; have rt := Rt_in_GE.
have ph := Phat_in_GE.
have a : CGE (funSq \o funS \o funSq \o F) by clos_solve.
have b := exprOplus_in_GE a hG.
have sF : CGE (funSq \o F) by clos_solve.
have sG : CGE (funSq \o G) by clos_solve.
have c := exprOminus_in_GE b sF.
have d : CGE (funSq \o exprPhat \o exprOminus (exprOplus (funSq \o funS \o funSq \o F) G)
               (funSq \o F)) by clos_solve.
have e := exprOminus_in_GE d sG.
have f : CGE (funHf \o funHf \o exprOminus (funSq \o exprPhat \o exprOminus (exprOplus
               (funSq \o funS \o funSq \o F) G) (funSq \o F)) (funSq \o G)) by clos_solve.
have g := exprOminus_in_GE f sF.
clos_solve.
Qed.
Lemma exprPlus_in_GE F G : CGE F -> CGE G -> CGE (exprPlus F G).
Proof.
move=> hF hG; rewrite /exprPlus.
have pF : CGE (opPlusI F) by clos_solve.
have pG : CGE (opPlusI G) by clos_solve.
have t := exprOtimes_in_GE pF pG.
have d : CGE (funD \o exprOtimes (opPlusI F) (opPlusI G)) by have ? := D_in_GE; clos_solve.
have o := exprOplus_in_GE (exprOplus_in_GE d pF) pG.
have r : CGE (funRt \o exprOplus (exprOplus (funD \o exprOtimes (opPlusI F) (opPlusI G))
               (opPlusI F)) (opPlusI G)) by have ? := Rt_in_GE; clos_solve.
exact: exprMinusI_in_GE (exprMinusI_in_GE r).
Qed.
Lemma exprMinus_in_GE F G : CGE F -> CGE G -> CGE (exprMinus F G).
Proof.
move=> hF hG; rewrite /exprMinus.
have a := exprPlus_in_GE hF hG.
have b : CGE (funSq \o exprPlus F G) by have ? := Sq_in_GE; clos_solve.
have c : CGE (funM3 \o F) by have ? := M3_in_GE; clos_solve.
have d := exprPlus_in_GE (exprPlus_in_GE b c) hG.
by have ? := S_in_GE; clos_solve.
Qed.

(* Lemma 6.6 in clos <1, E, F^+, FG, F^-1> *)
Lemma plus_in_GE F G : CGE F -> CGE G -> CGE (opPlus F G).
Proof. by move=> hF hG; rewrite -exprPlus_eq; exact: exprPlus_in_GE. Qed.

Lemma minus_in_GE F G : CGE F -> CGE G -> (forall x, G x <= F x) -> CGE (opMinus F G).
Proof.
move=> hF hG h.
have -> : opMinus F G = exprMinus F G.
  by apply: functional_extensionality => x; rewrite exprMinus_eq /opDiffE dE_diff.
exact: exprMinus_in_GE.
Qed.

Lemma JR_sub_GE F : CJR F -> CGE F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [exact: S_in_GE | clos_solve].
- by move=> u G -> hG; clos_solve.
- by move=> b G H [->|->] hG hH; [exact: plus_in_GE | clos_solve].
Qed.

Theorem GR_E_eq_JR F : CGE F <-> CJR F.
Proof. by split; [exact: GE_sub_JR | exact: JR_sub_GE]. Qed.

(** * The bases with K and L *)

(** ** K and L in clos <1, E, F^+, FG, F^-1>: K = I - A V and L = A S V - S, with
   A = Hf Sq^+ and V = Hf (Rt S M8 - 1) *)

Definition exprA : ufun := funHf \o opPlusI funSq.
Definition exprV : ufun := funHf \o opMinus (funRt \o funS \o funD \o funD \o funD) (cst 1).

Lemma A_expr : exprA = funA.
Proof. by apply: functional_extensionality => x; rewrite /exprA /comp /funA /funHf /opPlusI /funSq. Qed.

Lemma V_expr : exprV = funV.
Proof.
apply: functional_extensionality => x.
rewrite /exprV /comp /funV /funHf /opMinus /funS /funD /cst.
have -> : 2 * (2 * (2 * x)) = 8 * x by lia.
by rewrite addn1.
Qed.

Lemma Rt_pos n : 0 < funRt n.+1.
Proof.
have hl := funRt_lt n.+1; rewrite lt0n; apply/negP => /eqP h.
by rewrite h in hl.
Qed.

Lemma A_in_GE : CGE funA.
Proof. by rewrite -A_expr /exprA; have ? := Hf_in_GE; have ? := Sq_in_GE; clos_solve. Qed.

Lemma V_in_GE : CGE funV.
Proof.
rewrite -V_expr /exprV.
have m : CGE (opMinus (funRt \o funS \o funD \o funD \o funD) (cst 1)).
  apply: minus_in_GE.
  - by have ? := Rt_in_GE; have ? := S_in_GE; have ? := D_in_GE; clos_solve.
  - by clos_solve.
  - by move=> x; rewrite /cst /comp /funS; exact: Rt_pos.
by have ? := Hf_in_GE; clos_solve.
Qed.

Lemma K_in_GE : CGE funK.
Proof.
have -> : funK = opMinus funI (funA \o funV) by [].
apply: minus_in_GE; first exact: I_in_GE.
- by have ? := A_in_GE; have ? := V_in_GE; clos_solve.
- by move=> x; have [h1 h2] := decomp x; rewrite /comp /funI; lia.
Qed.

Lemma L_in_GE : CGE funL.
Proof.
have -> : funL = opMinus (funA \o funS \o funV) funS.
  by apply: functional_extensionality => x; rewrite /opMinus /comp /funS /funL addn1; lia.
apply: minus_in_GE.
- by have ? := A_in_GE; have ? := V_in_GE; have ? := S_in_GE; clos_solve.
- exact: S_in_GE.
- move=> x; rewrite /comp /funS; have [h1 h2] := decomp x.
  have ? := funA_succ (funV x); have [t /andP [a b]] := funA_index x.
  rewrite (funV_char a b) in h1 *; lia.
Qed.

Lemma GK_sub_GE F : CGK F -> CGE F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [exact: one_in_GE | exact: K_in_GE].
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

Lemma GL_sub_GE F : CGL F -> CGE F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [exact: one_in_GE | exact: L_in_GE].
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

(** ** E in clos <1, K, F^+, FG, F^-1> *)

Lemma S_in_GK : CGK funS. Proof. by rewrite -S_expr; clos_solve. Qed.
Lemma zero_expr_K : funK \o cst 1 = cst 0.
Proof. by apply: functional_extensionality => x; rewrite /comp /cst funK1. Qed.

Lemma zero_in_GK : CGK (cst 0). Proof. by rewrite -zero_expr_K; clos_solve. Qed.
Lemma I_in_GK : CGK funI. Proof. by rewrite -I_expr; have ? := zero_in_GK; clos_solve. Qed.
Lemma D_in_GK : CGK funD. Proof. by rewrite -D_expr; have ? := zero_in_GK; clos_solve. Qed.
Lemma M3_in_GK : CGK funM3. Proof. by rewrite -M3_expr; have ? := D_in_GK; clos_solve. Qed.

Lemma surj_funK : surj funK.
Proof. by move=> x; exists (funA x + x); apply: funK_diag. Qed.

Lemma KZ x : funK (funZ x) = x. Proof. exact: funK_diag. Qed.

(* K^-1 = Z *)
Lemma Kinv_eq_Z : opInv funK = funZ.
Proof.
apply: functional_extensionality => x; inv_eq surj_funK; first exact: KZ.
move=> y hy; have [d1 d2] := decomp y; rewrite hy in d1 d2.
have ? := funA_mono d2; rewrite /funZ; lia.
Qed.

Lemma Z_in_GK : CGK funZ. Proof. by rewrite -Kinv_eq_Z; clos_solve. Qed.

Lemma exprIminusF_in_GK F : CGK F -> CGK (exprIminusF F).
Proof. by move=> h; rewrite /exprIminusF; have ? := Z_in_GK; have ? := S_in_GK; clos_solve. Qed.

(* A == Z - I, i.e. A == K S S S (Y Z K)^+ Z with Y == (Z Z^+ K)^+ Z *)
Definition exprAK : ufun :=
  funK \o funS \o funS \o funS \o opPlusI (opPlusI (funZ \o opPlusI funZ \o funK) \o funZ \o funK)
    \o funZ.

Lemma exprAK_in : CGK exprAK.
Proof. by rewrite /exprAK; have ? := Z_in_GK; have ? := S_in_GK; clos_solve. Qed.

Lemma A_expr_K : exprAK = funA.
Proof.
apply: functional_extensionality => x.
rewrite /exprAK /comp /opPlusI !KZ /funS.
have -> : (funZ (funZ x + x) + funZ x + funZ x).+3 = funZ (funZ x + x) + 2 * funZ x + 3 by lia.
by rewrite robinson_diff_K /funZ; lia.
Qed.

Lemma A_in_GK : CGK funA. Proof. by rewrite -A_expr_K; exact: exprAK_in. Qed.

(* F^- == K (S S S M3 F K)^+ (A F^+)^+ (if F(x) >= x) *)
Definition exprMinusIK (F : ufun) : ufun :=
  funK \o opPlusI (funS \o funS \o funS \o funM3 \o F \o funK) \o opPlusI (funA \o opPlusI F).

Lemma exprMinusIK_in F : CGK F -> CGK (exprMinusIK F).
Proof.
by move=> h; rewrite /exprMinusIK; have ? := A_in_GK; have ? := S_in_GK; have ? := M3_in_GK;
  clos_solve.
Qed.

Lemma exprMinusIK_val F x : x <= F x -> exprMinusIK F x = F x - x.
Proof.
move=> h; rewrite /exprMinusIK /comp /opPlusI /funS /funM3.
have -> : funK (funA (F x + x) + x) = x by apply: funK_diag; lia.
have ? := funA_succ (F x + x); have ? := funA_succ (F x + x).+1.
have -> : (3 * F x).+3 + (funA (F x + x) + x) = funA (F x + x).+2 + (F x - x) by lia.
by apply: funK_diag; lia.
Qed.

Lemma Sq_expr_GK : exprMinusIK (exprMinusIK (exprMinusIK (funD \o funZ))) = funSq.
Proof.
apply: functional_extensionality => x.
have a : (funD \o funZ) x = x * x + 3 * x by rewrite /comp /funD /funZ; have ? := two_funA x; lia.
have b : exprMinusIK (funD \o funZ) x = x * x + 2 * x by rewrite exprMinusIK_val a; lia.
have c : exprMinusIK (exprMinusIK (funD \o funZ)) x = x * x + x.
  by rewrite exprMinusIK_val b; lia.
by rewrite exprMinusIK_val c /funSq; lia.
Qed.

Lemma Sq_in_GK : CGK funSq.
Proof.
rewrite -Sq_expr_GK; apply: exprMinusIK_in; apply: exprMinusIK_in; apply: exprMinusIK_in.
by have ? := D_in_GK; have ? := Z_in_GK; clos_solve.
Qed.

(* the predecessor x - 1 *)
Definition funPred : ufun := fun x => x.-1.

Lemma surj_KS : surj (funK \o funS).
Proof.
move=> x; exists (funA x.+1 + x).-1; rewrite /comp /funS.
have ? := funA_succ x; have -> : (funA x.+1 + x).-1.+1 = funA x.+1 + x by lia.
by apply: funK_diag; lia.
Qed.

(* P == K (K S)^-1 *)
Lemma P_expr_K : funK \o opInv (funK \o funS) = funPred.
Proof.
apply: functional_extensionality => x; rewrite /comp /funPred.
case: x => [|x].
- have h : opInv (funK \o funS) 0 <= 0.
    by apply: (opInv_least surj_KS); rewrite /comp /funS funK1.
  have -> : opInv (funK \o funS) 0 = 0 by lia.
  by have := funK_diag (k := 0) (t := 0) (leqnn 0); rewrite funA0.
- have y := opInv_right surj_KS x.+1; rewrite /comp /funS in y.
  have [d1 d2] := decomp (opInv (funK \o funS) x.+1).+1.
  rewrite y in d1 d2.
  have -> : opInv (funK \o funS) x.+1 = funA (funV (opInv (funK \o funS) x.+1).+1) + x by lia.
  by apply: funK_diag; lia.
Qed.

Lemma P_in_GK : CGK funPred.
Proof. by rewrite -P_expr_K; have ? := S_in_GK; clos_solve. Qed.

Lemma P_succ y : funPred y.+1 = y. Proof. by []. Qed.

(* U == I - A K P (I - K), U(y) = V(y) + K(y) *)
Definition exprU : ufun := exprIminusF (funA \o funK \o funPred \o exprIminusF funK).

Lemma exprU_in : CGK exprU.
Proof.
rewrite /exprU; apply: exprIminusF_in_GK.
have ? := A_in_GK; have ? := P_in_GK.
have ? := exprIminusF_in_GK (clos_init (B := basisGR funK) (or_intror (erefl funK))).
clos_solve.
Qed.

Lemma IminusK y : exprIminusF funK y = funA (funV y).
Proof. by have [d1 d2] := decomp y; rewrite exprIminusF_val; lia. Qed.

Lemma KP_sf t : funK (funPred (funA t)) = t.-1.
Proof.
case: t => [|t]; first by rewrite funA0 /funPred; have := funK_diag (k := 0) (t := 0) (leqnn 0); rewrite funA0.
have -> : funPred (funA t.+1) = funA t + t by rewrite /funPred funA_succ; lia.
by rewrite funK_diag.
Qed.

Lemma exprU_val y : exprU y = funV y + funK y.
Proof.
have [d1 d2] := decomp y.
have inner : (funA \o funK \o funPred \o exprIminusF funK) y = funA (funV y).-1.
  by rewrite /comp IminusK KP_sf.
have le : funA (funV y).-1 <= y by have ? := funA_mono (leq_pred (funV y)); lia.
rewrite /exprU exprIminusF_val inner //.
case: (funV y) d1 d2 inner le => [|t] d1 d2 _ _.
- by rewrite funA0 in d1 *; lia.
- by have ? := funA_succ t; rewrite /=; lia.
Qed.

Lemma exprU_pair k t : k <= t -> exprU (funA t + k) = t + k.
Proof. by move=> h; rewrite exprU_val funV_diag // funK_diag. Qed.

Lemma exprU_sf t : exprU (funA t) = t.
Proof. by have := exprU_pair (k := 0) (t := t) (leq0n t); rewrite !addn0. Qed.

Lemma surj_exprU : surj exprU.
Proof.
move=> x; exists (funA (x - x %/ 2) + x %/ 2); have ? := half_spec x.
by rewrite exprU_pair; lia.
Qed.

Lemma funA_lt_of_lt s t : s < t -> funA s + s < funA t.
Proof. by move=> h; have ? := funA_mono h; have ? := funA_succ s; lia. Qed.

(* Hf == K U^-1 *)
Lemma Hf_expr_K : funK \o opInv exprU = funHf.
Proof.
apply: functional_extensionality => x; rewrite /comp /funHf.
have u := opInv_right surj_exprU x; rewrite exprU_val in u.
have [d1 d2] := decomp (opInv exprU x).
have hs := half_spec x.
have : x %/ 2 <= funK (opInv exprU x).
  rewrite leqNgt; apply/negP => hc.
  have lt : x - x %/ 2 < funV (opInv exprU x) by lia.
  have w : exprU (funA (x - x %/ 2) + x %/ 2) = x by rewrite exprU_pair; lia.
  have ? := opInv_least surj_exprU w; have ? := funA_lt_of_lt lt; lia.
lia.
Qed.

Lemma Hf_in_GK : CGK funHf. Proof. by rewrite -Hf_expr_K; have ? := exprU_in; clos_solve. Qed.

(* B == I - (I - Sq (I - Hf) U) (I - K), B(y) = K(y) + ceil(V(y)/2)^2 *)
Definition exprB : ufun :=
  exprIminusF (exprIminusF (funSq \o exprIminusF funHf \o exprU) \o exprIminusF funK).

Lemma exprB_in : CGK exprB.
Proof.
rewrite /exprB; apply: exprIminusF_in_GK.
have ? := Sq_in_GK; have ? := exprU_in; have ? := exprIminusF_in_GK Hf_in_GK.
have ? := exprIminusF_in_GK (clos_init (B := basisGR funK) (or_intror (erefl funK))).
have ? : CGK (exprIminusF (funSq \o exprIminusF funHf \o exprU)).
  by apply: exprIminusF_in_GK; clos_solve.
clos_solve.
Qed.

Lemma ceil_sq_le_sf t : (t - t %/ 2) * (t - t %/ 2) <= funA t.
Proof.
have h := two_funA t; have hs := half_spec t.
have h1 : 2 * (t - t %/ 2) <= t + 1 by lia.
have h2 : t - t %/ 2 <= t by lia.
nia.
Qed.

Lemma exprB_val y : exprB y = funK y + (funV y - funV y %/ 2) * (funV y - funV y %/ 2).
Proof.
have [d1 d2] := decomp y.
have hf t : exprIminusF funHf t = t - t %/ 2.
  by rewrite exprIminusF_val /funHf; [lia | have ? := half_spec t; lia].
have c := ceil_sq_le_sf (funV y).
have inner : exprIminusF (funSq \o exprIminusF funHf \o exprU) (funA (funV y))
    = funA (funV y) - (funV y - funV y %/ 2) * (funV y - funV y %/ 2).
  by rewrite exprIminusF_val /comp exprU_sf hf /funSq.
rewrite /exprB exprIminusF_val /comp IminusK inner; lia.
Qed.

Lemma surj_exprB : surj exprB.
Proof.
move=> x; exists (funA (2 * funRt x) + funE x).
have b := funE_bound x; have ? := funE_add x.
rewrite exprB_val funV_diag // funK_diag //.
have -> : 2 * funRt x - 2 * funRt x %/ 2 = funRt x by rewrite mulKn; lia.
lia.
Qed.

(* E == K B^-1: if B(y) = x then x = c^2 + K(y) with K(y) <= V(y) <= 2c, so E(x) = K(y) *)
Lemma E_expr_GK : funK \o opInv exprB = funE.
Proof.
apply: functional_extensionality => x; rewrite /comp.
have b := opInv_right surj_exprB x; rewrite exprB_val in b.
have [_ d2] := decomp (opInv exprB x).
have hs := half_spec (funV (opInv exprB x)).
have key c k : k <= 2 * c -> funE (k + c * c) = k by move=> h; rewrite addnC funE_sq_add.
have hle : funK (opInv exprB x) <= 2 * (funV (opInv exprB x) - funV (opInv exprB x) %/ 2)
  by lia.
by have := key _ _ hle; rewrite b => ->.
Qed.

Lemma E_in_GK : CGK funE. Proof. by rewrite -E_expr_GK; have ? := exprB_in; clos_solve. Qed.

Lemma GE_sub_GK F : CGE F -> CGK F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [clos_solve | exact: E_in_GK].
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

(** ** K in clos <1, L, F^+, FG, F^-1> *)

Lemma K_in_GL : CGL funK. Proof. by rewrite -K_expr_L; clos_solve. Qed.

Lemma GK_sub_GL F : CGK F -> CGL F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [clos_solve | exact: K_in_GL].
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

Theorem GR_K_eq_JR F : CGK F <-> CJR F.
Proof.
by split=> h; [exact: GE_sub_JR (GK_sub_GE h) | exact: GE_sub_GK (JR_sub_GE h)].
Qed.

Theorem GR_L_eq_JR F : CGL F <-> CJR F.
Proof.
by split=> h; [exact: GE_sub_JR (GL_sub_GE h) | exact: GK_sub_GL (GE_sub_GK (JR_sub_GE h))].
Qed.

(** * The constant cannot be dropped

   In <X, F^+, FG, F^-1> with X(0) = 0 every function fixes 0: F^+(0) = F(0), and
   F^-1(0) = 0 when F(0) = 0. *)

Lemma GR0_fix0 X : X 0 = 0 -> forall F, Clos (basisGR0 X) F -> F 0 = 0.
Proof.
move=> X0 F; elim=> [G hG|u G hu _ ih|c G H hc _ ih1 _ ih2].
- by rewrite /= in hG; rewrite hG.
- by case: hu => ->; [rewrite /opPlusI ih | exact: opInv0].
- by rewrite /= in hc; rewrite hc /comp ih2 ih1.
Qed.

Theorem GR0_not_one :
  [/\ ~ Clos (basisGR0 funE) (cst 1), ~ Clos (basisGR0 funK) (cst 1)
    & ~ Clos (basisGR0 funL) (cst 1)].
Proof.
split=> h.
- by have := GR0_fix0 funE0 h.
- by have := GR0_fix0 funK0 h.
- by have := GR0_fix0 funL0 h.
Qed.

(** * Assuming Robinson's theorem

   J. Robinson's theorem (1950, Sec. 4, Thm. 3) is a hypothesis: her basis generates the set GR
   of unary general recursive functions. *)

Section Robinson_1950.
Variable GR : ufun -> Prop.
Hypothesis Robinson_1950_sec4_thm3 : forall F, CJR F <-> GR F.

Theorem Ext_GR :
  [/\ forall F, CGE F <-> GR F, forall F, CGK F <-> GR F & forall F, CGL F <-> GR F].
Proof.
split=> F.
- by rewrite GR_E_eq_JR.
- by rewrite GR_K_eq_JR.
- by rewrite GR_L_eq_JR.
Qed.

Theorem Ext_GR0 :
  [/\ ~ (forall F, Clos (basisGR0 funE) F <-> GR F), ~ (forall F, Clos (basisGR0 funK) F <-> GR F)
    & ~ (forall F, Clos (basisGR0 funL) F <-> GR F)].
Proof.
have one : GR (cst 1) by apply/Robinson_1950_sec4_thm3; exact: one_in_JR.
case: GR0_not_one => nE nK nL.
by split=> h; [apply: nE | apply: nK | apply: nL]; apply/h.
Qed.

End Robinson_1950.

(** * Remark: 1 and S are interchangeable

   <S, X, F^+, FG, F^-1> generates the same closure as <1, X, F^+, FG, F^-1>: S = 1^+, and
   1 = S 0, where 0 == K S K^-1, 0 == (E S E^-1)^2, 0 == L (L S)^-1 S. *)

Definition basisGRS (X : ufun) : basis :=
  Basis (fun F => F = funS \/ F = X) (fun u => u = opPlusI \/ u = opInv) (fun b => b = comp).

Lemma GRS_sub_GR X F : Clos (basisGRS X) F -> Clos (basisGR X) F.
Proof.
apply: clos_subset.
- by move=> G [->|->]; [rewrite -S_expr; clos_solve | clos_solve].
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

Lemma GR_sub_GRS X : Clos (basisGRS X) (cst 0) -> forall F, Clos (basisGR X) F -> Clos (basisGRS X) F.
Proof.
move=> z; have one : Clos (basisGRS X) (cst 1) by rewrite -one_expr; clos_solve.
apply: clos_subset.
- by move=> G [->|->]; clos_solve.
- by move=> u G [->|->] hG; clos_solve.
- by move=> b G H -> hG hH; clos_solve.
Qed.

(* 0 == K S K^-1: K^-1(x) + 1 = A(x) + x + 1 = A(x + 1) *)
Lemma zero_expr_GRS_K : funK \o funS \o opInv funK = cst 0.
Proof.
apply: functional_extensionality => x; rewrite /comp Kinv_eq_Z /funS /funZ /cst.
have -> : (funA x + x).+1 = funA x.+1 + 0 by rewrite funA_succ; lia.
by rewrite funK_diag.
Qed.

(* E S E^-1 maps 2j to 0 and 2j + 1 to 2j + 2 *)
Lemma ESEinv_val x : (funE \o funS \o opInv funE) x = if odd x then x.+1 else 0.
Proof.
rewrite /comp /funS; have [j [b [hb ->]]] : exists j b, b < 2 /\ x = 2 * j + b.
  by exists (x %/ 2), (x %% 2); split; [apply: ltn_pmod | rewrite mulnC; apply: divn_eq].
have : b = 0 \/ b = 1 by lia.
case=> ->.
- rewrite addn0 Einv_even oddM /=.
  by rewrite (@funE_at j.+1 0) //; nia.
- rewrite Einv_odd oddD oddM /=.
  by rewrite (@funE_at j.+1 (2 * j).+2) //; nia.
Qed.

(* 0 == (E S E^-1)^2 *)
Lemma zero_expr_GRS_E : (funE \o funS \o opInv funE) \o (funE \o funS \o opInv funE) = cst 0.
Proof.
apply: functional_extensionality => x.
change ((funE \o funS \o opInv funE) ((funE \o funS \o opInv funE) x) = cst 0 x).
rewrite (ESEinv_val x); case hx: (odd x).
- by rewrite ESEinv_val oddS hx.
- by rewrite ESEinv_val.
Qed.

Lemma surj_LS : surj (funL \o funS).
Proof.
move=> v; exists (funA v.+1); rewrite /comp /funS.
have -> : (funA v.+1).+1 = funA v.+1 + 1 by lia.
by rewrite funL_diag; lia.
Qed.

(* the least y with L(y + 1) = x + 1 is A(x) + x *)
Lemma LSinv_succ x : opInv (funL \o funS) x.+1 = funA x + x.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: (opInv_least surj_LS); rewrite /comp /funS.
  have -> : (funA x + x).+1 = funA x.+1 + 0 by rewrite funA_succ; lia.
  by rewrite funL_diag.
- have y := opInv_right surj_LS x.+1; rewrite /comp /funS in y.
  have [d1 d2] := decomp (opInv (funL \o funS) x.+1).+1.
  have hl := funL_eq (opInv (funL \o funS) x.+1).+1; rewrite y in hl.
  have ? : x.+1 <= funV (opInv (funL \o funS) x.+1).+1 by lia.
  have ? := funA_mono (n := funV (opInv (funL \o funS) x.+1).+1) (m := x.+1) ltac:(lia).
  have ? := funA_succ x; lia.
Qed.

(* 0 == L (L S)^-1 S *)
Lemma zero_expr_GRS_L : funL \o opInv (funL \o funS) \o funS = cst 0.
Proof.
apply: functional_extensionality => x; rewrite /comp /funS LSinv_succ /cst.
by rewrite funL_diag // subnn.
Qed.

Theorem GRS_eq_GR :
  [/\ forall F, Clos (basisGRS funE) F <-> CGE F, forall F, Clos (basisGRS funK) F <-> CGK F
    & forall F, Clos (basisGRS funL) F <-> CGL F].
Proof.
have zE : Clos (basisGRS funE) (cst 0) by rewrite -zero_expr_GRS_E; clos_solve.
have zK : Clos (basisGRS funK) (cst 0) by rewrite -zero_expr_GRS_K; clos_solve.
have zL : Clos (basisGRS funL) (cst 0) by rewrite -zero_expr_GRS_L; clos_solve.
by split=> F; split; [exact: GRS_sub_GR | exact: GR_sub_GRS | exact: GRS_sub_GR
  | exact: GR_sub_GRS | exact: GRS_sub_GR | exact: GR_sub_GRS].
Qed.

Theorem Ext_GRS (GR : ufun -> Prop) : (forall F, CJR F <-> GR F) ->
  [/\ forall F, Clos (basisGRS funE) F <-> GR F, forall F, Clos (basisGRS funK) F <-> GR F
    & forall F, Clos (basisGRS funL) F <-> GR F].
Proof.
move=> hJR; case: (Ext_GR hJR) => hE hK hL; case: GRS_eq_GR => sE sK sL.
by split=> F; [rewrite sE | rewrite sK | rewrite sL].
Qed.
