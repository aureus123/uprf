(* The general recursive analogue of the shifted operator of ExtVb: for X in {E, K, L},

     clos <X, F^+b, FG, F^-1> = clos <S, E, F + G, FG, F^-1>   iff   b >= 1,

   where F^+b(x) = F(x) + x + b.  So, assuming J. Robinson's theorem, these bases generate exactly
   the unary general recursive functions when b >= 1, and not when b = 0 (then every generated
   function fixes 0, ExtGR).

   In each case a successor S is generated first; then a predecessor P (P(x + 1) = x) gives
   F^+ == P^b F^+b and the constant 1, so the closure contains the basis <1, X, F^+, FG, F^-1> of
   ExtGR.  With T == I^+b (T(x) = 2x + b):
   - E, b >= 2: E (E^-1 T)^+b and E (E^-1 (E (E^-1 T)^+b) T)^+b are the shifts x + b - 1 and
     x + b - 2 (in an order that depends on the parity of b); if V(x) = x + c then E (E V)^-1
     subtracts c, and S == E (E U2)^-1 U1.
   - E, b = 1: P == E (E^-1 T)^+1 is a predecessor and S == E P^-1 (E^-1 P T)^+1.
   - K, b >= 2: U == K (Z T)^+b is x + b - 1 (Z = K^-1), the constant 2b - 4 is
     K (Z K (K U)^-1)^+b U U U, and S == K (K V)^-1 U U U with V == (2b - 4)^+b.
   - K, b = 1: P == K (Z^+1)^+1 is a predecessor and S == K P^-1 (Z T)^+1.
   - L: L^-1 = A, L ((...(A^+b)...)^+b) (2b - 2 times) is x + b - 1, L A^+b subtracts b - 2, and
     S is their composition. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.
From Ltac2 Require Import Ltac2.
From UPRF Require Import Basic Prim Tactics Sec6 Robinson Thm67 Thm68 Rem69 ExtA ExtVb ExtGR.
Set Default Proof Mode "Classic".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The bases <X, F^+b, FG, F^-1> *)

Definition basisGRb (X : ufun) (b : nat) : basis :=
  Basis (fun F => F = X) (fun u => u = opPlusIb b \/ u = opInv) (fun c => c = comp).

Notation CbE b := (Clos (basisGRb funE b)).
Notation CbK b := (Clos (basisGRb funK b)).
Notation CbL b := (Clos (basisGRb funL b)).

(* for b = 0 this is the basis <X, F^+, FG, F^-1> of ExtGR *)
Lemma basisGRb0 X : basisGRb X 0 = basisGR0 X.
Proof. by rewrite /basisGRb /basisGR0 opPlusIb0. Qed.

(** * General facts *)

Lemma clos_iter_unop B u F : unops B u -> Clos B F -> forall n, Clos B (iter n u F).
Proof. by move=> hu hF; elim=> [//|n ih]; rewrite iterS; exact: clos_unop. Qed.

Lemma T_val b x : opPlusIb b funI x = 2 * x + b.
Proof. by rewrite /opPlusIb /funI; lia. Qed.

(* a predecessor recovers F^+: F^+ = P^b F^+b *)
Lemma plusI_from_pred P : (forall y, P y.+1 = y) -> forall b F, iter b P \o opPlusIb b F = opPlusI F.
Proof.
move=> hP b F; apply: functional_extensionality => x.
by rewrite /comp /opPlusIb /opPlusI (pred_pow hP).
Qed.

Lemma plusI_in_b X b P F : Clos (basisGRb X b) P -> (forall y, P y.+1 = y) ->
  Clos (basisGRb X b) F -> Clos (basisGRb X b) (opPlusI F).
Proof.
move=> hP hS hF; rewrite -(plusI_from_pred hS b F).
apply: (clos_powcomp (B := basisGRb X b) (erefl comp) hP); clos_solve.
Qed.

(* with 1 and a predecessor, the closure contains the basis <1, X, F^+, FG, F^-1> *)
Lemma GR_sub_GRb X b P : Clos (basisGRb X b) (cst 1) -> Clos (basisGRb X b) P ->
  (forall y, P y.+1 = y) -> forall F, Clos (basisGR X) F -> Clos (basisGRb X b) F.
Proof.
move=> one hP hS; apply: clos_subset.
- by move=> G [->|->]; [exact: one | clos_solve].
- by move=> u G [->|->] hG; [exact: plusI_in_b hP hS hG | clos_solve].
- by move=> c G H -> hG hH; clos_solve.
Qed.

(* conversely, F^+b = F^+ + b, so the closure lies in Robinson's *)
Lemma cst_in_GE n : CGE (cst n).
Proof.
elim: n => [|n ih]; first exact: zero_in_GE.
have -> : cst n.+1 = funS \o cst n by [].
by have ? := S_in_GE; clos_solve.
Qed.

Lemma opPlusIb_eq b F : opPlusIb b F = opPlus (opPlusI F) (cst b). Proof. by []. Qed.

Lemma GRb_sub_GE X b : CGE X -> forall F, Clos (basisGRb X b) F -> CGE F.
Proof.
move=> hX; apply: clos_subset.
- by move=> G ->.
- move=> u G [->|->] hG; last by clos_solve.
  rewrite opPlusIb_eq; apply: plus_in_GE; [clos_solve | exact: cst_in_GE].
- by move=> c G H -> hG hH; clos_solve.
Qed.

(** * The basis with E *)

Lemma E_shift_even b x m : 0 < b -> x + b <= 2 * m + 3 ->
  funE (opInv funE (2 * m) + x + b) = x + b - 1.
Proof.
move=> hb h; rewrite Einv_even.
by rewrite (@funE_at m.+1 (x + b - 1)) //; nia.
Qed.

Lemma E_shift_odd b x m : 1 < b -> x + b <= 2 * m + 6 ->
  funE (opInv funE (2 * m + 1) + x + b) = x + b - 2.
Proof.
move=> hb h; rewrite Einv_odd.
by rewrite (@funE_at m.+2 (x + b - 2)) //; nia.
Qed.

(* subtraction by inversion with E: an instance of sub_inv_val with base(t) = t^2 and
   bound(t) = 2t *)
Lemma E_dec y : exists t, y = t * t + funE y /\ funE y <= 2 * t.
Proof. by exists (funRt y); have := funE_add y; have := funE_bound y; lia. Qed.

Lemma E_diag t k : k <= 2 * t -> funE (t * t + k) = k.
Proof. exact: funE_sq_add. Qed.

Lemma E_big c z : exists t, z <= 2 * t /\ c <= t * t.
Proof. by exists (z + c); split; nia. Qed.

Lemma surj_E_shift V c : (forall y, V y = y + c) -> surj (funE \o V).
Proof. exact: (@sub_inv_surj funE V (fun t => t * t) (fun t => 2 * t) c E_diag (E_big c)). Qed.

Lemma E_sub_inv V c x : (forall y, V y = y + c) -> c <= x -> funE (opInv (funE \o V) x) = x - c.
Proof.
exact: (@sub_inv_val funE V (fun t => t * t) (fun t => 2 * t) c x E_dec E_diag (E_big c)).
Qed.

(** ** The successor, b >= 2 *)

Definition expW1 (b : nat) : ufun := funE \o opPlusIb b (opInv funE \o opPlusIb b funI).
Definition expW2 (b : nat) : ufun := funE \o opPlusIb b (opInv funE \o expW1 b \o opPlusIb b funI).

Lemma I_in_bE b : CbE b funI. Proof. by rewrite -I_expr_inv; clos_solve. Qed.
Lemma expW1_in b : CbE b (expW1 b). Proof. by rewrite /expW1; have ? := I_in_bE b; clos_solve. Qed.
Lemma expW2_in b : CbE b (expW2 b).
Proof. by rewrite /expW2; have ? := I_in_bE b; have ? := expW1_in b; clos_solve. Qed.

Lemma expW1_val b x : 1 < b -> expW1 b x = x + (if odd b then b - 2 else b - 1).
Proof.
move=> hb.
have e : expW1 b x = funE (opInv funE (opPlusIb b funI x) + x + b) by [].
rewrite e T_val; have hd := divn_eq b 2; rewrite modn2 in hd.
case hodd: (odd b); rewrite hodd /= in hd.
- have -> : 2 * x + b = 2 * (x + b %/ 2) + 1 by lia.
  by rewrite E_shift_odd; lia.
- have -> : 2 * x + b = 2 * (x + b %/ 2) by lia.
  by rewrite E_shift_even; lia.
Qed.

Lemma expW2_val b x : 1 < b -> expW2 b x = x + (if odd b then b - 1 else b - 2).
Proof.
move=> hb.
have e : expW2 b x = funE (opInv funE (expW1 b (opPlusIb b funI x)) + x + b) by [].
rewrite e T_val expW1_val //.
case hodd: (odd b).
- have -> : 2 * x + b + (b - 2) = 2 * (x + b - 1) by lia.
  by rewrite E_shift_even; lia.
- have -> : 2 * x + b + (b - 1) = 2 * (x + b - 1) + 1 by lia.
  by rewrite E_shift_odd; lia.
Qed.

(* U1(x) = x + b - 1 and U2(x) = x + b - 2 *)
Definition expU1 (b : nat) : ufun := if odd b then expW2 b else expW1 b.
Definition expU2 (b : nat) : ufun := if odd b then expW1 b else expW2 b.

Lemma expU1_val b x : 1 < b -> expU1 b x = x + (b - 1).
Proof.
by move=> hb; rewrite /expU1; case h: (odd b); rewrite ?expW1_val ?expW2_val ?h.
Qed.
Lemma expU2_val b x : 1 < b -> expU2 b x = x + (b - 2).
Proof.
by move=> hb; rewrite /expU2; case h: (odd b); rewrite ?expW1_val ?expW2_val ?h.
Qed.

Lemma expU1_in b : CbE b (expU1 b).
Proof. by rewrite /expU1; case: (odd b); [exact: expW2_in | exact: expW1_in]. Qed.
Lemma expU2_in b : CbE b (expU2 b).
Proof. by rewrite /expU2; case: (odd b); [exact: expW1_in | exact: expW2_in]. Qed.

Definition expSE2 (b : nat) : ufun := funE \o opInv (funE \o expU2 b) \o expU1 b.

Lemma expSE2_val b : 1 < b -> expSE2 b = funS.
Proof.
move=> hb; apply: functional_extensionality => x.
have hV y : expU2 b y = y + (b - 2) by rewrite expU2_val.
by rewrite /expSE2 /comp expU1_val // (E_sub_inv hV) /funS; lia.
Qed.

Lemma expSE2_in b : CbE b (expSE2 b).
Proof. by rewrite /expSE2; have ? := expU1_in b; have ? := expU2_in b; clos_solve. Qed.

(** ** The successor, b = 1 *)

Definition expPE1 : ufun := funE \o opPlusIb 1 (opInv funE \o opPlusIb 1 funI).

Lemma expPE1_val x : expPE1 x = funE (opInv funE (2 * x + 1) + x + 1).
Proof.
have e : expPE1 x = funE (opInv funE (opPlusIb 1 funI x) + x + 1) by [].
by rewrite e T_val.
Qed.

Lemma expPE1_succ y : expPE1 y.+1 = y.
Proof. by rewrite expPE1_val Einv_odd (@funE_at y.+3 y) //; nia. Qed.

Lemma expPE1_0 : expPE1 0 = 2.
Proof. by rewrite expPE1_val Einv_odd; case: funE_small. Qed.

Lemma surj_expPE1 : surj expPE1. Proof. by move=> y; exists y.+1; exact: expPE1_succ. Qed.

Lemma expPE1_inv v : v <> 2 -> opInv expPE1 v = v.+1.
Proof.
move=> hv; have e := opInv_right surj_expPE1 v.
case h: (opInv expPE1 v) e => [|y]; first by rewrite expPE1_0 => ev; case: hv.
by rewrite expPE1_succ => ->.
Qed.

Definition expSE1 : ufun :=
  funE \o opInv expPE1 \o opPlusIb 1 (opInv funE \o expPE1 \o opPlusIb 1 funI).

Lemma expSE1_val : expSE1 = funS.
Proof.
apply: functional_extensionality => x.
have d : expPE1 (opPlusIb 1 funI x) = 2 * x by rewrite T_val addn1 expPE1_succ.
have v : opPlusIb 1 (opInv funE \o expPE1 \o opPlusIb 1 funI) x = x * x + 3 * x + 1.
  have e : opPlusIb 1 (opInv funE \o expPE1 \o opPlusIb 1 funI) x
      = opInv funE (expPE1 (opPlusIb 1 funI x)) + x + 1 by [].
  by rewrite e d Einv_even; lia.
have v2 : x * x + 3 * x + 1 <> 2 by case: x {d v} => [|x]; nia.
rewrite /expSE1 /comp v expPE1_inv // /funS.
by rewrite (@funE_at x.+1 x.+1) //; nia.
Qed.

Lemma expSE1_in : CbE 1 expSE1.
Proof.
have ? := I_in_bE 1.
have ? : CbE 1 expPE1 by rewrite /expPE1; clos_solve.
by rewrite /expSE1; clos_solve.
Qed.

(** ** The basis with E generates Robinson's closure *)

Lemma S_in_bE b : 0 < b -> CbE b funS.
Proof.
move=> hb; case: (ltnP b 2) => h.
- have -> : b = 1 by lia.
  by rewrite -expSE1_val; exact: expSE1_in.
- by rewrite -(expSE2_val h); exact: expSE2_in.
Qed.

(* the predecessor E (E S)^-1 *)
Lemma predE_succ y : (funE \o opInv (funE \o funS)) y.+1 = y.
Proof.
have hV z : funS z = z + 1 by rewrite /funS addn1.
change (funE (opInv (funE \o funS) y.+1) = y).
by rewrite (E_sub_inv hV); lia.
Qed.

Lemma zeroE_b : funE \o funS \o opInv funE \o opPlusI funI = cst 0.
Proof.
apply: functional_extensionality => x; rewrite /comp.
have -> : opPlusI funI x = 2 * x by rewrite /opPlusI /funI; lia.
by rewrite Einv_even /funS /cst (@funE_at x.+1 0) //; nia.
Qed.

Lemma GE_sub_bE b : 0 < b -> forall F, CGE F -> CbE b F.
Proof.
move=> hb; have S := S_in_bE hb.
have P : CbE b (funE \o opInv (funE \o funS)) by clos_solve.
have D : CbE b (opPlusI funI) := plusI_in_b P predE_succ (I_in_bE b).
have z : CbE b (cst 0) by rewrite -zeroE_b; clos_solve.
have one : CbE b (cst 1) by rewrite -one_expr; clos_solve.
exact: GR_sub_GRb one P predE_succ.
Qed.

Theorem GRb_E_eq_JR b : 0 < b -> forall F, CbE b F <-> CJR F.
Proof.
move=> hb F; split=> h.
- by apply: GE_sub_JR; apply: (GRb_sub_GE (X := funE) (b := b)) h; clos_solve.
- by apply: GE_sub_bE; [exact: hb | exact: JR_sub_GE].
Qed.

(** * The basis with K *)

Lemma Z_in_bK b : CbK b funZ. Proof. by rewrite -Kinv_eq_Z; clos_solve. Qed.

Lemma KZ_I : funK \o funZ = funI.
Proof. by apply: functional_extensionality => x; rewrite /comp KZ. Qed.

Lemma I_in_bK b : CbK b funI. Proof. by rewrite -KZ_I; have ? := Z_in_bK b; clos_solve. Qed.

Lemma le_funA n : n <= funA n. Proof. by have ? := two_funA n; nia. Qed.

(* subtraction by inversion with K: an instance of sub_inv_val with base = A and
   bound(t) = t *)
Lemma K_dec y : exists t, y = funA t + funK y /\ funK y <= id t.
Proof. by exists (funV y); exact: decomp. Qed.

Lemma K_diag t k : k <= id t -> funK (funA t + k) = k.
Proof. exact: funK_diag. Qed.

Lemma K_big c z : exists t, z <= id t /\ c <= funA t.
Proof. by exists (z + c); have ? := le_funA (z + c); rewrite /id; split; lia. Qed.

Lemma surj_K_shift V c : (forall y, V y = y + c) -> surj (funK \o V).
Proof. exact: (@sub_inv_surj funK V funA id c K_diag (K_big c)). Qed.

Lemma K_sub_inv V c x : (forall y, V y = y + c) -> c <= x -> funK (opInv (funK \o V) x) = x - c.
Proof. exact: (@sub_inv_val funK V funA id c x K_dec K_diag (K_big c)). Qed.

(* U == K (Z T)^+b, U(x) = x + b - 1 *)
Definition expUK (b : nat) : ufun := funK \o opPlusIb b (funZ \o opPlusIb b funI).

Lemma expUK_val b x : 0 < b -> expUK b x = x + (b - 1).
Proof.
move=> hb.
have e : expUK b x = funK (funZ (opPlusIb b funI x) + x + b) by [].
rewrite e T_val /funZ.
have ? := funA_succ (2 * x + b).
have -> : funA (2 * x + b) + (2 * x + b) + x + b = funA (2 * x + b).+1 + (x + (b - 1)) by lia.
by rewrite funK_diag //; lia.
Qed.

Lemma expUK_in b : CbK b (expUK b).
Proof. by rewrite /expUK; have ? := Z_in_bK b; have ? := I_in_bK b; clos_solve. Qed.

(** ** The successor, b >= 2 *)

Definition expP1K (b : nat) : ufun := funK \o opInv (funK \o expUK b).
Definition expCK (b : nat) : ufun :=
  funK \o opPlusIb b (funZ \o expP1K b) \o expUK b \o expUK b \o expUK b.
Definition expSK2 (b : nat) : ufun :=
  funK \o opInv (funK \o opPlusIb b (expCK b)) \o expUK b \o expUK b \o expUK b.

Lemma expP1K_val b x : 0 < b -> b - 1 <= x -> expP1K b x = x - (b - 1).
Proof. by move=> hb hx; rewrite /expP1K /comp (@K_sub_inv (expUK b) (b - 1)) // => y; rewrite expUK_val. Qed.

(* the constant 2b - 4 *)
Lemma expCK_val b x : 1 < b -> expCK b x = 2 * b - 4.
Proof.
move=> hb.
have u3 : expUK b (expUK b (expUK b x)) = x + 3 * (b - 1) by rewrite !expUK_val //; lia.
have p : expP1K b (x + 3 * (b - 1)) = x + 2 * (b - 1) by rewrite expP1K_val //; lia.
rewrite /expCK /comp u3 /opPlusIb p /funZ.
have ? := funA_succ (x + 2 * (b - 1)); have ? := funA_succ (x + 2 * (b - 1)).+1.
have -> : funA (x + 2 * (b - 1)) + (x + 2 * (b - 1)) + (x + 3 * (b - 1)) + b
    = funA (x + 2 * (b - 1)).+2 + (2 * b - 4) by lia.
by rewrite funK_diag //; lia.
Qed.

Lemma expSK2_val b : 1 < b -> expSK2 b = funS.
Proof.
move=> hb; apply: functional_extensionality => x.
have V y : opPlusIb b (expCK b) y = y + (3 * b - 4) by rewrite /opPlusIb expCK_val //; lia.
have u3 : expUK b (expUK b (expUK b x)) = x + 3 * (b - 1) by rewrite !expUK_val //; lia.
rewrite /expSK2 /comp u3 (@K_sub_inv _ (3 * b - 4)) // /funS; lia.
Qed.

Lemma expSK2_in b : CbK b (expSK2 b).
Proof.
have ? := expUK_in b; have ? := Z_in_bK b.
have ? : CbK b (expP1K b) by rewrite /expP1K; clos_solve.
have ? : CbK b (expCK b) by rewrite /expCK; clos_solve.
by rewrite /expSK2; clos_solve.
Qed.

(** ** The successor, b = 1 *)

Definition expPK1 : ufun := funK \o opPlusIb 1 (opPlusIb 1 funZ).

Lemma expPK1_succ y : expPK1 y.+1 = y.
Proof.
rewrite /expPK1 /comp /opPlusIb /funZ.
have ? := funA_succ y.+1; have ? := funA_succ y.+2.
have -> : funA y.+1 + y.+1 + y.+1 + 1 + y.+1 + 1 = funA y.+3 + y by lia.
by rewrite funK_diag //; lia.
Qed.

Lemma expPK1_0 : expPK1 0 = 1.
Proof.
rewrite /expPK1 /comp /opPlusIb /funZ funA0.
by have := funK_diag (k := 1) (t := 1) (leqnn 1); rewrite funA1.
Qed.

Lemma surj_expPK1 : surj expPK1. Proof. by move=> y; exists y.+1; exact: expPK1_succ. Qed.

Lemma expPK1_inv v : v <> 1 -> opInv expPK1 v = v.+1.
Proof.
move=> hv; have e := opInv_right surj_expPK1 v.
case h: (opInv expPK1 v) e => [|y]; first by rewrite expPK1_0 => ev; case: hv.
by rewrite expPK1_succ => ->.
Qed.

Definition expSK1 : ufun := funK \o opInv expPK1 \o opPlusIb 1 (funZ \o opPlusIb 1 funI).

Lemma expSK1_val : expSK1 = funS.
Proof.
apply: functional_extensionality => x.
have ? := funA_succ (2 * x + 1).
have v : opPlusIb 1 (funZ \o opPlusIb 1 funI) x = funA (2 * x + 1).+1 + x.
  have e : opPlusIb 1 (funZ \o opPlusIb 1 funI) x = funZ (opPlusIb 1 funI x) + x + 1 by [].
  by rewrite e T_val /funZ; lia.
have v1 : funA (2 * x + 1).+1 + x <> 1.
  have ? := funA_mono (m := 2) (n := (2 * x + 1).+1) ltac:(lia).
  have : funA 2 = 3 by have ? := two_funA 2; lia.
  lia.
rewrite /expSK1 /comp v expPK1_inv // /funS.
have -> : (funA (2 * x + 1).+1 + x).+1 = funA (2 * x + 1).+1 + x.+1 by lia.
by rewrite funK_diag //; lia.
Qed.

Lemma expSK1_in : CbK 1 expSK1.
Proof.
have ? := Z_in_bK 1; have ? := I_in_bK 1.
have ? : CbK 1 expPK1 by rewrite /expPK1; clos_solve.
by rewrite /expSK1; clos_solve.
Qed.

(** ** The basis with K generates Robinson's closure *)

Lemma S_in_bK b : 0 < b -> CbK b funS.
Proof.
move=> hb; case: (ltnP b 2) => h.
- have -> : b = 1 by lia.
  by rewrite -expSK1_val; exact: expSK1_in.
- by rewrite -(expSK2_val h); exact: expSK2_in.
Qed.

Lemma A0_K : funK \o funA = cst 0.
Proof.
apply: functional_extensionality => x; rewrite /comp /cst.
by have := funK_diag (k := 0) (t := x) (leq0n x); rewrite addn0.
Qed.

Lemma GK_sub_bK b : 0 < b -> forall F, CGK F -> CbK b F.
Proof.
move=> hb; have S := S_in_bK hb.
have P : CbK b funPred by rewrite -P_expr_K; clos_solve.
have Z := Z_in_bK b.
have pI F : CbK b F -> CbK b (opPlusI F) by move=> h; exact: plusI_in_b P P_succ h.
have A : CbK b funA.
  rewrite -A_expr_K /exprAK.
  have h1 : CbK b (opPlusI funZ) := pI _ Z.
  have h2 : CbK b (opPlusI (funZ \o opPlusI funZ \o funK)) by apply: pI; clos_solve.
  have h3 : CbK b (opPlusI (opPlusI (funZ \o opPlusI funZ \o funK) \o funZ \o funK)).
    by apply: pI; clos_solve.
  clos_solve.
have z : CbK b (cst 0) by rewrite -A0_K; clos_solve.
have one : CbK b (cst 1) by rewrite -one_expr; clos_solve.
exact: GR_sub_GRb one P P_succ.
Qed.

Theorem GRb_K_eq_JR b : 0 < b -> forall F, CbK b F <-> CJR F.
Proof.
move=> hb F; split=> h.
- by apply: GE_sub_JR; apply: (GRb_sub_GE (X := funK) (b := b)) h; exact: K_in_GE.
- by apply: GK_sub_bK; [exact: hb | apply: GE_sub_GK; exact: JR_sub_GE].
Qed.

(** * The basis with L *)

Lemma surj_funL : surj funL.
Proof. by move=> x; exists (funA x); have := funL_diag (k := 0) (t := x) (leq0n x); rewrite addn0 subn0. Qed.

(* L^-1 = A *)
Lemma Linv_eq_A : opInv funL = funA.
Proof.
apply: functional_extensionality => x; inv_eq surj_funL.
- by have := funL_diag (k := 0) (t := x) (leq0n x); rewrite addn0 subn0.
- move=> y hy; have [d1 d2] := decomp y.
  have hl := funL_eq y; rewrite hy in hl.
  have ? := funA_mono (m := x) (n := funV y) ltac:(lia).
  lia.
Qed.

Lemma A_in_bL b : CbL b funA. Proof. by rewrite -Linv_eq_A; clos_solve. Qed.

Lemma iter_A b n x : iter n (opPlusIb b) funA x = funA x + n * (x + b).
Proof. by elim: n => [|n ih]; rewrite ?mul0n ?addn0 // iterS /opPlusIb ih; nia. Qed.

Lemma funA_add x n : funA (x + n) = funA x + n * x + funA n.
Proof. by have ? := two_funA (x + n); have ? := two_funA x; have ? := two_funA n; nia. Qed.

(* U == L (...(A^+b)...)^+b (2b - 2 times), U(x) = x + b - 1 *)
Definition expUL (b : nat) : ufun := funL \o iter (2 * b - 2) (opPlusIb b) funA.

Lemma expUL_val b x : 0 < b -> expUL b x = x + (b - 1).
Proof.
move=> hb; rewrite /expUL /comp iter_A.
have sfc : funA (2 * (b - 1)) = 2 * (b - 1) * (b - 1) + (b - 1).
  by have ? := two_funA (2 * (b - 1)); nia.
have ? := funA_add x (2 * (b - 1)).
have -> : funA x + (2 * b - 2) * (x + b) = funA (x + 2 * (b - 1)) + (b - 1) by nia.
by rewrite funL_diag //; lia.
Qed.

(* L A^+b subtracts b - 2: A(y) + y + b = A(y + 1) + (b - 1) *)
Lemma sigmaL_val b y : 0 < b -> b - 1 <= y.+1 -> (funL \o opPlusIb b funA) y = y.+1 - (b - 1).
Proof.
move=> hb h; rewrite /comp /opPlusIb.
have ? := funA_succ y.
have -> : funA y + y + b = funA y.+1 + (b - 1) by lia.
by rewrite funL_diag.
Qed.

Definition expSL (b : nat) : ufun := funL \o opPlusIb b funA \o expUL b.

Lemma expSL_val b : 0 < b -> expSL b = funS.
Proof.
move=> hb; apply: functional_extensionality => x.
have := @sigmaL_val b (x + (b - 1)) hb ltac:(lia).
rewrite /expSL /comp expUL_val // /funS => ->; lia.
Qed.

Lemma expSL_in b : CbL b (expSL b).
Proof.
have A := A_in_bL b.
have ? : CbL b (iter (2 * b - 2) (opPlusIb b) funA).
  by apply: clos_iter_unop A _; left.
by rewrite /expSL /expUL; clos_solve.
Qed.

(* the predecessor L S A and the constant 0 == L A^+ *)
Lemma predL_succ y : (funL \o funS \o funA) y.+1 = y.
Proof. by rewrite /comp /funS -addn1 funL_diag //; lia. Qed.

Lemma zeroL : funL \o opPlusI funA = cst 0.
Proof. by apply: functional_extensionality => x; rewrite /comp /opPlusI /cst funL_diag // subnn. Qed.

Lemma GL_sub_bL b : 0 < b -> forall F, CGL F -> CbL b F.
Proof.
move=> hb; have S : CbL b funS by rewrite -(expSL_val hb); exact: expSL_in.
have A := A_in_bL b.
have P : CbL b (funL \o funS \o funA) by clos_solve.
have pA : CbL b (opPlusI funA) := plusI_in_b P predL_succ A.
have z : CbL b (cst 0) by rewrite -zeroL; clos_solve.
have one : CbL b (cst 1) by rewrite -one_expr; clos_solve.
exact: GR_sub_GRb one P predL_succ.
Qed.

Theorem GRb_L_eq_JR b : 0 < b -> forall F, CbL b F <-> CJR F.
Proof.
move=> hb F; split=> h.
- by apply: GE_sub_JR; apply: (GRb_sub_GE (X := funL) (b := b)) h; exact: L_in_GE.
- by apply: GL_sub_bL; [exact: hb | apply: GK_sub_GL; apply: GE_sub_GK; exact: JR_sub_GE].
Qed.

(** * Assuming Robinson's theorem *)

Theorem Ext_GRb_iff (GR : ufun -> Prop) : (forall F, CJR F <-> GR F) -> forall b,
  [/\ (forall F, CbE b F <-> GR F) <-> 0 < b, (forall F, CbK b F <-> GR F) <-> 0 < b
    & (forall F, CbL b F <-> GR F) <-> 0 < b].
Proof.
move=> hJR b; case: (Ext_GR0 hJR) => nE nK nL.
case: b => [|b].
- have z (P : Prop) : 0 < 0 -> P by rewrite ltnn.
  rewrite !basisGRb0; split; split; first [exact: z | move=> h].
  + by case: (nE h).
  + by case: (nK h).
  + by case: (nL h).
- split; split=> // _ F.
  + by rewrite GRb_E_eq_JR.
  + by rewrite GRb_K_eq_JR.
  + by rewrite GRb_L_eq_JR.
Qed.
