(* D. E. Severin, "Unary primitive recursive functions", J. Symbolic Logic 73(4), 2008.

   Section 2 (notation), bases and closures, Definition 3.2 (suitable bases), and
   the elementary arithmetic used silently in the paper.

   Naming: a function X of the paper is funX, an operator is opX; the juxtaposition
   FG of the paper is F \o G. *)

From Stdlib Require Import PeanoNat FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* one-argument functions N -> N *)
Definition ufun := nat -> nat.

(** * Section 2: basic and arithmetic functions *)

Definition funI : ufun := fun x => x.
Definition cst (n : nat) : ufun := fun _ => n.
Definition funS : ufun := fun x => x.+1.
Definition funD : ufun := fun x => 2 * x.
Definition funSq : ufun := fun x => x * x.
Definition funHf : ufun := fun x => x %/ 2.
Definition funRt : ufun := Nat.sqrt.
Definition funE : ufun := fun x => x - funRt x * funRt x.
Definition funO : ufun := fun x => if x == 0 then 1 else 0.
Definition funSgn : ufun := fun x => if x == 0 then 0 else 1.

(* Cantor pairing: A(x) = x(x+1)/2, V(x) = (Rt(8x+1) - 1)/2,
   K(x) = x - A(V(x)), L(x) = A(V(x)+1) - x - 1, J(x,y) = A(x+y) + x *)
Definition funA : ufun := fun x => (x * x + x) %/ 2.
Definition funV : ufun := fun x => (funRt (8 * x + 1) - 1) %/ 2.
Definition funK : ufun := fun x => x - funA (funV x).
Definition funL : ufun := fun x => funA (funV x + 1) - x - 1.
Definition funJ (x y : nat) : nat := funA (x + y) + x.

(** * Operators *)

Definition opPlusI (F : ufun) : ufun := fun x => F x + x.
Definition opPlus (F G : ufun) : ufun := fun x => F x + G x.
Definition opMinus (F G : ufun) : ufun := fun x => F x - G x.

(* iteration F^box(a): F^box(a)(0) = a, F^box(a)(x+1) = F(F^box(a)(x)) *)
Definition opBoxA (a : nat) (F : ufun) : ufun := fun n => iter n F a.
Definition opBox (F : ufun) : ufun := opBoxA 0 F.

Lemma opBox0 F : opBox F 0 = 0. Proof. by []. Qed.
Lemma opBoxS F n : opBox F n.+1 = F (opBox F n). Proof. by []. Qed.
Lemma opBoxA0 a F : opBoxA a F 0 = a. Proof. by []. Qed.
Lemma opBoxAS a F n : opBoxA a F n.+1 = F (opBoxA a F n). Proof. by []. Qed.

(** * Bases and closures (end of Section 2) *)

(* A basis <F1,...,Fn, F^op,..., F op G,...>: initial functions, unary and binary operators *)
Record basis := Basis {
  inits : ufun -> Prop;
  unops : (ufun -> ufun) -> Prop;
  binops : (ufun -> ufun -> ufun) -> Prop }.

(* clos B: the least set containing the initial functions, closed under the operators *)
Inductive Clos (B : basis) : ufun -> Prop :=
  | clos_init F : inits B F -> Clos B F
  | clos_unop u F : unops B u -> Clos B F -> Clos B (u F)
  | clos_binop b F G : binops B b -> Clos B F -> Clos B G -> Clos B (b F G).

(** * Primitive recursive functions Prim(N,N)

   Prim(N,N) is defined by the standard characterization of the primitive recursive
   functions of one variable through Cantor's pairing: 0, S and the inverses K, L of the
   pairing, closed under composition, pairing J(F, G) and the unary recursion operator
   below (primitive recursion with parameters reduces to it by pairing; cf. R. M. Robinson,
   Primitive recursive functions, Bull. AMS 53 (1947), Section 3). *)

(* f(0, x) = g(x),  f(y+1, x) = h(J(J(y, f(y, x)), x)) *)
Fixpoint recF (g h : ufun) (y x : nat) : nat :=
  if y is y'.+1 then h (funJ (funJ y' (recF g h y' x)) x) else g x.

Definition unaryRec (g h : ufun) : ufun := fun z => recF g h (funK z) (funL z).

Inductive PrimNN : ufun -> Prop :=
  | pr_zero : PrimNN (cst 0)
  | pr_succ : PrimNN funS
  | pr_fst : PrimNN funK
  | pr_snd : PrimNN funL
  | pr_comp f g : PrimNN f -> PrimNN g -> PrimNN (f \o g)
  | pr_pair f g : PrimNN f -> PrimNN g -> PrimNN (fun x => funJ (f x) (g x))
  | pr_rec g h : PrimNN g -> PrimNN h -> PrimNN (unaryRec g h).

(* Definition 3.2 *)
Definition suitable (B : basis) : Prop := forall F, Clos B F <-> PrimNN F.

Lemma clos_subset (B1 B2 : basis) :
  (forall F, inits B1 F -> Clos B2 F) ->
  (forall u F, unops B1 u -> Clos B2 F -> Clos B2 (u F)) ->
  (forall b F G, binops B1 b -> Clos B2 F -> Clos B2 G -> Clos B2 (b F G)) ->
  forall F, Clos B1 F -> Clos B2 F.
Proof. by move=> I U Bi F; elim=> [? /I|u ? /U H _|b ? ? /Bi H _ ? _]; auto. Qed.

Lemma clos_sound (B : basis) :
  (forall F, inits B F -> PrimNN F) ->
  (forall u F, unops B u -> PrimNN F -> PrimNN (u F)) ->
  (forall b F G, binops B b -> PrimNN F -> PrimNN G -> PrimNN (b F G)) ->
  forall F, Clos B F -> PrimNN F.
Proof. by move=> I U Bi F; elim=> [? /I|u ? /U H _|b ? ? /Bi H _ ? _]; auto. Qed.

Lemma suitable_by_simulation (B1 B2 : basis) :
  suitable B1 ->
  (forall F, inits B1 F -> Clos B2 F) ->
  (forall u F, unops B1 u -> Clos B2 F -> Clos B2 (u F)) ->
  (forall b F G, binops B1 b -> Clos B2 F -> Clos B2 G -> Clos B2 (b F G)) ->
  (forall F, Clos B2 F -> PrimNN F) -> suitable B2.
Proof.
move=> S I U Bi P F; split; first exact: P.
by move/(S F)=> /(clos_subset I U Bi).
Qed.

(** * Arithmetic facts used silently in the paper *)

Lemma funRt_spec n : funRt n * funRt n <= n < (funRt n).+1 * (funRt n).+1.
Proof. by have := Nat.sqrt_spec n; rewrite /funRt; lia. Qed.

Lemma funRt_sq_le n : funRt n * funRt n <= n.
Proof. by case/andP: (funRt_spec n). Qed.

Lemma funRt_lt n : n < (funRt n).+1 * (funRt n).+1.
Proof. by case/andP: (funRt_spec n). Qed.

Lemma funRt_unique r n : r * r <= n -> n < r.+1 * r.+1 -> funRt n = r.
Proof. by move=> h1 h2; apply: Nat.sqrt_unique; lia. Qed.

(* Rt(m^2 + k) = m and E(m^2 + k) = k whenever k <= 2m *)
Lemma funRt_sq_add m k : k <= 2 * m -> funRt (m * m + k) = m.
Proof. by move=> h; apply: funRt_unique; nia. Qed.

Lemma funE_sq_add m k : k <= 2 * m -> funE (m * m + k) = k.
Proof. by move=> h; rewrite /funE funRt_sq_add //; lia. Qed.

Lemma funRt_sq m : funRt (m * m) = m.
Proof. by have := funRt_sq_add (m := m) (k := 0); rewrite addn0; apply; lia. Qed.

Lemma funE_add x : funE x + funRt x * funRt x = x.
Proof. by have := funRt_sq_le x; rewrite /funE; lia. Qed.

(* Robinson's difference formula: if b <= a then a - b = E((a+b)^2 + 3a + b + 1) *)
Lemma robinson_diff_E a b : b <= a -> funE ((a + b) * (a + b) + 3 * a + b + 1) = a - b.
Proof.
move=> h; have -> : (a + b) * (a + b) + 3 * a + b + 1
                    = (a + b).+1 * (a + b).+1 + (a - b) by nia.
by rewrite funE_sq_add //; lia.
Qed.

(* Cantor pairing *)

Lemma two_funA x : 2 * funA x = x * x + x.
Proof.
rewrite /funA; have: ~~ odd (x * x + x) by rewrite oddD oddM andbb addbb.
by move/negbTE=> ev; rewrite [in RHS](divn_eq (x * x + x) 2) modn2 ev; lia.
Qed.

Lemma funA_succ x : funA x.+1 = funA x + x + 1.
Proof. by have := two_funA x; have := two_funA x.+1; nia. Qed.

Lemma funA_mono m n : m <= n -> funA m <= funA n.
Proof. by move=> h; have := two_funA m; have := two_funA n; nia. Qed.

Lemma funA_lt_imp m n : funA m < funA n -> m < n.
Proof. by move=> h; rewrite ltnNge; apply/negP=> /funA_mono; lia. Qed.

(* V is the inverse of A: if A(t) <= x < A(t+1) then V(x) = t *)
Lemma funV_char t x : funA t <= x -> x < funA t.+1 -> funV x = t.
Proof.
move=> h1 h2; have a := two_funA t; have b := two_funA t.+1.
have lo : (2 * t + 1) * (2 * t + 1) <= 8 * x + 1 by nia.
have hi : 8 * x + 1 < (2 * t + 3) * (2 * t + 3) by nia.
rewrite /funV.
have [r [hr ->]] : exists r, r <= 1 /\ funRt (8 * x + 1) = 2 * t + 1 + r.
  case: (leqP ((2 * t + 2) * (2 * t + 2)) (8 * x + 1)) => hc.
  - by exists 1; split=> //; apply: funRt_unique; nia.
  - by exists 0; split=> //; apply: funRt_unique; nia.
have -> : 2 * t + 1 + r - 1 = r + t * 2 by lia.
by rewrite divnDr ?dvdn_mull // mulnK // divn_small; lia.
Qed.

Lemma funA_index x : exists t, funA t <= x < funA t.+1.
Proof.
elim: x => [|x [t /andP [h1 h2]]]; first by exists 0.
case: (ltnP x.+1 (funA t.+1)) => h; first by exists t; lia.
by exists t.+1; have := funA_succ t.+1; lia.
Qed.

(* values on a diagonal of the Cantor table: for k <= t,
   V(A(t)+k) = t, K(A(t)+k) = k and L(A(t)+k) = t - k *)
Lemma funV_diag k t : k <= t -> funV (funA t + k) = t.
Proof. by move=> h; apply: funV_char; have := funA_succ t; lia. Qed.

Lemma funK_diag k t : k <= t -> funK (funA t + k) = k.
Proof. by move=> h; rewrite /funK funV_diag //; lia. Qed.

Lemma funL_diag k t : k <= t -> funL (funA t + k) = t - k.
Proof. by move=> h; rewrite /funL funV_diag // addn1 funA_succ; lia. Qed.

Lemma decomp x : x = funA (funV x) + funK x /\ funK x <= funV x.
Proof.
have [t /andP [h1 h2]] := funA_index x.
rewrite /funK (funV_char h1 h2); have := funA_succ t; lia.
Qed.

Lemma funL_eq x : funL x = funV x - funK x.
Proof. by have [h1 h2] := decomp x; rewrite [in LHS]h1 funL_diag. Qed.

Lemma funK_J x y : funK (funJ x y) = x.
Proof. by rewrite /funJ funK_diag //; lia. Qed.

Lemma funL_J x y : funL (funJ x y) = y.
Proof. by rewrite /funJ funL_diag //; lia. Qed.

Lemma funJ_KL z : funJ (funK z) (funL z) = z.
Proof. by have [h1 h2] := decomp z; rewrite /funJ funL_eq subnKC // -h1. Qed.
