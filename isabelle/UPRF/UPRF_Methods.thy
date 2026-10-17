(*  Title:   UPRF_Methods.thy

    Eisbach proof methods for the three mechanisms that recur in the proofs:

    - clos_solve      membership in a closure, F \<in> clos B.  F is decomposed with the generic
                      closure rules (one per operator, collected in clos_rules), the membership
                      lemmas registered in clos_rules and the facts given with "add:"; what is
                      left is closed by assumption, by an initial function of B, or by
                      unfolding the basis definitions collected in clos_defs.
    - clos_sound_m    soundness of a closure, clos B \<subseteq> PrimNN (clos_sound followed by the
                      primitive recursiveness lemmas collected in prim_intros).
    - clos_subset_m   an inclusion clos B1 \<subseteq> clos B2 (clos_subset followed by clos_solve).
    - simulate S      a whole suitable_by_simulation proof from the suitable basis S.
    - eval            the value of an expression at a point: the operators and the basic
                      functions are unfolded (eval_simps, with the value lemmas given with
                      "add:"), and the arithmetic goal that is left is tried with simp and
                      linarith.
    (The method inv_eq, for equalities with the inversion F\<^sup>-\<^sup>1, is in UPRF_Ext_GR.)
*)

theory UPRF_Methods
  imports UPRF_Aux "HOL-Eisbach.Eisbach"
begin

section \<open>Proof methods\<close>

named_theorems clos_defs "selector equations of the bases (inits B = ..., unops B = ..., binops B = ...)"
named_theorems clos_rules "introduction rules for membership in a closure"
named_theorems prim_intros "introduction rules for primitive recursiveness"
named_theorems eval_simps "unfolding equations of the operators and basic functions, for eval"

declare comp_apply [eval_simps] opPlus_def [eval_simps]
  funI_def [eval_simps] cst_def [eval_simps] funS_def [eval_simps] funD_def [eval_simps]
  funSq_def [eval_simps]

subsection \<open>Generic closure rules, one per operator\<close>

text \<open>Each rule fixes the operator, so the unification with the goal stays first order.\<close>
lemma clos_comp_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> G \<in> clos B \<Longrightarrow> (\<circ>) \<in> binops B \<Longrightarrow> F \<circ> G \<in> clos B"
  using clos_binop[of "(\<circ>)" B F G] by simp

lemma clos_plus_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> G \<in> clos B \<Longrightarrow> opPlus \<in> binops B \<Longrightarrow> opPlus F G \<in> clos B"
  using clos_binop[of opPlus B F G] by simp

lemma clos_box_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> opBox \<in> unops B \<Longrightarrow> opBox F \<in> clos B"
  using clos_unop[of opBox B F] by simp

lemma clos_boxA_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> opBoxA a \<in> unops B \<Longrightarrow> opBoxA a F \<in> clos B"
  using clos_unop[of "opBoxA a" B F] by simp

declare funS_PR [prim_intros] cst_PR [prim_intros] funI_PR [prim_intros]
  funSq_PR [prim_intros] funO_PR [prim_intros] funHf_PR [prim_intros] funRt_PR [prim_intros]
  funE_PR [prim_intros] funK_PR [prim_intros] funL_PR [prim_intros] comp_PR [prim_intros]
  opPlus_PR [prim_intros] opBoxA_PR [prim_intros] opBox_PR [prim_intros]

subsection \<open>The methods\<close>

text \<open>Membership in a closure.  A goal is closed by an assumption, or it is a side condition
  on the basis (\<open>op \<in> unops B\<close>, \<open>F \<in> inits B\<close>, \<dots>) solved by \<open>simp\<close> with the basis
  definitions, or a rule decomposes it (backtracking to the next rule when a side condition
  fails), or it is an initial function of the basis.\<close>
method clos_solve uses add =
  (assumption
   | solves \<open>simp add: clos_defs\<close>
   | (rule add clos_rules; clos_solve add: add)
   | (rule clos_init; solves \<open>simp add: clos_defs\<close>))

text \<open>Case analysis on the membership in a basis: the selector equations turn
  \<open>F \<in> inits B\<close>, \<open>u \<in> unops B\<close>, \<open>b \<in> binops B\<close> into disjunctions of equations, which are
  split and substituted (with \<open>simp only\<close>, so the functions are not normalized).\<close>
method basis_cases =
  ((simp only: clos_defs applyU_def applyB_def subset_iff insert_iff empty_iff)?;
     (intro allI impI)?; (elim disjE FalseE)?; (hypsubst_thin)?)

text \<open>Soundness of a closure.\<close>
method clos_sound_m uses add =
  (rule clos_sound; basis_cases; (intro add prim_intros)?; assumption?)

text \<open>An inclusion \<open>clos B\<^sub>1 \<subseteq> clos B\<^sub>2\<close>: the initial functions and the operators of
  \<open>B\<^sub>1\<close> are generated in \<open>clos B\<^sub>2\<close> (with the membership facts given with "add:").\<close>
method clos_subset_m uses add =
  (rule clos_subset; basis_cases; clos_solve add: add)

text \<open>The value of an expression at a point.  Only the unfolding equations are used for the
  rewriting (so that the value lemmas given with "add:" still match); then the arithmetic goal
  is tried with \<open>simp\<close> and \<open>linarith\<close>, and left to the user if both fail.\<close>
method eval uses add =
  ((simp only: eval_simps add)?;
     (solves \<open>simp add: add\<close> | solves \<open>linarith\<close> | solves \<open>simp add: algebra_simps add\<close>
      | succeed))

text \<open>A suitability proof by simulation of the suitable basis \<open>S\<close>: as above, and the
  closure is sound (with the primitive recursiveness facts given with "prim:").\<close>
method simulate uses S add prim =
  (rule suitable_by_simulation[OF S];
     (clos_sound_m add: prim | (basis_cases; clos_solve add: add)))

end
