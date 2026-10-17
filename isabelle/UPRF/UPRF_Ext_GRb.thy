(*  Title:   UPRF_Ext_GRb.thy

    The general recursive analogue of the shifted operator of UPRF_Ext_Vb: for X \<in> {E, K, L},

       clos \<langle>X, F\<^sup>+\<^sup>b, FG, F\<^sup>-\<^sup>1\<rangle> = clos \<langle>S, E, F + G, FG, F\<^sup>-\<^sup>1\<rangle>   iff   b \<ge> 1,

    where F\<^sup>+\<^sup>b(x) = F(x) + x + b.  So, assuming J. Robinson's theorem, these bases generate
    exactly the unary general recursive functions when b \<ge> 1, and not when b = 0 (then every
    generated function fixes 0, UPRF_Ext_GR).

    In each case a successor S is generated first; then a predecessor P (P(x + 1) = x) gives
    F\<^sup>+ \<equiv> P\<^sup>b F\<^sup>+\<^sup>b and the constant 1, so the closure contains the basis \<langle>1, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>
    of UPRF_Ext_GR.  With T \<equiv> I\<^sup>+\<^sup>b (T(x) = 2x + b):
    - E, b \<ge> 2:  E (E\<^sup>-\<^sup>1 T)\<^sup>+\<^sup>b and E (E\<^sup>-\<^sup>1 (E (E\<^sup>-\<^sup>1 T)\<^sup>+\<^sup>b) T)\<^sup>+\<^sup>b are the shifts x + b - 1 and
      x + b - 2 (in an order that depends on the parity of b); if V(x) = x + c then
      E (E V)\<^sup>-\<^sup>1 subtracts c, and S \<equiv> E (E U\<^sub>2)\<^sup>-\<^sup>1 U\<^sub>1.
    - E, b = 1:  P \<equiv> E (E\<^sup>-\<^sup>1 T)\<^sup>+\<^sup>1 is a predecessor and S \<equiv> E P\<^sup>-\<^sup>1 (E\<^sup>-\<^sup>1 P T)\<^sup>+\<^sup>1.
    - K, b \<ge> 2:  U \<equiv> K (Z T)\<^sup>+\<^sup>b is x + b - 1 (Z = K\<^sup>-\<^sup>1), the constant 2b - 4 is
      K (Z K (K U)\<^sup>-\<^sup>1)\<^sup>+\<^sup>b U U U, and S \<equiv> K (K V)\<^sup>-\<^sup>1 U U U with V \<equiv> (2b - 4)\<^sup>+\<^sup>b.
    - K, b = 1:  P \<equiv> K (Z\<^sup>+\<^sup>1)\<^sup>+\<^sup>1 is a predecessor and S \<equiv> K P\<^sup>-\<^sup>1 (Z T)\<^sup>+\<^sup>1.
    - L:  L\<^sup>-\<^sup>1 = A, L ((\<dots>(A\<^sup>+\<^sup>b)\<dots>)\<^sup>+\<^sup>b) (2b - 2 times) is x + b - 1, L A\<^sup>+\<^sup>b subtracts b - 2,
      and S is their composition.
*)

theory UPRF_Ext_GRb
  imports UPRF_Ext_GR UPRF_Ext_Vb
begin

section \<open>The bases \<open>\<langle>X, F\<^sup>+\<^sup>b, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

definition basis_GRb :: "ufun \<Rightarrow> nat \<Rightarrow> basis" where
  "basis_GRb X b = Basis {X} {opPlusIb b, opInv} {(\<circ>)}"

lemmas basis_GRb_sel [clos_defs] =
  basis.sel[of "{X}" "{opPlusIb b, opInv}" "{(\<circ>)}", folded basis_GRb_def] for X b

abbreviation CbE :: "nat \<Rightarrow> ufun set" where "CbE b \<equiv> clos (basis_GRb funE b)"
abbreviation CbK :: "nat \<Rightarrow> ufun set" where "CbK b \<equiv> clos (basis_GRb funK b)"
abbreviation CbL :: "nat \<Rightarrow> ufun set" where "CbL b \<equiv> clos (basis_GRb funL b)"

text \<open>For \<open>b = 0\<close> this is the basis \<open>\<langle>X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close> of UPRF_Ext_GR.\<close>
lemma basis_GRb_0: "basis_GRb X 0 = basis_GR0 X"
  by (simp add: basis_GRb_def basis_GR0_def opPlusIb_0)

subsection \<open>General facts\<close>

lemma clos_powcomp_b: "F \<in> clos (basis_GRb X b) \<Longrightarrow> G \<in> clos (basis_GRb X b) \<Longrightarrow> (F ^^ k) \<circ> G \<in> clos (basis_GRb X b)"
  by (rule clos_powcomp) (simp_all add: clos_defs)

lemma clos_iter_b: "F \<in> clos (basis_GRb X b) \<Longrightarrow> (opPlusIb b ^^ n) F \<in> clos (basis_GRb X b)"
  by (induct n) (simp_all, clos_solve)

lemma opPlusIb_val: "opPlusIb b F x = F x + x + b"
  by (simp add: opPlusIb_def)

lemma T_val: "opPlusIb b funI x = 2 * x + b"
  by (simp add: opPlusIb_def funI_def)

text \<open>A predecessor recovers \<open>F\<^sup>+\<close>: \<open>F\<^sup>+ = P\<^sup>b F\<^sup>+\<^sup>b\<close>.\<close>
lemma plusI_from_pred:
  assumes "\<And>y. P (Suc y) = y" shows "(P ^^ b) \<circ> opPlusIb b F = opPlusI F"
proof
  fix x
  have "((P ^^ b) \<circ> opPlusIb b F) x = (P ^^ b) ((F x + x) + b)" by (simp add: opPlusIb_def)
  also have "\<dots> = F x + x" by (rule pred_pow[OF assms])
  finally show "((P ^^ b) \<circ> opPlusIb b F) x = opPlusI F x" by (simp add: opPlusI_def)
qed

lemma plusI_in_b:
  assumes P: "P \<in> clos (basis_GRb X b)" "\<And>y. P (Suc y) = y" and F: "F \<in> clos (basis_GRb X b)"
  shows "opPlusI F \<in> clos (basis_GRb X b)"
proof -
  have "(P ^^ b) \<circ> opPlusIb b F \<in> clos (basis_GRb X b)"
    by (rule clos_powcomp_b[OF P(1)]) (clos_solve add: F)
  then show ?thesis by (simp only: plusI_from_pred[OF P(2)])
qed

text \<open>With \<open>1\<close> and a predecessor, the closure contains the basis \<open>\<langle>1, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>.\<close>
lemma GR_sub_GRb:
  assumes one: "cst 1 \<in> clos (basis_GRb X b)"
    and P: "P \<in> clos (basis_GRb X b)" "\<And>y. P (Suc y) = y"
  shows "clos (basis_GR X) \<subseteq> clos (basis_GRb X b)"
proof (rule clos_subset)
  show "inits (basis_GR X) \<subseteq> clos (basis_GRb X b)"
    using one by (auto simp: clos_defs intro: clos_init)
next
  fix u F assume u: "u \<in> unops (basis_GR X)" and F: "F \<in> clos (basis_GRb X b)"
  from u have "u = opPlusI \<or> u = opInv" by (simp add: clos_defs)
  then show "applyU u F \<in> clos (basis_GRb X b)"
  proof
    assume "u = opPlusI" then show ?thesis using plusI_in_b[OF P F] by (simp add: applyU_def)
  next
    assume "u = opInv" then show ?thesis by (simp only: applyU_def) (clos_solve add: F)
  qed
next
  fix c F G assume c: "c \<in> binops (basis_GR X)" and F: "F \<in> clos (basis_GRb X b)"
    and G: "G \<in> clos (basis_GRb X b)"
  from c have "c = (\<circ>)" by (simp add: clos_defs)
  then show "applyB c F G \<in> clos (basis_GRb X b)"
    by (simp only: applyB_def) (rule clos_comp_rule[OF F G], simp add: clos_defs)
qed

text \<open>Conversely, \<open>F\<^sup>+\<^sup>b = F\<^sup>+ + b\<close>, so the closure lies in Robinson's.\<close>
lemma cst_in_GE: "cst n \<in> CGE"
proof (induct n)
  case 0 show ?case by clos_solve
next
  case (Suc n)
  have "funS \<circ> cst n = cst (Suc n)" by (rule ext) (simp add: funS_def cst_def)
  moreover have "funS \<circ> cst n \<in> CGE" by (clos_solve add: Suc.hyps)
  ultimately show ?case by simp
qed

lemma opPlusIb_eq: "opPlusIb b F = opPlus (opPlusI F) (cst b)"
  by (rule ext) (simp add: opPlusIb_def opPlus_def opPlusI_def cst_def)

lemma GRb_sub_GE:
  assumes X: "X \<in> CGE" shows "clos (basis_GRb X b) \<subseteq> CGE"
proof (rule clos_subset)
  show "inits (basis_GRb X b) \<subseteq> CGE" using X by (simp add: clos_defs)
next
  fix u F assume u: "u \<in> unops (basis_GRb X b)" and F: "F \<in> CGE"
  from u have "u = opPlusIb b \<or> u = opInv" by (simp add: clos_defs)
  then show "applyU u F \<in> CGE"
  proof
    assume "u = opPlusIb b"
    then show ?thesis by (simp only: applyU_def opPlusIb_eq) (clos_solve add: F cst_in_GE)
  next
    assume "u = opInv" then show ?thesis by (simp only: applyU_def) (clos_solve add: F)
  qed
next
  fix c F G assume c: "c \<in> binops (basis_GRb X b)" and F: "F \<in> CGE" and G: "G \<in> CGE"
  from c have "c = (\<circ>)" by (simp add: clos_defs)
  then show "applyB c F G \<in> CGE"
    by (simp only: applyB_def) (rule clos_comp_rule[OF F G], simp add: clos_defs)
qed


section \<open>The basis with \<open>E\<close>\<close>

lemma Einv_even: "opInv funE (2 * m) = m * m + 2 * m"
  using Einv_D[of m] by (simp only: funD_def)

lemma Einv_odd: "opInv funE (2 * m + 1) = (m + 1) * (m + 1) + (2 * m + 1)"
proof -
  have h: "(2 * m + 1 + 1) div 2 = m + 1" by simp
  show ?thesis using Einv_val[of "2 * m + 1"] unfolding h .
qed

lemma E_shift_even:
  assumes "1 \<le> b" and "x + b \<le> 2 * m + 3"
  shows "funE (opInv funE (2 * m) + x + b) = x + b - 1"
proof -
  obtain c where b: "b = Suc c" using assms(1) by (cases b) auto
  have eq: "opInv funE (2 * m) + x + b = (m + 1) * (m + 1) + (x + c)"
    unfolding Einv_even using b by (simp add: algebra_simps)
  have le: "x + c \<le> 2 * (m + 1)" using assms(2) b by simp
  have "funE (opInv funE (2 * m) + x + b) = x + c" unfolding eq by (rule funE_sq_add[OF le])
  then show ?thesis using b by simp
qed

lemma E_shift_odd:
  assumes "2 \<le> b" and "x + b \<le> 2 * m + 6"
  shows "funE (opInv funE (2 * m + 1) + x + b) = x + b - 2"
proof -
  obtain c where b: "b = Suc (Suc c)" using assms(1) by (cases b; cases "b - 1") auto
  have eq: "opInv funE (2 * m + 1) + x + b = (m + 2) * (m + 2) + (x + c)"
    unfolding Einv_odd using b by (simp add: algebra_simps)
  have le: "x + c \<le> 2 * (m + 2)" using assms(2) b by simp
  have "funE (opInv funE (2 * m + 1) + x + b) = x + c" unfolding eq by (rule funE_sq_add[OF le])
  then show ?thesis using b by simp
qed

text \<open>Subtraction by inversion: if \<open>V(y) = y + c\<close>, then \<open>E (E V)\<^sup>-\<^sup>1\<close> subtracts \<open>c\<close> on \<open>x \<ge> c\<close>.\<close>
text \<open>Subtraction by inversion with \<open>E\<close>: an instance of \<open>sub_inv\<close> with \<open>base(t) = t\<^sup>2\<close> and
  \<open>bound(t) = 2t\<close>.\<close>
lemma E_sub_inv_hyps:
  shows "\<And>y. \<exists>t. y = funSq t + funE y \<and> funE y \<le> funD t"
    and "\<And>t k. k \<le> funD t \<Longrightarrow> funE (funSq t + k) = k"
    and "\<And>z. \<exists>t. z \<le> funD t \<and> c \<le> funSq t"
proof -
  fix y show "\<exists>t. y = funSq t + funE y \<and> funE y \<le> funD t"
    using funE_decomp[of y] funE_bound[of y]
    by (intro exI[of _ "funRt y"]) (simp add: funSq_def funD_def)
next
  fix t k assume "k \<le> funD t"
  then show "funE (funSq t + k) = k" by (simp add: funSq_def funD_def funE_sq_add)
next
  fix z have "c \<le> (z + c) * (z + c)" using le_square[of "z + c"] by linarith
  then show "\<exists>t. z \<le> funD t \<and> c \<le> funSq t"
    by (intro exI[of _ "z + c"]) (simp add: funSq_def funD_def)
qed

lemma surj_E_shift:
  assumes V: "\<And>y. V y = y + c" shows "surj (funE \<circ> V)"
  by (rule sub_inv_surj[OF E_sub_inv_hyps V])

lemma E_sub_inv:
  assumes V: "\<And>y. V y = y + c" and cx: "c \<le> x"
  shows "funE (opInv (funE \<circ> V) x) = x - c"
  by (rule sub_inv_val[OF E_sub_inv_hyps V cx])

subsection \<open>The successor, \<open>b \<ge> 2\<close>\<close>

definition expW1 :: "nat \<Rightarrow> ufun" where
  "expW1 b = funE \<circ> opPlusIb b (opInv funE \<circ> opPlusIb b funI)"
definition expW2 :: "nat \<Rightarrow> ufun" where
  "expW2 b = funE \<circ> opPlusIb b (opInv funE \<circ> expW1 b \<circ> opPlusIb b funI)"

lemma expW1_in: "expW1 b \<in> CbE b"
proof -
  have "funI \<in> CbE b" by (subst I_expr_inv[symmetric]) clos_solve
  show ?thesis unfolding expW1_def by (clos_solve add: \<open>funI \<in> CbE b\<close>)
qed

lemma expW2_in: "expW2 b \<in> CbE b"
proof -
  have "funI \<in> CbE b" by (subst I_expr_inv[symmetric]) clos_solve
  show ?thesis unfolding expW2_def by (clos_solve add: \<open>funI \<in> CbE b\<close> expW1_in)
qed

lemma expW1_val:
  assumes "2 \<le> b" shows "expW1 b x = x + (if even b then b - 1 else b - 2)"
proof -
  have e: "expW1 b x = funE (opInv funE (2 * x + b) + x + b)"
    by (simp only: expW1_def comp_apply opPlusIb_val funI_def mult_2[symmetric])
  show ?thesis
  proof (cases "even b")
    case True
    then obtain c where c: "b = 2 * c" by (auto elim: evenE)
    have "2 * x + b = 2 * (x + c)" using c by simp
    then have "expW1 b x = funE (opInv funE (2 * (x + c)) + x + b)" using e by simp
    also have "\<dots> = x + b - 1" using assms c by (intro E_shift_even) simp_all
    finally show ?thesis using True assms by simp
  next
    case False
    then obtain c where c: "b = 2 * c + 1" by (auto elim: oddE)
    have "2 * x + b = 2 * (x + c) + 1" using c by simp
    then have "expW1 b x = funE (opInv funE (2 * (x + c) + 1) + x + b)" using e by simp
    also have "\<dots> = x + b - 2" using assms c by (intro E_shift_odd) simp_all
    finally show ?thesis using False assms by simp
  qed
qed

lemma expW2_val:
  assumes "2 \<le> b" shows "expW2 b x = x + (if even b then b - 2 else b - 1)"
proof -
  have w: "expW1 b (2 * x + b) = 2 * x + b + (if even b then b - 1 else b - 2)"
    using expW1_val[OF assms] by simp
  have e: "expW2 b x = funE (opInv funE (expW1 b (2 * x + b)) + x + b)"
    by (simp only: expW2_def comp_apply opPlusIb_val funI_def mult_2[symmetric])
  show ?thesis
  proof (cases "even b")
    case True
    have "expW1 b (2 * x + b) = 2 * (x + b - 1) + 1" using w True assms by simp
    then have "expW2 b x = funE (opInv funE (2 * (x + b - 1) + 1) + x + b)" using e by simp
    also have "\<dots> = x + b - 2" using assms by (intro E_shift_odd) simp_all
    finally show ?thesis using True assms by simp
  next
    case False
    have "expW1 b (2 * x + b) = 2 * (x + b - 1)" using w False assms by simp
    then have "expW2 b x = funE (opInv funE (2 * (x + b - 1)) + x + b)" using e by simp
    also have "\<dots> = x + b - 1" using assms by (intro E_shift_even) simp_all
    finally show ?thesis using False assms by simp
  qed
qed

text \<open>\<open>U\<^sub>1(x) = x + b - 1\<close> and \<open>U\<^sub>2(x) = x + b - 2\<close>.\<close>
definition expU1 :: "nat \<Rightarrow> ufun" where "expU1 b = (if even b then expW1 b else expW2 b)"
definition expU2 :: "nat \<Rightarrow> ufun" where "expU2 b = (if even b then expW2 b else expW1 b)"

lemma expU1_val: "2 \<le> b \<Longrightarrow> expU1 b x = x + (b - 1)"
  by (simp add: expU1_def expW1_val expW2_val)
lemma expU2_val: "2 \<le> b \<Longrightarrow> expU2 b x = x + (b - 2)"
  by (simp add: expU2_def expW1_val expW2_val)

lemma expU1_in: "expU1 b \<in> CbE b" by (simp add: expU1_def expW1_in expW2_in)
lemma expU2_in: "expU2 b \<in> CbE b" by (simp add: expU2_def expW1_in expW2_in)

definition expSE2 :: "nat \<Rightarrow> ufun" where
  "expSE2 b = funE \<circ> opInv (funE \<circ> expU2 b) \<circ> expU1 b"

lemma expSE2_val: "2 \<le> b \<Longrightarrow> expSE2 b = funS"
proof
  fix x assume b: "2 \<le> b"
  have "expSE2 b x = funE (opInv (funE \<circ> expU2 b) (x + (b - 1)))"
    by (simp add: expSE2_def expU1_val[OF b])
  also have "\<dots> = x + (b - 1) - (b - 2)" by (rule E_sub_inv) (simp_all add: expU2_val[OF b])
  also have "\<dots> = funS x" using b by (simp add: funS_def)
  finally show "expSE2 b x = funS x" .
qed

lemma expSE2_in: "expSE2 b \<in> CbE b"
  unfolding expSE2_def by (clos_solve add: expU1_in expU2_in)

subsection \<open>The successor, \<open>b = 1\<close>\<close>

definition expPE1 :: ufun where "expPE1 = funE \<circ> opPlusIb 1 (opInv funE \<circ> opPlusIb 1 funI)"

lemma expPE1_val: "expPE1 x = funE (opInv funE (2 * x + 1) + x + 1)"
  by (simp only: expPE1_def comp_apply opPlusIb_val funI_def mult_2[symmetric])

lemma expPE1_Suc: "expPE1 (Suc y) = y"
proof -
  have e: "opInv funE (2 * Suc y + 1) = (Suc y + 1) * (Suc y + 1) + (2 * Suc y + 1)" by (rule Einv_odd)
  have h: "opInv funE (2 * Suc y + 1) + Suc y + 1 = (y + 3) * (y + 3) + y"
    unfolding e by (simp add: algebra_simps)
  have "expPE1 (Suc y) = funE ((y + 3) * (y + 3) + y)" by (simp only: expPE1_val h)
  also have "\<dots> = y" by (rule funE_sq_add) simp
  finally show ?thesis .
qed

lemma expPE1_0: "expPE1 0 = 2"
  using Einv_odd[of 0] by (simp add: expPE1_val)

lemma surj_expPE1: "surj expPE1"
  by (rule surjI'[of _ Suc]) (rule expPE1_Suc)

lemma expPE1_inv: assumes "v \<noteq> 2" shows "opInv expPE1 v = Suc v"
proof -
  let ?y = "opInv expPE1 v"
  have e: "expPE1 ?y = v" by (rule opInv_right[OF surj_expPE1])
  show ?thesis
  proof (cases ?y)
    case 0 then show ?thesis using e expPE1_0 assms by simp
  next
    case (Suc y') then show ?thesis using e by (simp add: expPE1_Suc)
  qed
qed

definition expSE1 :: ufun where
  "expSE1 = funE \<circ> opInv expPE1 \<circ> opPlusIb 1 (opInv funE \<circ> expPE1 \<circ> opPlusIb 1 funI)"

lemma expSE1_val: "expSE1 = funS"
proof
  fix x
  have d: "expPE1 (2 * x + 1) = 2 * x" using expPE1_Suc[of "2 * x"] by simp
  define v where "v = x * x + 3 * x + 1"
  have "opPlusIb 1 (opInv funE \<circ> expPE1 \<circ> opPlusIb 1 funI) x = opInv funE (2 * x) + x + 1"
    by (simp only: opPlusIb_val comp_apply funI_def mult_2[symmetric] d)
  also have "\<dots> = v" by (simp only: Einv_even) (simp add: v_def)
  finally have v: "opPlusIb 1 (opInv funE \<circ> expPE1 \<circ> opPlusIb 1 funI) x = v" .
  have v2: "v \<noteq> 2" by (cases x) (simp_all add: v_def)
  have "expSE1 x = funE (opInv expPE1 (opPlusIb 1 (opInv funE \<circ> expPE1 \<circ> opPlusIb 1 funI) x))"
    by (simp add: expSE1_def)
  also have "\<dots> = funE (Suc v)" by (simp only: v expPE1_inv[OF v2])
  also have "Suc v = (x + 1) * (x + 1) + (x + 1)" by (simp add: v_def algebra_simps)
  also have "funE \<dots> = x + 1" by (rule funE_sq_add) simp
  finally show "expSE1 x = funS x" by (simp add: funS_def)
qed

lemma expSE1_in: "expSE1 \<in> CbE 1"
proof -
  have I: "funI \<in> CbE 1" by (subst I_expr_inv[symmetric]) clos_solve
  have PE: "expPE1 \<in> CbE 1" unfolding expPE1_def by (clos_solve add: I)
  show ?thesis unfolding expSE1_def by (clos_solve add: I PE)
qed

subsection \<open>The basis with \<open>E\<close> generates Robinson's closure\<close>

lemma S_in_bE: "1 \<le> b \<Longrightarrow> funS \<in> CbE b"
proof -
  assume b: "1 \<le> b"
  show ?thesis
  proof (cases "b = 1")
    case True then show ?thesis using expSE1_in expSE1_val by simp
  next
    case False then have "2 \<le> b" using b by simp
    then show ?thesis using expSE2_in[of b] expSE2_val by simp
  qed
qed

text \<open>The predecessor \<open>E (E S)\<^sup>-\<^sup>1\<close>.\<close>
lemma predE_Suc: "(funE \<circ> opInv (funE \<circ> funS)) (Suc y) = y"
  using E_sub_inv[of funS 1 "Suc y"] by (simp add: funS_def)

lemma zeroE_b: "funE \<circ> funS \<circ> opInv funE \<circ> opPlusI funI = cst 0"
proof
  fix x
  have o: "opPlusI funI x = 2 * x" by (simp add: opPlusI_def funI_def)
  have ar: "Suc (x * x + 2 * x) = (x + 1) * (x + 1) + 0" by (simp add: algebra_simps)
  have "(funE \<circ> funS \<circ> opInv funE \<circ> opPlusI funI) x = funE ((x + 1) * (x + 1) + 0)"
    by (simp only: comp_apply o Einv_even funS_def ar)
  also have "\<dots> = 0" by (rule funE_sq_add) simp
  finally show "(funE \<circ> funS \<circ> opInv funE \<circ> opPlusI funI) x = cst 0 x" by (simp add: cst_def)
qed

lemma GE_sub_bE:
  assumes b: "1 \<le> b" shows "CGE \<subseteq> CbE b"
proof -
  have S: "funS \<in> CbE b" by (rule S_in_bE[OF b])
  have P: "funE \<circ> opInv (funE \<circ> funS) \<in> CbE b" by (clos_solve add: S)
  have I: "funI \<in> CbE b" by (subst I_expr_inv[symmetric]) clos_solve
  have D: "opPlusI funI \<in> CbE b" by (rule plusI_in_b[OF P predE_Suc I])
  have "funE \<circ> funS \<circ> opInv funE \<circ> opPlusI funI \<in> CbE b" by (clos_solve add: S D)
  then have Z0: "cst 0 \<in> CbE b" by (simp only: zeroE_b)
  have "funS \<circ> cst 0 \<in> CbE b" by (clos_solve add: S Z0)
  then have "cst 1 \<in> CbE b" by (simp only: one_expr)
  then show ?thesis by (rule GR_sub_GRb[OF _ P predE_Suc])
qed

theorem GRb_E_eq_JR: "1 \<le> b \<Longrightarrow> clos (basis_GRb funE b) = clos basis_JR"
proof -
  assume b: "1 \<le> b"
  have "funE \<in> CGE" by clos_solve
  then have "clos (basis_GRb funE b) \<subseteq> CGE" by (rule GRb_sub_GE)
  moreover have "CGE \<subseteq> clos (basis_GRb funE b)" by (rule GE_sub_bE[OF b])
  ultimately show ?thesis using GR_E_eq_JR by blast
qed


section \<open>The basis with \<open>K\<close>\<close>

lemma Z_in_bK: "funZ \<in> CbK b" by (subst Kinv_eq_Z[symmetric]) clos_solve

lemma KZ_I: "funK \<circ> funZ = funI"
  by (rule ext) (simp add: KZ funI_def)

lemma I_in_bK: "funI \<in> CbK b"
  by (subst KZ_I[symmetric]) (clos_solve add: Z_in_bK)

lemma le_sf: "n \<le> sf n"
  using two_sf[of n] le_square[of n] by linarith

text \<open>Subtraction by inversion, with \<open>K\<close>.\<close>
text \<open>Subtraction by inversion with \<open>K\<close>: an instance of \<open>sub_inv\<close> with \<open>base = A\<close> and
  \<open>bound(t) = t\<close>.\<close>
lemma K_sub_inv_hyps:
  shows "\<And>y. \<exists>t. y = sf t + funK y \<and> funK y \<le> funI t"
    and "\<And>t k. k \<le> funI t \<Longrightarrow> funK (sf t + k) = k"
    and "\<And>z. \<exists>t. z \<le> funI t \<and> c \<le> sf t"
proof -
  fix y show "\<exists>t. y = sf t + funK y \<and> funK y \<le> funI t"
    using funK_decomp[of y] funK_le_V[of y]
    by (intro exI[of _ "funV y"]) (simp add: funI_def)
next
  fix t k assume "k \<le> funI t"
  then show "funK (sf t + k) = k" by (simp add: funI_def funK_diag)
next
  fix z have "c \<le> sf (z + c)" using le_sf[of "z + c"] by linarith
  then show "\<exists>t. z \<le> funI t \<and> c \<le> sf t" by (intro exI[of _ "z + c"]) (simp add: funI_def)
qed

lemma surj_K_shift:
  assumes V: "\<And>y. V y = y + c" shows "surj (funK \<circ> V)"
  by (rule sub_inv_surj[OF K_sub_inv_hyps V])

lemma K_sub_inv:
  assumes V: "\<And>y. V y = y + c" and cx: "c \<le> x"
  shows "funK (opInv (funK \<circ> V) x) = x - c"
  by (rule sub_inv_val[OF K_sub_inv_hyps V cx])

text \<open>\<open>U \<equiv> K (Z T)\<^sup>+\<^sup>b\<close>, \<open>U(x) = x + b - 1\<close>.\<close>
definition expUK :: "nat \<Rightarrow> ufun" where "expUK b = funK \<circ> opPlusIb b (funZ \<circ> opPlusIb b funI)"

lemma expUK_val: assumes "1 \<le> b" shows "expUK b x = x + (b - 1)"
proof -
  obtain c where b: "b = Suc c" using assms by (cases b) auto
  have e: "expUK b x = funK (funZ (2 * x + b) + x + b)"
    by (simp only: expUK_def comp_apply opPlusIb_val funI_def mult_2[symmetric])
  have s: "sf (Suc (2 * x + b)) = sf (2 * x + b) + (2 * x + b) + 1" by (rule sf_Suc)
  have ar: "funZ (2 * x + b) + x + b = sf (Suc (2 * x + b)) + (x + c)"
    using s b funZ_sf[of "2 * x + b"] by linarith
  have "expUK b x = funK (sf (Suc (2 * x + b)) + (x + c))" by (simp only: e ar)
  also have "\<dots> = x + c" by (rule funK_diag) (simp add: b)
  finally show ?thesis using b by simp
qed

lemma expUK_in: "expUK b \<in> CbK b"
  unfolding expUK_def by (clos_solve add: Z_in_bK I_in_bK)

subsection \<open>The successor, \<open>b \<ge> 2\<close>\<close>

definition expP1K :: "nat \<Rightarrow> ufun" where "expP1K b = funK \<circ> opInv (funK \<circ> expUK b)"
definition expCK :: "nat \<Rightarrow> ufun" where
  "expCK b = funK \<circ> opPlusIb b (funZ \<circ> expP1K b) \<circ> expUK b \<circ> expUK b \<circ> expUK b"
definition expSK2 :: "nat \<Rightarrow> ufun" where
  "expSK2 b = funK \<circ> opInv (funK \<circ> opPlusIb b (expCK b)) \<circ> expUK b \<circ> expUK b \<circ> expUK b"

lemma expP1K_val: assumes "1 \<le> b" "b - 1 \<le> x" shows "expP1K b x = x - (b - 1)"
proof -
  have "expP1K b x = funK (opInv (funK \<circ> expUK b) x)" by (simp add: expP1K_def)
  also have "\<dots> = x - (b - 1)" by (rule K_sub_inv[of "expUK b" "b - 1"]) (rule expUK_val[OF assms(1)], rule assms(2))
  finally show ?thesis .
qed

text \<open>The constant \<open>2b - 4\<close>.\<close>
lemma expCK_val: assumes "2 \<le> b" shows "expCK b x = 2 * b - 4"
proof -
  obtain c where b: "b = Suc (Suc c)" using assms by (cases b; cases "b - 1") auto
  define y where "y = x + 3 * (b - 1)"
  have u3: "expUK b (expUK b (expUK b x)) = y" using assms by (simp add: expUK_val y_def)
  define g where "g = x + 2 * (b - 1)"
  have p: "expP1K b y = g" using assms by (subst expP1K_val) (simp_all add: y_def g_def)
  have sf2: "sf (Suc (Suc g)) = sf g + 2 * g + 3" using sf_Suc[of g] sf_Suc[of "Suc g"] by simp
  have "funZ g + y + b = sf (Suc (Suc g)) + (2 * b - 4)"
    using sf2 b by (simp add: funZ_sf y_def g_def)
  moreover have "2 * b - 4 \<le> Suc (Suc g)" using b by (simp add: g_def)
  ultimately have "funK (funZ g + y + b) = 2 * b - 4" by (simp add: funK_diag)
  then show ?thesis by (simp add: expCK_def u3 opPlusIb_def p)
qed

lemma expSK2_val: assumes "2 \<le> b" shows "expSK2 b = funS"
proof
  fix x
  have V: "opPlusIb b (expCK b) y = y + (3 * b - 4)" for y using assms by (simp add: opPlusIb_def expCK_val)
  have u: "expUK b (expUK b (expUK b x)) = x + 3 * (b - 1)" using assms by (simp add: expUK_val)
  have "expSK2 b x = funK (opInv (funK \<circ> opPlusIb b (expCK b)) (expUK b (expUK b (expUK b x))))"
    by (simp add: expSK2_def)
  also have "\<dots> = funK (opInv (funK \<circ> opPlusIb b (expCK b)) (x + 3 * (b - 1)))" by (simp only: u)
  also have "\<dots> = x + 3 * (b - 1) - (3 * b - 4)" by (rule K_sub_inv) (simp_all add: V)
  also have "\<dots> = funS x" using assms by (simp add: funS_def)
  finally show "expSK2 b x = funS x" .
qed

lemma expSK2_in: "expSK2 b \<in> CbK b"
proof -
  have P1: "expP1K b \<in> CbK b" unfolding expP1K_def by (clos_solve add: expUK_in)
  have CK: "expCK b \<in> CbK b" unfolding expCK_def by (clos_solve add: Z_in_bK expUK_in P1)
  show ?thesis unfolding expSK2_def by (clos_solve add: expUK_in CK)
qed

subsection \<open>The successor, \<open>b = 1\<close>\<close>

definition expPK1 :: ufun where "expPK1 = funK \<circ> opPlusIb 1 (opPlusIb 1 funZ)"

lemma expPK1_Suc: "expPK1 (Suc y) = y"
proof -
  have e: "expPK1 (Suc y) = funK (funZ (Suc y) + Suc y + 1 + Suc y + 1)"
    by (simp only: expPK1_def comp_apply opPlusIb_val)
  have s1: "sf (Suc (Suc y)) = sf (Suc y) + Suc y + 1" by (rule sf_Suc)
  have s2: "sf (Suc (Suc (Suc y))) = sf (Suc (Suc y)) + Suc (Suc y) + 1" by (rule sf_Suc)
  have ar: "funZ (Suc y) + Suc y + 1 + Suc y + 1 = sf (Suc (Suc (Suc y))) + y"
    using s1 s2 funZ_sf[of "Suc y"] by linarith
  have "expPK1 (Suc y) = funK (sf (Suc (Suc (Suc y))) + y)" by (simp only: e ar)
  also have "\<dots> = y" by (rule funK_diag) simp
  finally show ?thesis .
qed

lemma expPK1_0: "expPK1 0 = 1"
proof -
  have "expPK1 0 = funK (funZ 0 + 0 + 1 + 0 + 1)" by (simp only: expPK1_def comp_apply opPlusIb_val)
  also have "funZ 0 + 0 + 1 + 0 + 1 = sf 1 + 1" by (simp add: funZ_def sf_def)
  also have "funK (sf 1 + 1) = 1" by (rule funK_diag) simp
  finally show ?thesis .
qed

lemma surj_expPK1: "surj expPK1"
  by (rule surjI'[of _ Suc]) (rule expPK1_Suc)

lemma expPK1_inv: assumes "v \<noteq> 1" shows "opInv expPK1 v = Suc v"
proof -
  let ?y = "opInv expPK1 v"
  have e: "expPK1 ?y = v" by (rule opInv_right[OF surj_expPK1])
  show ?thesis
  proof (cases ?y)
    case 0 then show ?thesis using e expPK1_0 assms by simp
  next
    case (Suc y') then show ?thesis using e by (simp add: expPK1_Suc)
  qed
qed

definition expSK1 :: ufun where
  "expSK1 = funK \<circ> opInv expPK1 \<circ> opPlusIb 1 (funZ \<circ> opPlusIb 1 funI)"

lemma expSK1_val: "expSK1 = funS"
proof
  fix x
  define v where "v = sf (Suc (2 * x + 1)) + x"
  have t: "opPlusIb 1 funI x = 2 * x + 1" by (rule T_val)
  have s: "sf (Suc (2 * x + 1)) = sf (2 * x + 1) + (2 * x + 1) + 1" by (rule sf_Suc)
  have "opPlusIb 1 (funZ \<circ> opPlusIb 1 funI) x = funZ (2 * x + 1) + x + 1"
    by (simp only: opPlusIb_val comp_apply funI_def mult_2[symmetric])
  also have "\<dots> = v" using s funZ_sf[of "2 * x + 1"] by (simp add: v_def)
  finally have v: "opPlusIb 1 (funZ \<circ> opPlusIb 1 funI) x = v" .
  have "sf 2 \<le> sf (Suc (2 * x + 1))" by (rule sf_mono) simp
  moreover have "sf 2 = 3" by (simp add: sf_def)
  ultimately have v1: "v \<noteq> 1" by (simp add: v_def)
  have "expSK1 x = funK (opInv expPK1 (opPlusIb 1 (funZ \<circ> opPlusIb 1 funI) x))"
    by (simp add: expSK1_def)
  also have "\<dots> = funK (sf (Suc (2 * x + 1)) + (x + 1))" by (simp only: v expPK1_inv[OF v1]) (simp add: v_def)
  also have "\<dots> = x + 1" by (rule funK_diag) simp
  finally show "expSK1 x = funS x" by (simp add: funS_def)
qed

lemma expSK1_in: "expSK1 \<in> CbK 1"
proof -
  have PK: "expPK1 \<in> CbK 1" unfolding expPK1_def by (clos_solve add: Z_in_bK)
  show ?thesis unfolding expSK1_def by (clos_solve add: Z_in_bK I_in_bK PK)
qed

subsection \<open>The basis with \<open>K\<close> generates Robinson's closure\<close>

lemma S_in_bK: "1 \<le> b \<Longrightarrow> funS \<in> CbK b"
proof -
  assume b: "1 \<le> b"
  show ?thesis
  proof (cases "b = 1")
    case True then show ?thesis using expSK1_in expSK1_val by simp
  next
    case False then have "2 \<le> b" using b by simp
    then show ?thesis using expSK2_in[of b] expSK2_val by simp
  qed
qed

lemma funP_Suc: "funP (Suc y) = y" by (simp add: funP_def)

lemma A0_K: "funK \<circ> funA = cst 0"
  by (rule ext) (simp add: funA_eq_sf cst_def funK_diag[of 0, simplified])

lemma GK_sub_bK:
  assumes b: "1 \<le> b" shows "CGK \<subseteq> CbK b"
proof -
  have S: "funS \<in> CbK b" by (rule S_in_bK[OF b])
  have P: "funP \<in> CbK b" by (subst P_expr_K[symmetric]) (clos_solve add: S)
  note plusI = plusI_in_b[OF P funP_Suc]
  have "exprAK \<in> CbK b" unfolding exprAK_def by (clos_solve add: plusI Z_in_bK S)
  then have A: "funA \<in> CbK b" by (simp only: A_expr_K)
  have "funK \<circ> funA \<in> CbK b" by (clos_solve add: A)
  then have Z0: "cst 0 \<in> CbK b" by (simp only: A0_K)
  have "funS \<circ> cst 0 \<in> CbK b" by (clos_solve add: S Z0)
  then have "cst 1 \<in> CbK b" by (simp only: one_expr)
  then show ?thesis by (rule GR_sub_GRb[OF _ P funP_Suc])
qed

theorem GRb_K_eq_JR: "1 \<le> b \<Longrightarrow> clos (basis_GRb funK b) = clos basis_JR"
proof -
  assume b: "1 \<le> b"
  have "clos (basis_GRb funK b) \<subseteq> CGE" by (rule GRb_sub_GE) (rule K_in_GE)
  moreover have "CGK \<subseteq> clos (basis_GRb funK b)" by (rule GK_sub_bK[OF b])
  ultimately show ?thesis using GR_K_eq_JR GR_E_eq_JR by blast
qed


section \<open>The basis with \<open>L\<close>\<close>

text \<open>\<open>L\<^sup>-\<^sup>1 = A\<close>.\<close>
lemma surj_funL: "surj funL"
  by (rule surjI'[of _ sf]) (simp add: funL_diag[of 0, simplified])

lemma Linv_eq_sf: "opInv funL = sf"
proof (inv_eq surj: surj_funL add: funL_diag[of 0, simplified])
  fix x y assume y: "funL y = x"
  let ?t = "funV y" and ?k = "funK y"
  have dec: "sf ?t + ?k = y" by (rule funK_decomp)
  have kt: "?k \<le> ?t" by (rule funK_le_V)
  have "funL y = ?t - ?k" using funL_diag[OF kt] dec by simp
  then have "x \<le> ?t" using y by simp
  then have "sf x \<le> sf ?t" by (rule sf_mono)
  then show "sf x \<le> y" using dec by linarith
qed

lemma sf_in_bL: "sf \<in> CbL b" by (subst Linv_eq_sf[symmetric]) clos_solve

lemma sf_add: "sf (x + n) = sf x + n * x + sf n"
proof -
  have "2 * sf (x + n) = 2 * (sf x + n * x + sf n)"
    using two_sf[of "x + n"] two_sf[of x] two_sf[of n] by (simp add: algebra_simps)
  then show ?thesis by simp
qed

lemma iter_sf: "(opPlusIb b ^^ n) sf x = sf x + n * (x + b)"
  by (induct n) (simp_all add: opPlusIb_def algebra_simps)

text \<open>\<open>U \<equiv> L (\<dots>(A\<^sup>+\<^sup>b)\<dots>)\<^sup>+\<^sup>b\<close> (\<open>2b - 2\<close> times), \<open>U(x) = x + b - 1\<close>.\<close>
definition expUL :: "nat \<Rightarrow> ufun" where "expUL b = funL \<circ> (opPlusIb b ^^ (2 * b - 2)) sf"

lemma expUL_val: assumes "1 \<le> b" shows "expUL b x = x + (b - 1)"
proof -
  obtain c where b: "b = Suc c" using assms by (cases b) auto
  have n: "2 * b - 2 = 2 * c" using b by simp
  have e: "2 * c * (2 * c) + 2 * c = 2 * (2 * c * c + c)" by (simp add: algebra_simps)
  have sfc: "sf (2 * c) = 2 * c * c + c" using two_sf[of "2 * c"] e by linarith
  have sa: "sf (x + 2 * c) = sf x + 2 * c * x + sf (2 * c)" by (rule sf_add)
  have e2: "2 * c * (x + b) = 2 * c * x + 2 * c * c + 2 * c" using b by (simp add: algebra_simps)
  have ar: "sf x + 2 * c * (x + b) = sf (x + 2 * c) + c" using sa sfc e2 by linarith
  have "expUL b x = funL (sf x + (2 * b - 2) * (x + b))" by (simp only: expUL_def comp_apply iter_sf)
  also have "\<dots> = funL (sf (x + 2 * c) + c)" by (simp only: n ar)
  also have "\<dots> = x + 2 * c - c" by (rule funL_diag) simp
  finally show ?thesis using b by simp
qed

text \<open>\<open>L A\<^sup>+\<^sup>b\<close> subtracts \<open>b - 2\<close>: \<open>A(y) + y + b = A(y + 1) + (b - 1)\<close>.\<close>
lemma sigmaL_val:
  assumes "1 \<le> b" "b - 1 \<le> y + 1" shows "(funL \<circ> opPlusIb b sf) y = y + 1 - (b - 1)"
proof -
  have "sf y + y + b = sf (Suc y) + (b - 1)" using sf_Suc[of y] assms(1) by simp
  then show ?thesis using assms(2) by (simp add: opPlusIb_def funL_diag)
qed

definition expSL :: "nat \<Rightarrow> ufun" where "expSL b = funL \<circ> opPlusIb b sf \<circ> expUL b"

lemma expSL_val: assumes "1 \<le> b" shows "expSL b = funS"
proof
  fix x
  have "expSL b x = (funL \<circ> opPlusIb b sf) (x + (b - 1))" by (simp add: expSL_def expUL_val[OF assms])
  also have "\<dots> = x + (b - 1) + 1 - (b - 1)" by (rule sigmaL_val[OF assms]) simp
  finally show "expSL b x = funS x" by (simp add: funS_def)
qed

lemma expSL_in: "expSL b \<in> CbL b"
proof -
  have it: "(opPlusIb b ^^ (2 * b - 2)) sf \<in> CbL b" by (rule clos_iter_b[OF sf_in_bL])
  show ?thesis unfolding expSL_def expUL_def by (clos_solve add: sf_in_bL it)
qed

text \<open>The predecessor \<open>L S A\<close> and the constant \<open>0 \<equiv> L A\<^sup>+\<close>.\<close>
lemma predL_Suc: "(funL \<circ> funS \<circ> sf) (Suc y) = y"
proof -
  have "sf (Suc y) + 1 = sf (Suc y) + 1" ..
  then show ?thesis using funL_diag[of 1 "Suc y"] by (simp add: funS_def)
qed

lemma zeroL: "funL \<circ> opPlusI sf = cst 0"
  by (rule ext) (simp add: opPlusI_def cst_def funL_diag)

lemma GL_sub_bL:
  assumes b: "1 \<le> b" shows "CGL \<subseteq> CbL b"
proof -
  have S: "funS \<in> CbL b" using expSL_in[of b] expSL_val[OF b] by simp
  have P: "funL \<circ> funS \<circ> sf \<in> CbL b" by (clos_solve add: S sf_in_bL)
  have "opPlusI sf \<in> CbL b" by (rule plusI_in_b[OF P predL_Suc sf_in_bL])
  have "funL \<circ> opPlusI sf \<in> CbL b" by (clos_solve add: \<open>opPlusI sf \<in> CbL b\<close>)
  then have Z0: "cst 0 \<in> CbL b" by (simp only: zeroL)
  have "funS \<circ> cst 0 \<in> CbL b" by (clos_solve add: S Z0)
  then have "cst 1 \<in> CbL b" by (simp only: one_expr)
  then show ?thesis by (rule GR_sub_GRb[OF _ P predL_Suc])
qed

theorem GRb_L_eq_JR: "1 \<le> b \<Longrightarrow> clos (basis_GRb funL b) = clos basis_JR"
proof -
  assume b: "1 \<le> b"
  have "clos (basis_GRb funL b) \<subseteq> CGE" by (rule GRb_sub_GE) (rule L_in_GE)
  moreover have "CGL \<subseteq> clos (basis_GRb funL b)" by (rule GL_sub_bL[OF b])
  ultimately show ?thesis using GR_L_eq_JR GR_E_eq_JR by blast
qed


section \<open>Assuming Robinson's theorem\<close>

context Robinson_1950
begin

theorem Ext_GRb_iff:
  "clos (basis_GRb funE b) = GR \<longleftrightarrow> 1 \<le> b"
  "clos (basis_GRb funK b) = GR \<longleftrightarrow> 1 \<le> b"
  "clos (basis_GRb funL b) = GR \<longleftrightarrow> 1 \<le> b"
  using GRb_E_eq_JR GRb_K_eq_JR GRb_L_eq_JR Robinson_1950_sec4_thm3 Ext_GR0
  by (cases b; simp add: basis_GRb_0)+

end

end
