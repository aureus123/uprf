(*  Title:   UPRF_Ext_Cn.thy

    Replacing the constant 1 by any constant n: for X \<in> {E, K, L} and a set U of unary
    operators containing F\<^sup>+, the bases \<langle>n, X, U, FG\<rangle> and \<langle>1, X, U, FG\<rangle> generate the same
    closure whenever n \<ge> 1.  For U = {F\<^sup>+, F\<^sup>\<box>} (Theorems 6.7, 6.8) this gives suitable bases,
    and for U = {F\<^sup>+, F\<^sup>-\<^sup>1} (UPRF_Ext_GR) the unary general recursive functions.  For n = 0
    every generated function fixes 0, so 1 is missing.

    Only F\<^sup>+ and X are used.  Since n\<^sup>+(x) = x + n, every constant c + kn is generated from c;
    X then steps down from c to c - 1:
    - E:  c + kn = (nc + 1)\<^sup>2 + (c - 1) for k = nc\<^sup>2 + 2c;
    - K:  c + kn = A(2nc + 1) + (c - 1) for k = 2nc\<^sup>2 + 3c;
    - L:  two steps, c \<mapsto> nc - c \<mapsto> c - 1, since
          c + n(2nc\<^sup>2 + 2c) = A(2nc) + (nc + c)   and   (nc - c) + n(2nc\<^sup>2) = A(2nc - 1) + (2nc - c).
*)

theory UPRF_Ext_Cn
  imports UPRF_Ext_GRb
begin

section \<open>The bases \<open>\<langle>n, X, U, FG\<rangle>\<close>\<close>

definition basis_C :: "ufun \<Rightarrow> uop set \<Rightarrow> nat \<Rightarrow> basis" where
  "basis_C X U n = Basis {cst n, X} U {(\<circ>)}"

lemmas basis_C_sel [clos_defs] =
  basis.sel[of "{cst n, X}" U "{(\<circ>)}", folded basis_C_def] for X U n

lemma basis_6_C: "basis_6 = basis_C funE {opPlusI, opBox} 1"
  and basis_6K_C: "basis_6K = basis_C funK {opPlusI, opBox} 1"
  and basis_6L_C: "basis_6L = basis_C funL {opPlusI, opBox} 1"
  and basis_GR_C: "basis_GR X = basis_C X {opPlusI, opInv} 1"
  by (simp_all add: basis_6_def basis_6K_def basis_6L_def basis_GR_def basis_C_def)

subsection \<open>Shifting constants\<close>

lemma cst_comp: "F \<circ> cst m = cst (F m)"
  by (rule ext) (simp add: cst_def)

lemma shift_cst: "(opPlusI (cst n) ^^ k) \<circ> cst c = cst (c + k * n)"
proof -
  have "(opPlusI (cst n) ^^ k) c = c + k * n"
    by (rule shift_pow) (simp add: opPlusI_def cst_def)
  then show ?thesis by (simp add: cst_comp)
qed

context
  fixes X :: ufun and U :: "uop set" and n :: nat
  assumes P: "opPlusI \<in> U"
begin

lemma cst_shift_in:
  assumes c: "cst c \<in> clos (basis_C X U n)" shows "cst (c + k * n) \<in> clos (basis_C X U n)"
proof -
  have nC: "cst n \<in> clos (basis_C X U n)" by (rule clos_init) (simp add: clos_defs)
  have "opPlusI (cst n) \<in> clos (basis_C X U n)" by (rule clos_plusI_rule[OF nC]) (simp add: clos_defs P)
  then have "(opPlusI (cst n) ^^ k) \<circ> cst c \<in> clos (basis_C X U n)"
    by (rule clos_powcomp[rotated]) (simp_all add: clos_defs c)
  then show ?thesis by (simp only: shift_cst)
qed

lemma X_cst_in:
  assumes c: "cst c \<in> clos (basis_C X U n)" shows "cst (X (c + k * n)) \<in> clos (basis_C X U n)"
proof -
  have XC: "X \<in> clos (basis_C X U n)" by (rule clos_init) (simp add: clos_defs)
  have "X \<circ> cst (c + k * n) \<in> clos (basis_C X U n)"
    by (rule clos_comp_rule[OF XC cst_shift_in[OF c]]) (simp add: clos_defs)
  then show ?thesis by (simp only: cst_comp)
qed

text \<open>If \<open>X\<close> steps down from every constant \<open>c \<ge> 1\<close>, then \<open>1\<close> is generated from \<open>n \<ge> 1\<close>.\<close>
lemma one_by_descent:
  assumes n: "1 \<le> n"
    and step: "\<And>c. cst c \<in> clos (basis_C X U n) \<Longrightarrow> 1 \<le> c \<Longrightarrow> cst (c - 1) \<in> clos (basis_C X U n)"
  shows "cst 1 \<in> clos (basis_C X U n)"
proof -
  have "j < n \<Longrightarrow> cst (n - j) \<in> clos (basis_C X U n)" for j
  proof (induct j)
    case 0 show ?case by (simp, rule clos_init) (simp add: clos_defs)
  next
    case (Suc j)
    then have "cst (n - j) \<in> clos (basis_C X U n)" by simp
    then have "cst (n - j - 1) \<in> clos (basis_C X U n)" using Suc.prems by (intro step) simp_all
    moreover have "n - Suc j = n - j - 1" by arith
    ultimately show ?case by (simp only:)
  qed
  from this[of "n - 1"] show ?thesis using n by simp
qed

text \<open>With \<open>1\<close> in the closure the two bases are equivalent.\<close>
lemma C_eq_C1:
  assumes one: "cst 1 \<in> clos (basis_C X U n)" and n: "1 \<le> n"
  shows "clos (basis_C X U n) = clos (basis_C X U 1)"
proof
  show "clos (basis_C X U 1) \<subseteq> clos (basis_C X U n)"
  proof (rule clos_subset)
    show "inits (basis_C X U 1) \<subseteq> clos (basis_C X U n)"
      using one by (auto simp: clos_defs intro: clos_init)
  next
    fix u F assume "u \<in> unops (basis_C X U 1)" "F \<in> clos (basis_C X U n)"
    then show "applyU u F \<in> clos (basis_C X U n)" by (intro clos_unop_app) (simp_all add: clos_defs)
  next
    fix c F G assume "c \<in> binops (basis_C X U 1)" "F \<in> clos (basis_C X U n)" "G \<in> clos (basis_C X U n)"
    then show "applyB c F G \<in> clos (basis_C X U n)" by (intro clos_binop_app) (simp_all add: clos_defs)
  qed
next
  have one1: "cst 1 \<in> clos (basis_C X U 1)" by (rule clos_init) (simp add: clos_defs)
  have "cst (1 + (n - 1) * 1) \<in> clos (basis_C X U 1)"
    by (rule UPRF_Ext_Cn.cst_shift_in[OF P one1])
  then have nC: "cst n \<in> clos (basis_C X U 1)" using n by simp
  show "clos (basis_C X U n) \<subseteq> clos (basis_C X U 1)"
  proof (rule clos_subset)
    show "inits (basis_C X U n) \<subseteq> clos (basis_C X U 1)"
      using nC by (auto simp: clos_defs intro: clos_init)
  next
    fix u F assume "u \<in> unops (basis_C X U n)" "F \<in> clos (basis_C X U 1)"
    then show "applyU u F \<in> clos (basis_C X U 1)" by (intro clos_unop_app) (simp_all add: clos_defs)
  next
    fix c F G assume "c \<in> binops (basis_C X U n)" "F \<in> clos (basis_C X U 1)" "G \<in> clos (basis_C X U 1)"
    then show "applyB c F G \<in> clos (basis_C X U 1)" by (intro clos_binop_app) (simp_all add: clos_defs)
  qed
qed

end

subsection \<open>The descent for \<open>E\<close>, \<open>K\<close>, \<open>L\<close>\<close>

lemma E_desc: "1 \<le> n \<Longrightarrow> 1 \<le> c \<Longrightarrow> funE (c + (n * c * c + 2 * c) * n) = c - 1"
proof -
  assume n: "1 \<le> n" and "1 \<le> c"
  then obtain d where c: "c = Suc d" by (cases c) auto
  have eq: "c + (n * c * c + 2 * c) * n = (n * c + 1) * (n * c + 1) + d"
    by (simp add: c algebra_simps)
  have "c \<le> n * c" using mult_le_mono1[OF n, of c] by simp
  then have le: "d \<le> 2 * (n * c + 1)" using c by simp
  have "funE (c + (n * c * c + 2 * c) * n) = d" unfolding eq by (rule funE_sq_add[OF le])
  then show ?thesis using c by simp
qed

lemma K_desc: "1 \<le> n \<Longrightarrow> 1 \<le> c \<Longrightarrow> funK (c + (2 * n * c * c + 3 * c) * n) = c - 1"
proof -
  assume n: "1 \<le> n" and "1 \<le> c"
  then obtain d where c: "c = Suc d" by (cases c) auto
  define t where "t = 2 * n * c + 1"
  have "2 * sf t = 2 * (2 * n * n * c * c + 3 * n * c + 1)"
    using two_sf[of t] by (simp add: t_def algebra_simps)
  then have st: "sf t = 2 * n * n * c * c + 3 * n * c + 1" by simp
  have eq: "c + (2 * n * c * c + 3 * c) * n = sf t + d" using st c by (simp add: algebra_simps)
  have "c \<le> n * c" using mult_le_mono1[OF n, of c] by simp
  then have le: "d \<le> t" using c by (simp add: t_def)
  have "funK (c + (2 * n * c * c + 3 * c) * n) = d" unfolding eq by (rule funK_diag[OF le])
  then show ?thesis using c by simp
qed

text \<open>For \<open>L\<close>, two steps: \<open>c \<mapsto> nc - c \<mapsto> c - 1\<close> (with \<open>N = nc\<close>).\<close>
lemma L_desc1: "1 \<le> n \<Longrightarrow> funL (c + (2 * n * c * c + 2 * c) * n) = n * c - c"
proof -
  assume n: "1 \<le> n"
  define N where "N = n * c"
  have cN: "c \<le> N" using mult_le_mono1[OF n, of c] by (simp add: N_def)
  have "2 * sf (2 * N) = 2 * (2 * N * N + N)" using two_sf[of "2 * N"] by (simp add: algebra_simps)
  then have s: "sf (2 * N) = 2 * N * N + N" by simp
  define j where "j = 2 * N - (N - c)"
  have j: "j = N + c" using cN by (simp add: j_def)
  have m: "(2 * n * c * c + 2 * c) * n = 2 * N * N + 2 * N" by (simp add: N_def algebra_simps)
  have eq: "c + (2 * n * c * c + 2 * c) * n = sf (2 * N) + j" using s j m by simp
  have le: "j \<le> 2 * N" using j cN by simp
  have "funL (c + (2 * n * c * c + 2 * c) * n) = 2 * N - j" unfolding eq by (rule funL_diag[OF le])
  then have "funL (c + (2 * n * c * c + 2 * c) * n) = 2 * N - (2 * N - (N - c))" by (simp only: j_def)
  also have "\<dots> = N - c" using cN by simp
  finally show ?thesis by (simp only: N_def)
qed

lemma L_desc2: "1 \<le> n \<Longrightarrow> 1 \<le> c \<Longrightarrow> funL ((n * c - c) + (2 * n * c * c) * n) = c - 1"
proof -
  assume n: "1 \<le> n" and c1: "1 \<le> c"
  define N where "N = n * c"
  have cN: "c \<le> N" using mult_le_mono1[OF n, of c] by (simp add: N_def)
  then obtain M where M: "N = Suc M" using c1 by (cases N) auto
  have "2 * sf (2 * M + 1) = 2 * (2 * N * N - N)"
    using two_sf[of "2 * M + 1"] M by (simp add: algebra_simps)
  then have s: "sf (2 * M + 1) = 2 * N * N - N" by simp
  have NN: "N \<le> 2 * N * N" using M by simp
  define j where "j = 2 * N - c"
  have m: "(2 * n * c * c) * n = 2 * N * N" by (simp add: N_def algebra_simps)
  have nc: "n * c - c = N - c" by (simp add: N_def)
  have eq: "(n * c - c) + (2 * n * c * c) * n = sf (2 * M + 1) + j"
    unfolding m nc s j_def using cN NN by simp
  have le: "j \<le> 2 * M + 1" using M c1 by (simp add: j_def)
  have "funL ((n * c - c) + (2 * n * c * c) * n) = (2 * M + 1) - j" unfolding eq by (rule funL_diag[OF le])
  then have "funL ((n * c - c) + (2 * n * c * c) * n) = (2 * M + 1) - (2 * N - c)" by (simp only: j_def)
  also have "\<dots> = c - 1" using M cN c1 by simp
  finally show ?thesis .
qed

context
  fixes U :: "uop set" and n :: nat
  assumes P: "opPlusI \<in> U" and n: "1 \<le> n"
begin

lemma one_in_E: "cst 1 \<in> clos (basis_C funE U n)"
proof (rule one_by_descent[OF P n])
  fix c assume c: "cst c \<in> clos (basis_C funE U n)" and c1: "1 \<le> c"
  have "cst (funE (c + (n * c * c + 2 * c) * n)) \<in> clos (basis_C funE U n)" by (rule X_cst_in[OF P c])
  then show "cst (c - 1) \<in> clos (basis_C funE U n)" by (simp only: E_desc[OF n c1])
qed

lemma one_in_K: "cst 1 \<in> clos (basis_C funK U n)"
proof (rule one_by_descent[OF P n])
  fix c assume c: "cst c \<in> clos (basis_C funK U n)" and c1: "1 \<le> c"
  have "cst (funK (c + (2 * n * c * c + 3 * c) * n)) \<in> clos (basis_C funK U n)" by (rule X_cst_in[OF P c])
  then show "cst (c - 1) \<in> clos (basis_C funK U n)" by (simp only: K_desc[OF n c1])
qed

lemma one_in_L: "cst 1 \<in> clos (basis_C funL U n)"
proof (rule one_by_descent[OF P n])
  fix c assume c: "cst c \<in> clos (basis_C funL U n)" and c1: "1 \<le> c"
  have "cst (funL (c + (2 * n * c * c + 2 * c) * n)) \<in> clos (basis_C funL U n)"
    by (rule X_cst_in[OF P c])
  then have w: "cst (n * c - c) \<in> clos (basis_C funL U n)" by (simp only: L_desc1[OF n])
  have "cst (funL ((n * c - c) + (2 * n * c * c) * n)) \<in> clos (basis_C funL U n)"
    by (rule X_cst_in[OF P w])
  then show "cst (c - 1) \<in> clos (basis_C funL U n)" by (simp only: L_desc2[OF n c1])
qed

theorem C_eq_C1_ELK:
  "clos (basis_C funE U n) = clos (basis_C funE U 1)"
  "clos (basis_C funK U n) = clos (basis_C funK U 1)"
  "clos (basis_C funL U n) = clos (basis_C funL U 1)"
  by (rule C_eq_C1[OF P one_in_E n], rule C_eq_C1[OF P one_in_K n], rule C_eq_C1[OF P one_in_L n])

end

subsection \<open>The constant \<open>0\<close>\<close>

text \<open>If \<open>X(0) = 0\<close> and every operator of \<open>U\<close> preserves \<open>F(0) = 0\<close>, then every function of
  \<open>\<langle>0, X, U, FG\<rangle>\<close> fixes \<open>0\<close>.\<close>
lemma C0_fix0:
  assumes X: "X 0 = 0" and U: "\<forall>u \<in> U. \<forall>F. F 0 = 0 \<longrightarrow> u F 0 = 0"
    and F: "F \<in> clos (basis_C X U 0)"
  shows "F 0 = 0"
  using F
proof (induct rule: clos_induct)
  case (init F) then show ?case using X by (auto simp: clos_defs cst_def)
next
  case (unop u F) then show ?case using U by (simp add: clos_defs applyU_def)
next
  case (binop b F G) then show ?case by (simp add: clos_defs applyB_def)
qed

lemma U_box_fix0: "\<forall>u \<in> {opPlusI, opBox}. \<forall>F. F 0 = 0 \<longrightarrow> u F 0 = 0"
  by (auto simp: opPlusI_def)

lemma U_inv_fix0: "\<forall>u \<in> {opPlusI, opInv}. \<forall>F. F 0 = 0 \<longrightarrow> u F 0 = 0"
  by (auto simp: opPlusI_def opInv_def)

lemma one_notin_C0:
  assumes "X 0 = 0" "\<forall>u \<in> U. \<forall>F. F 0 = 0 \<longrightarrow> u F 0 = 0"
  shows "cst 1 \<notin> clos (basis_C X U 0)"
  using C0_fix0[of X U "cst 1", OF assms] by (auto simp: cst_def)


section \<open>Primitive recursive functions\<close>

theorem Ext_Cn_suitable:
  "suitable (basis_C funE {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
  "suitable (basis_C funK {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
  "suitable (basis_C funL {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
proof -
  have P: "opPlusI \<in> {opPlusI, opBox}" by simp
  have one: "cst 1 \<in> PrimNN" by (rule cst_PR)
  have no: "\<not> suitable (basis_C X {opPlusI, opBox} 0)" if X0: "X 0 = 0" for X
  proof
    assume "suitable (basis_C X {opPlusI, opBox} 0)"
    then have "cst 1 \<in> clos (basis_C X {opPlusI, opBox} 0)" using one by (simp add: suitable_def)
    moreover have "cst 1 \<notin> clos (basis_C X {opPlusI, opBox} 0)" by (rule one_notin_C0[of X "{opPlusI, opBox}", OF X0 U_box_fix0])
    ultimately show False by contradiction
  qed
  show "suitable (basis_C funE {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funE {opPlusI, opBox} n) = clos (basis_C funE {opPlusI, opBox} 1)" by (rule C_eq_C1_ELK(1)[OF P True])
    then show ?thesis using True Theorem_6_7 by (simp add: basis_6_C suitable_def)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funE] funE_small(1) by simp
  qed
  show "suitable (basis_C funK {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funK {opPlusI, opBox} n) = clos (basis_C funK {opPlusI, opBox} 1)" by (rule C_eq_C1_ELK(2)[OF P True])
    then show ?thesis using True Theorem_6_8_K by (simp add: basis_6K_C suitable_def)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funK] funK_0 by simp
  qed
  show "suitable (basis_C funL {opPlusI, opBox} n) \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funL {opPlusI, opBox} n) = clos (basis_C funL {opPlusI, opBox} 1)" by (rule C_eq_C1_ELK(3)[OF P True])
    then show ?thesis using True Theorem_6_8_L by (simp add: basis_6L_C suitable_def)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funL] funL_0 by simp
  qed
qed


section \<open>General recursive functions\<close>

context Robinson_1950
begin

theorem Ext_GRCn:
  "clos (basis_C funE {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
  "clos (basis_C funK {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
  "clos (basis_C funL {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
proof -
  have P: "opPlusI \<in> {opPlusI, opInv}" by simp
  have one: "cst 1 \<in> GR" using one_in_JR Robinson_1950_sec4_thm3 by simp
  have no: "clos (basis_C X {opPlusI, opInv} 0) \<noteq> GR" if X0: "X 0 = 0" for X
  proof
    assume "clos (basis_C X {opPlusI, opInv} 0) = GR"
    then have "cst 1 \<in> clos (basis_C X {opPlusI, opInv} 0)" using one by simp
    moreover have "cst 1 \<notin> clos (basis_C X {opPlusI, opInv} 0)" by (rule one_notin_C0[of X "{opPlusI, opInv}", OF X0 U_inv_fix0])
    ultimately show False by contradiction
  qed
  show "clos (basis_C funE {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funE {opPlusI, opInv} n) = clos (basis_C funE {opPlusI, opInv} 1)" by (rule C_eq_C1_ELK(1)[OF P True])
    then show ?thesis using True Ext_GR(1) by (simp add: basis_GR_C)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funE] funE_small(1) by simp
  qed
  show "clos (basis_C funK {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funK {opPlusI, opInv} n) = clos (basis_C funK {opPlusI, opInv} 1)" by (rule C_eq_C1_ELK(2)[OF P True])
    then show ?thesis using True Ext_GR(2) by (simp add: basis_GR_C)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funK] funK_0 by simp
  qed
  show "clos (basis_C funL {opPlusI, opInv} n) = GR \<longleftrightarrow> 1 \<le> n"
  proof (cases "1 \<le> n")
    case True
    have "clos (basis_C funL {opPlusI, opInv} n) = clos (basis_C funL {opPlusI, opInv} 1)" by (rule C_eq_C1_ELK(3)[OF P True])
    then show ?thesis using True Ext_GR(3) by (simp add: basis_GR_C)
  next
    case False then have "n = 0" by simp
    then show ?thesis using no[of funL] funL_0 by simp
  qed
qed

end

end
