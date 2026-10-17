(*  Title:   UPRF_Ext_GR.thy

    The general recursive analogue of Section 6 (README, open problem 3.2).

    J. Robinson (General recursive functions, Proc. AMS 1 (1950), Sec. 4, Thm. 3) proved that
    the unary general recursive functions are the closure of
       \<langle>S, E, F + G, FG, F\<^sup>-\<^sup>1\<rangle>,   F\<^sup>-\<^sup>1(x) = \<mu>y [F(y) = x]   (F onto).
    Here the binary operator F + G is replaced by the unary operator F\<^sup>+(x) = F(x) + x: for
    X \<in> {E, K, L},
       clos \<langle>1, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle> = clos \<langle>S, E, F + G, FG, F\<^sup>-\<^sup>1\<rangle>,
    so, assuming Robinson's theorem, these bases generate the unary general recursive functions.
    The constant 1 cannot be dropped: without it every generated function fixes 0.

    The proof generates inside the closure the functions E, S, D, M\<^sub>3, Sq, Hf, Rt used by
    Lemmas 6.2-6.6, with inversion in place of iteration; Lemma 6.6 then gives F + G.
    With E:  E\<^sup>-\<^sup>1(x) = \<lceil>x/2\<rceil>\<^sup>2 + x,   F\<^sup>- \<equiv> E (S S S M\<^sub>3 F E)\<^sup>+ S (E\<^sup>-\<^sup>1 D F\<^sup>+)\<^sup>+,
             Sq \<equiv> ((E\<^sup>-\<^sup>1 D)\<^sup>-)\<^sup>-,   I - F \<equiv> E (S (F\<^sup>+)\<^sup>+ E)\<^sup>+ (Sq F\<^sup>+)\<^sup>+,
             W \<equiv> E (S S D E E)\<^sup>+ E\<^sup>-\<^sup>1  (W(y) = 2E(y) + [y even]),   Hf \<equiv> E W\<^sup>-\<^sup>1,
             Rt \<equiv> Hf Hf S S E (I - 1) (I - E) S M\<^sub>4.
    With K:  Z \<equiv> K\<^sup>-\<^sup>1 (Z(x) = A(x) + x),  A \<equiv> Z - I,  F\<^sup>- \<equiv> K (S S S M\<^sub>3 F K)\<^sup>+ (A F\<^sup>+)\<^sup>+,
             Sq \<equiv> (((D Z)\<^sup>-)\<^sup>-)\<^sup>-,   P \<equiv> K (K S)\<^sup>-\<^sup>1,   U \<equiv> I - A K P (I - K)  (U = V + K),
             Hf \<equiv> K U\<^sup>-\<^sup>1,   B \<equiv> I - (I - Sq (I - Hf) U) (I - K)  (B = K + \<lceil>V/2\<rceil>\<^sup>2),   E \<equiv> K B\<^sup>-\<^sup>1,
    where V is the triangular root.  With L:  K \<equiv> L 1\<^sup>+ ((1\<^sup>+)\<^sup>+ L)\<^sup>+ (as in Theorem 6.8).
*)

theory UPRF_Ext_GR
  imports UPRF_Sec6_Thm68
begin

section \<open>Inversion\<close>

text \<open>\<open>F\<^sup>-\<^sup>1(x) = \<mu>y [F(y) = x]\<close>.  Robinson applies inversion only to onto functions; as an operator
  on all functions, \<open>opInv\<close> leaves a function that is not onto unchanged, so a closure under
  \<open>opInv\<close> is exactly a closure under Robinson's restricted inversion.\<close>
definition opInv :: uop where
  "opInv F = (if surj F then (\<lambda>x. LEAST y. F y = x) else F)"

lemma opInv_surj: "surj F \<Longrightarrow> opInv F x = (LEAST y. F y = x)"
  by (simp add: opInv_def)

lemma opInv_right: assumes "surj F" shows "F (opInv F x) = x"
proof -
  from surjD[OF assms] obtain y where "x = F y" by blast
  then have "F y = x" by simp
  then show ?thesis unfolding opInv_surj[OF assms] by (rule LeastI)
qed

lemma opInv_least: "surj F \<Longrightarrow> F y = x \<Longrightarrow> opInv F x \<le> y"
  unfolding opInv_surj by (rule Least_le)

lemma surjI': "(\<And>x. F (g x) = x) \<Longrightarrow> surj F"
  by (metis surjI)

lemma clos_inv_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> opInv \<in> unops B \<Longrightarrow> opInv F \<in> clos B"
  using clos_unop[of opInv B F] by simp

subsection \<open>Equalities with \<open>F\<^sup>-\<^sup>1\<close> and subtraction by inversion\<close>

text \<open>\<open>F\<^sup>-\<^sup>1(x) = v\<close> as soon as \<open>F\<close> is onto, \<open>v\<close> is a preimage of \<open>x\<close>, and every preimage is at
  least \<open>v\<close>.\<close>
lemma opInv_eqI:
  assumes s: "surj F" and v: "F v = x" and least: "\<And>y. F y = x \<Longrightarrow> v \<le> y"
  shows "opInv F x = v"
  using opInv_least[OF s v] least[OF opInv_right[OF s]] by simp

text \<open>The method \<open>inv_eq\<close> proves \<open>F\<^sup>-\<^sup>1(x) = v\<close> or \<open>F\<^sup>-\<^sup>1 = G\<close> with \<open>opInv_eqI\<close>.  Surjectivity is
  closed by the fact given with "surj:", and the other goals (\<open>F(v) = x\<close> and the minimality of
  \<open>v\<close>) by \<open>simp\<close> and \<open>linarith\<close> with the facts given with "add:".  The goals that remain are
  left to the user.\<close>
method inv_eq uses surj add =
  ((rule ext)?, rule opInv_eqI;
     (solves \<open>rule surj\<close> | solves \<open>simp add: add\<close> | solves \<open>(simp add: add)?, linarith\<close>
      | succeed))

text \<open>Subtraction by inversion.  Let every \<open>y\<close> decompose as \<open>y = base(t) + X(y)\<close> with
  \<open>X(y) \<le> bound(t)\<close>, where \<open>X(base(t) + k) = k\<close> for \<open>k \<le> bound(t)\<close> (for \<open>E\<close>: \<open>base(t) = t\<^sup>2\<close>,
  \<open>bound(t) = 2t\<close>; for \<open>K\<close>: \<open>base = A\<close>, \<open>bound(t) = t\<close>).  If \<open>V(y) = y + c\<close>, then \<open>X (X V)\<^sup>-\<^sup>1\<close>
  subtracts \<open>c\<close>.  No minimality is needed.\<close>
lemma sub_inv:
  fixes X V :: ufun and base bound :: "nat \<Rightarrow> nat"
  assumes dec: "\<And>y. \<exists>t. y = base t + X y \<and> X y \<le> bound t"
    and diag: "\<And>t k. k \<le> bound t \<Longrightarrow> X (base t + k) = k"
    and big: "\<And>z. \<exists>t. z \<le> bound t \<and> c \<le> base t"
    and V: "\<And>y. V y = y + c"
  shows sub_inv_surj: "surj (X \<circ> V)"
    and sub_inv_val: "c \<le> x \<Longrightarrow> X (opInv (X \<circ> V) x) = x - c"
proof -
  show s: "surj (X \<circ> V)"
    unfolding surj_def
  proof
    fix z
    obtain t where t: "z \<le> bound t" "c \<le> base t" using big by blast
    have "(X \<circ> V) (base t + z - c) = z" using t by (simp add: V diag)
    then show "\<exists>y. z = (X \<circ> V) y" by metis
  qed
  assume cx: "c \<le> x"
  let ?y = "opInv (X \<circ> V) x"
  have e: "X (?y + c) = x" using opInv_right[OF s, of x] by (simp add: V)
  obtain t where t: "?y + c = base t + X (?y + c)" "X (?y + c) \<le> bound t" using dec by blast
  have y: "?y = base t + (x - c)" using t e cx by linarith
  have "X ?y = X (base t + (x - c))" using arg_cong[OF y, of X] .
  also have "\<dots> = x - c" using t e by (intro diag) linarith
  finally show "X ?y = x - c" .
qed


section \<open>The bases\<close>

text \<open>J. Robinson's basis \<open>\<langle>S, E, F + G, FG, F\<^sup>-\<^sup>1\<rangle>\<close>.\<close>
definition basis_JR :: basis where
  "basis_JR = Basis {funS, funE} {opInv} {opPlus, (\<circ>)}"

text \<open>\<open>\<langle>1, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close> and \<open>\<langle>X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>.\<close>
definition basis_GR :: "ufun \<Rightarrow> basis" where
  "basis_GR X = Basis {cst 1, X} {opPlusI, opInv} {(\<circ>)}"

definition basis_GR0 :: "ufun \<Rightarrow> basis" where
  "basis_GR0 X = Basis {X} {opPlusI, opInv} {(\<circ>)}"

lemmas basis_JR_sel [clos_defs] =
  basis.sel[of "{funS, funE}" "{opInv}" "{opPlus, (\<circ>)}", folded basis_JR_def]
lemmas basis_GR_sel [clos_defs] =
  basis.sel[of "{cst 1, X}" "{opPlusI, opInv}" "{(\<circ>)}", folded basis_GR_def] for X
lemmas basis_GR0_sel [clos_defs] =
  basis.sel[of "{X}" "{opPlusI, opInv}" "{(\<circ>)}", folded basis_GR0_def] for X

abbreviation CJR :: "ufun set" where "CJR \<equiv> clos basis_JR"
abbreviation CGE :: "ufun set" where "CGE \<equiv> clos (basis_GR funE)"
abbreviation CGK :: "ufun set" where "CGK \<equiv> clos (basis_GR funK)"
abbreviation CGL :: "ufun set" where "CGL \<equiv> clos (basis_GR funL)"


section \<open>Arithmetic facts\<close>

lemma funE_decomp: "funRt y * funRt y + funE y = y"
  using funRt_sq_le[of y] by (simp add: funE_alt)

lemma funE_bound: "funE y \<le> 2 * funRt y"
  using funRt_sq_gt[of y] funRt_sq_le[of y] by (simp add: funE_alt algebra_simps)

lemma two_le_sq_Suc: "2 * r \<le> r * r + (1::nat)"
proof (cases r)
  case 0 then show ?thesis by simp
next
  case (Suc n) then show ?thesis by (simp add: algebra_simps)
qed

text \<open>\<open>2E(y) \<le> y + 1\<close>.\<close>
lemma two_funE_le: "2 * funE y \<le> y + 1"
proof -
  let ?r = "funRt y" and ?e = "funE y"
  have "?e \<le> 2 * ?r" by (rule funE_bound)
  also have "\<dots> \<le> ?r * ?r + 1" by (rule two_le_sq_Suc)
  finally have "?e \<le> ?r * ?r + 1" .
  then show ?thesis using funE_decomp[of y] by linarith
qed

text \<open>\<open>\<lfloor>\<surd>(4x+1)\<rfloor> div 2 = \<lfloor>\<surd>x\<rfloor>\<close>.\<close>
lemma funRt_4x1: "funRt (4 * x + 1) div 2 = funRt x"
proof -
  let ?m = "funRt x" and ?n = "funRt (4 * x + 1)"
  have lo: "(2 * ?m) * (2 * ?m) \<le> 4 * x + 1" using funRt_sq_le[of x] by simp
  have hi: "4 * x + 1 < (2 * ?m + 2) * (2 * ?m + 2)" using funRt_sq_gt[of x] by (simp add: algebra_simps)
  have "2 * ?m \<le> ?n"
  proof (rule ccontr)
    assume "\<not> 2 * ?m \<le> ?n"
    then have "Suc ?n \<le> 2 * ?m" by simp
    then have "Suc ?n * Suc ?n \<le> (2 * ?m) * (2 * ?m)" by (intro mult_le_mono)
    with lo funRt_sq_gt[of "4 * x + 1"] show False by linarith
  qed
  moreover have "?n < 2 * ?m + 2"
  proof (rule ccontr)
    assume "\<not> ?n < 2 * ?m + 2"
    then have "2 * ?m + 2 \<le> ?n" by simp
    then have "(2 * ?m + 2) * (2 * ?m + 2) \<le> ?n * ?n" by (intro mult_le_mono)
    with hi funRt_sq_le[of "4 * x + 1"] show False by linarith
  qed
  ultimately show ?thesis by linarith
qed

text \<open>Cantor decomposition \<open>y = A(V(y)) + K(y)\<close> with \<open>K(y) \<le> V(y)\<close>.\<close>
lemma funK_decomp: "sf (funV y) + funK y = y"
  using sf_c_sum_plus_c_fst[of y] by (simp add: funK_eq_c_fst funV_eq_c_sum)

lemma funK_le_V: "funK y \<le> funV y"
  using c_fst_le_c_sum[of y] by (simp add: funK_eq_c_fst funV_eq_c_sum)

lemma funV_diag: "k \<le> t \<Longrightarrow> funV (sf t + k) = t"
  unfolding funV_eq_c_sum by (rule c_sum_unique) (simp_all add: sf_Suc)

lemma funK_le: "funK y \<le> y"
  using funK_decomp[of y] by linarith

lemma sf_Suc_pred: "0 < t \<Longrightarrow> sf t = sf (t - 1) + (t - 1) + 1"
  using sf_Suc[of "t - 1"] by simp


section \<open>Inclusions between the closures and Robinson's\<close>

subsection \<open>\<open>clos \<langle>1, E, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle> \<subseteq> clos \<langle>S, E, F + G, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

lemma surj_funE: "surj funE"
  by (rule surjI'[of _ "\<lambda>x. x * x + x"]) (rule funE_sq_add, simp)

text \<open>\<open>E\<^sup>-\<^sup>1(x) = \<lceil>x/2\<rceil>\<^sup>2 + x\<close>.\<close>
lemma Einv_val: "opInv funE x = ((x + 1) div 2) * ((x + 1) div 2) + x"
proof -
  let ?c = "(x + 1) div 2"
  have xc: "x \<le> 2 * ?c" by simp
  have "(LEAST y. funE y = x) = ?c * ?c + x"
  proof (rule Least_equality)
    show "funE (?c * ?c + x) = x" using xc by (rule funE_sq_add)
  next
    fix y assume y: "funE y = x"
    let ?r = "funRt y"
    have "x \<le> 2 * ?r" using funE_bound[of y] y by simp
    then have "?c \<le> ?r" by simp
    then have "?c * ?c \<le> ?r * ?r" by (intro mult_le_mono)
    then show "?c * ?c + x \<le> y" using funE_decomp[of y] y by linarith
  qed
  then show ?thesis by (simp add: opInv_surj[OF surj_funE])
qed

lemma Einv_D: "opInv funE (funD z) = z * z + 2 * z"
proof -
  have h: "(2 * z + 1) div 2 = z" by simp
  show ?thesis by (simp only: funD_def Einv_val h)
qed

lemma I_expr_inv: "funE \<circ> opInv funE = funI"
  by (rule ext) (simp add: opInv_right[OF surj_funE] funI_def)

lemma zero_expr_JR: "funE \<circ> funS \<circ> opInv funE \<circ> opPlus funI funI = cst 0"
proof
  fix x :: nat
  have "Suc (opInv funE (funD x)) = (x + 1) * (x + 1) + 0" by (simp add: Einv_D algebra_simps)
  then have "funE (Suc (opInv funE (funD x))) = 0" using funE_sq_add[of 0 "x + 1"] by simp
  moreover have "opPlus funI funI x = funD x" by (simp add: opPlus_def funI_def funD_def)
  ultimately show "(funE \<circ> funS \<circ> opInv funE \<circ> opPlus funI funI) x = cst 0 x"
    by (simp add: funS_def cst_def)
qed

lemma I_in_JR [clos_rules]: "funI \<in> CJR" by (subst I_expr_inv[symmetric]) clos_solve
lemma zero_in_JR [clos_rules]: "cst 0 \<in> CJR" by (subst zero_expr_JR[symmetric]) clos_solve

lemma one_expr: "funS \<circ> cst 0 = cst 1"
  by (rule ext) eval

lemma one_in_JR [clos_rules]: "cst 1 \<in> CJR" by (subst one_expr[symmetric]) clos_solve

lemma plusI_expr: "opPlus F funI = opPlusI F"
  by (rule ext) eval

lemma plusI_in_JR [clos_rules]: "F \<in> CJR \<Longrightarrow> opPlusI F \<in> CJR"
  by (subst plusI_expr[symmetric]) clos_solve

lemma GE_sub_JR: "CGE \<subseteq> CJR" by clos_subset_m

subsection \<open>Generating \<open>Sq\<close>, \<open>Hf\<close>, \<open>Rt\<close> in \<open>clos \<langle>1, E, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

lemma I_expr: "opPlusI (cst 0) = funI"
  by (rule ext) eval

lemma S_in_GE [clos_rules]: "funS \<in> CGE" by (subst S_expr[symmetric]) clos_solve
lemma zero_in_GE [clos_rules]: "cst 0 \<in> CGE" by (subst zero_expr[symmetric]) clos_solve
lemma I_in_GE [clos_rules]: "funI \<in> CGE" by (subst I_expr[symmetric]) clos_solve
lemma D_in_GE [clos_rules]: "funD \<in> CGE" by (subst D_expr[symmetric]) clos_solve
lemma M3_in_GE [clos_rules]: "funM3 \<in> CGE" by (subst M3_expr[symmetric]) clos_solve

text \<open>\<open>F\<^sup>-\<close> without \<open>Sq\<close>: \<open>F\<^sup>- \<equiv> E (S S S M\<^sub>3 F E)\<^sup>+ S (E\<^sup>-\<^sup>1 D F\<^sup>+)\<^sup>+\<close>.\<close>
definition exprMinusIE :: uop where
  "exprMinusIE F = funE \<circ> opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funE) \<circ> funS
                     \<circ> opPlusI (opInv funE \<circ> funD \<circ> opPlusI F)"

lemma exprMinusIE_in [clos_rules]: "F \<in> CGE \<Longrightarrow> exprMinusIE F \<in> CGE"
  unfolding exprMinusIE_def by clos_solve

lemma exprMinusIE_val:
  assumes "x \<le> F x" shows "exprMinusIE F x = F x - x"
proof -
  define s where "s = F x + x"
  define v where "v = (s + 1) * (s + 1) + x"
  have g: "(opInv funE \<circ> funD \<circ> opPlusI F) x = s * s + 2 * s"
    by (simp only: comp_apply opPlusI_def s_def[symmetric] Einv_D)
  have sq1: "(s + 1) * (s + 1) = s * s + 2 * s + 1" by (simp add: algebra_simps)
  have v: "funS (opPlusI (opInv funE \<circ> funD \<circ> opPlusI F) x) = v"
    using sq1 by (simp only: funS_def opPlusI_def g v_def)
  have ev: "funE v = x" unfolding v_def by (rule funE_sq_add) (simp add: s_def)
  have h: "opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funE) v = Suc (Suc (Suc (3 * F x))) + v"
    by (simp only: opPlusI_def comp_apply ev funS_def funM3_def)
  have sq2: "(s + 2) * (s + 2) = (s + 1) * (s + 1) + 2 * s + 3" by (simp add: algebra_simps)
  have ar: "Suc (Suc (Suc (3 * F x))) + v = (s + 2) * (s + 2) + (F x - x)"
    using assms sq2 by (simp add: v_def s_def)
  have "exprMinusIE F x = funE (opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funE)
                              (funS (opPlusI (opInv funE \<circ> funD \<circ> opPlusI F) x)))"
    by (simp only: exprMinusIE_def comp_apply)
  also have "\<dots> = funE ((s + 2) * (s + 2) + (F x - x))" by (simp only: v h ar)
  also have "\<dots> = F x - x" by (rule funE_sq_add) (simp add: s_def)
  finally show ?thesis .
qed

lemma Sq_expr_GE: "exprMinusIE (exprMinusIE (opInv funE \<circ> funD)) = funSq"
proof
  fix x :: nat
  have b: "exprMinusIE (opInv funE \<circ> funD) x = x * x + x"
    by (subst exprMinusIE_val) (simp_all add: Einv_D)
  show "exprMinusIE (exprMinusIE (opInv funE \<circ> funD)) x = funSq x"
    by (subst exprMinusIE_val) (simp_all add: b funSq_def)
qed

lemma Sq_in_GE [clos_rules]: "funSq \<in> CGE" by (subst Sq_expr_GE[symmetric]) clos_solve

text \<open>\<open>I - F \<equiv> E (S (F\<^sup>+)\<^sup>+ E)\<^sup>+ (Sq F\<^sup>+)\<^sup>+\<close> (if \<open>F(x) \<le> x\<close>).\<close>
definition exprIminusE :: uop where
  "exprIminusE F = funE \<circ> opPlusI (funS \<circ> opPlusI (opPlusI F) \<circ> funE) \<circ> opPlusI (funSq \<circ> opPlusI F)"

lemma exprIminusE_in [clos_rules]: "F \<in> CGE \<Longrightarrow> exprIminusE F \<in> CGE"
  unfolding exprIminusE_def by clos_solve

lemma exprIminusE_val:
  assumes "F x \<le> x" shows "exprIminusE F x = x - F x"
proof -
  define y where "y = (F x + x) * (F x + x) + x"
  have p: "opPlusI (funSq \<circ> opPlusI F) x = y" by (simp only: opPlusI_def comp_apply funSq_def y_def)
  have e: "funE y = x" unfolding y_def by (rule funE_sq_add) simp
  have q: "opPlusI (funS \<circ> opPlusI (opPlusI F) \<circ> funE) y = Suc (F x + x + x) + y"
    by (simp only: opPlusI_def comp_apply e funS_def)
  have c: "(F x + x) * (F x + x) = (x + F x) * (x + F x)" by (simp add: add.commute)
  have ar: "Suc (F x + x + x) + y = (x + F x) * (x + F x) + 3 * x + F x + 1"
    using c by (simp add: y_def)
  have "exprIminusE F x = funE (opPlusI (funS \<circ> opPlusI (opPlusI F) \<circ> funE)
                                      (opPlusI (funSq \<circ> opPlusI F) x))"
    by (simp only: exprIminusE_def comp_apply)
  also have "\<dots> = funE ((x + F x) * (x + F x) + 3 * x + F x + 1)" by (simp only: p q ar)
  also have "\<dots> = x - F x" using assms by (rule robinson_diff_E)
  finally show ?thesis .
qed

text \<open>\<open>W \<equiv> E (S S D E E)\<^sup>+ E\<^sup>-\<^sup>1\<close>, \<open>W(y) = 2E(y) + [y even]\<close> (Robinson's \<open>W\<close>, 1950, Sec. 3).\<close>
definition exprW :: ufun where
  "exprW = funE \<circ> opPlusI (funS \<circ> funS \<circ> funD \<circ> funE \<circ> funE) \<circ> opInv funE"

lemma exprW_in [clos_rules]: "exprW \<in> CGE" unfolding exprW_def by clos_solve

lemma exprW_val: "exprW y = 2 * funE y + (1 - y mod 2)"
proof -
  define c where "c = (y + 1) div 2"
  define e where "e = funE y"
  have c2: "2 * c = y + y mod 2" unfolding c_def by presburger
  have m2: "y mod 2 \<le> 1" by simp
  have inv: "opInv funE y = c * c + y" by (simp only: Einv_val c_def)
  have ei: "funE (c * c + y) = y" by (rule funE_sq_add) (simp add: c2)
  have h: "opPlusI (funS \<circ> funS \<circ> funD \<circ> funE \<circ> funE) (c * c + y) = Suc (Suc (2 * e)) + (c * c + y)"
    by (simp only: opPlusI_def comp_apply ei funS_def funD_def e_def)
  have e2: "2 * e \<le> y + 1" unfolding e_def by (rule two_funE_le)
  have sq: "(c + 1) * (c + 1) = c * c + 2 * c + 1" by (simp add: algebra_simps)
  have ar: "Suc (Suc (2 * e)) + (c * c + y) = (c + 1) * (c + 1) + (2 * e + (1 - y mod 2))"
    using sq c2 m2 by arith
  have bd: "2 * e + (1 - y mod 2) \<le> 2 * (c + 1)" using e2 c2 m2 by arith
  have "exprW y = funE (opPlusI (funS \<circ> funS \<circ> funD \<circ> funE \<circ> funE) (opInv funE y))"
    by (simp only: exprW_def comp_apply)
  also have "\<dots> = funE ((c + 1) * (c + 1) + (2 * e + (1 - y mod 2)))" by (simp only: inv h ar)
  also have "\<dots> = 2 * e + (1 - y mod 2)" using bd by (rule funE_sq_add)
  finally show ?thesis by (simp only: e_def)
qed

lemma sq_add_mod2: "(m * m + k) mod 2 = (m + k) mod (2::nat)"
proof -
  have "even (m * m + k) \<longleftrightarrow> even (m + k)" by simp
  then show ?thesis by (simp add: mod2_eq_if)
qed

lemma surj_exprW: "surj exprW"
proof (rule surjI'[of _ "\<lambda>x. (x div 2 + 1 + x mod 2) * (x div 2 + 1 + x mod 2) + x div 2"])
  fix x :: nat
  define k where "k = x div 2"
  define b where "b = x mod 2"
  define m where "m = k + 1 + b"
  have b1: "b \<le> 1" by (simp add: b_def)
  have Ey: "funE (m * m + k) = k" by (rule funE_sq_add) (simp add: m_def)
  have mk: "m + k = 2 * k + 1 + b" by (simp add: m_def)
  have "(m * m + k) mod 2 = (2 * k + 1 + b) mod 2" by (simp only: sq_add_mod2 mk)
  also have "\<dots> = 1 - b" using b1 by presburger
  finally have par: "(m * m + k) mod 2 = 1 - b" .
  have "exprW (m * m + k) = 2 * k + b" using par b1 by (simp add: exprW_val Ey)
  also have "\<dots> = x" by (simp add: k_def b_def)
  finally show "exprW ((x div 2 + 1 + x mod 2) * (x div 2 + 1 + x mod 2) + x div 2) = x"
    by (simp only: m_def k_def b_def)
qed

lemma Hf_expr_GE: "funE \<circ> opInv exprW = funHf"
proof
  fix x :: nat
  have "exprW (opInv exprW x) = x" by (rule opInv_right[OF surj_exprW])
  then have h: "x = 2 * funE (opInv exprW x) + (1 - opInv exprW x mod 2)" by (simp add: exprW_val)
  show "(funE \<circ> opInv exprW) x = funHf x"
  proof (cases "opInv exprW x mod 2 = 0")
    case True then show ?thesis using h by (simp add: funHf_def)
  next
    case False then have "opInv exprW x mod 2 = 1" by simp
    then show ?thesis using h by (simp add: funHf_def)
  qed
qed

lemma Hf_in_GE [clos_rules]: "funHf \<in> CGE" by (subst Hf_expr_GE[symmetric]) clos_solve

text \<open>\<open>Rt \<equiv> Hf Hf S S E (I - 1) (I - E) S M\<^sub>4\<close>, with \<open>M\<^sub>4(x) = 4x\<close>.\<close>
definition exprRtGE :: ufun where
  "exprRtGE = funHf \<circ> funHf \<circ> funS \<circ> funS \<circ> funE \<circ> exprIminusE (cst 1) \<circ> exprIminusE funE
                \<circ> funS \<circ> opPlusI funM3"

lemma exprRtGE_in [clos_rules]: "exprRtGE \<in> CGE" unfolding exprRtGE_def by clos_solve

lemma Rt_expr_GE: "exprRtGE = funRt"
proof
  fix x :: nat
  define z where "z = 4 * x + 1"
  define n where "n = funRt z"
  have z: "funS (opPlusI funM3 x) = z" by (simp add: funS_def opPlusI_def funM3_def z_def)
  have n1: "1 \<le> n"
  proof (rule ccontr)
    assume "\<not> 1 \<le> n" then have "n = 0" by simp
    then show False using funRt_sq_gt[of z] by (simp add: n_def z_def)
  qed
  have ie: "exprIminusE funE z = n * n"
    using funE_decomp[of z] by (simp add: exprIminusE_val funE_le n_def)
  have i1: "exprIminusE (cst 1) (n * n) = (n - 1) * (n - 1) + 2 * (n - 1)"
  proof -
    have "1 \<le> n * n" using n1 by simp
    then have "exprIminusE (cst 1) (n * n) = n * n - 1" by (simp add: exprIminusE_val cst_def)
    also have "\<dots> = (n - 1) * (n - 1) + 2 * (n - 1)" using n1 by (cases n) (simp_all add: algebra_simps)
    finally show ?thesis .
  qed
  have eE: "funE ((n - 1) * (n - 1) + 2 * (n - 1)) = 2 * (n - 1)" by (rule funE_sq_add) simp
  have s2: "Suc (Suc (2 * (n - 1))) = 2 * n" using n1 by arith
  have "exprRtGE x = funHf (funHf (funS (funS (funE (exprIminusE (cst 1)
                       (exprIminusE funE (funS (opPlusI funM3 x))))))))"
    by (simp only: exprRtGE_def comp_apply)
  also have "\<dots> = funHf (funHf (funS (funS (2 * (n - 1)))))" by (simp only: z ie i1 eE)
  also have "\<dots> = n div 2" by (simp only: funS_def s2) (simp add: funHf_def)
  finally have "exprRtGE x = n div 2" .
  then show "exprRtGE x = funRt x" using funRt_4x1[of x] by (simp add: n_def z_def)
qed

lemma Rt_in_GE [clos_rules]: "funRt \<in> CGE" by (subst Rt_expr_GE[symmetric]) clos_solve

subsection \<open>Lemmas 6.2-6.6 in \<open>clos \<langle>1, E, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

text \<open>The expressions of Lemmas 6.2-6.6 only use \<open>E, S, D, M\<^sub>3, Sq, Hf, Rt\<close>, composition and
  \<open>F\<^sup>+\<close>; their values were computed in \<open>UPRF_Sec6\<close>.\<close>

lemma exprMinusI_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> exprMinusI F \<in> CGE"
  unfolding exprMinusI_def by clos_solve
lemma exprOplus_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> exprOplus F G \<in> CGE"
  unfolding exprOplus_def by clos_solve
lemma exprOminus_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> exprOminus F G \<in> CGE"
  unfolding exprOminus_def by clos_solve
lemma Phat_in_GE [clos_rules]: "exprPhat \<in> CGE"
  unfolding exprPhat_def by clos_solve
lemma exprOtimes_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> exprOtimes F G \<in> CGE"
  unfolding exprOtimes_def by clos_solve
lemma exprPlus_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> exprPlus F G \<in> CGE"
  unfolding exprPlus_def by clos_solve
lemma exprMinus_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> exprMinus F G \<in> CGE"
  unfolding exprMinus_def by clos_solve

text \<open>Lemma 6.6 in \<open>clos \<langle>1, E, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>.\<close>
lemma plus_in_GE [clos_rules]: "F \<in> CGE \<Longrightarrow> G \<in> CGE \<Longrightarrow> opPlus F G \<in> CGE"
  using exprPlus_in_GE by (simp add: exprPlus_eq)

lemma minus_in_GE:
  assumes "F \<in> CGE" "G \<in> CGE" and "\<And>x. G x \<le> F x"
  shows "opMinus F G \<in> CGE"
proof -
  have "exprMinus F G = opMinus F G"
    using dE_difference assms(3)
    by (intro ext) (simp add: exprMinus_eq opDiff_apply opMinus_def is_difference_def)
  then show ?thesis using exprMinus_in_GE[OF assms(1,2)] by simp
qed

lemma JR_sub_GE: "CJR \<subseteq> CGE" by clos_subset_m

theorem GR_E_eq_JR: "clos (basis_GR funE) = clos basis_JR"
  using GE_sub_JR JR_sub_GE by (rule equalityI)


section \<open>The bases with \<open>K\<close> and \<open>L\<close>\<close>

subsection \<open>\<open>K\<close> and \<open>L\<close> in \<open>clos \<langle>1, E, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

text \<open>\<open>K = I - A V\<close> and \<open>L = A S V - S\<close>, with \<open>A = Hf Sq\<^sup>+\<close> and \<open>V = Hf (Rt S M\<^sub>8 - 1)\<close>.\<close>
definition exprA :: ufun where "exprA = funHf \<circ> opPlusI funSq"
definition exprV :: ufun where
  "exprV = funHf \<circ> opMinus (funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD) (cst 1)"

lemma A_expr: "exprA = funA"
  by (rule ext) (simp add: exprA_def funA_def funHf_def opPlusI_def funSq_def)

lemma V_expr: "exprV = funV"
  by (rule ext) (simp add: exprV_def funV_def funHf_def opMinus_def funS_def funD_def cst_def)

lemma Rt_pos: "1 \<le> funRt (Suc n)"
proof (rule ccontr)
  assume "\<not> 1 \<le> funRt (Suc n)" then have "funRt (Suc n) = 0" by simp
  then show False using funRt_sq_gt[of "Suc n"] by simp
qed

lemma A_in_GE [clos_rules]: "funA \<in> CGE"
  by (subst A_expr[symmetric]) (unfold exprA_def, clos_solve)

lemma V_in_GE [clos_rules]: "funV \<in> CGE"
proof -
  have m: "opMinus (funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD) (cst 1) \<in> CGE"
  proof (rule minus_in_GE)
    show "funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD \<in> CGE" by clos_solve
    show "cst 1 \<in> CGE" by clos_solve
    fix x :: nat show "cst 1 x \<le> (funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD) x"
      by (simp only: comp_apply cst_def funS_def Rt_pos)
  qed
  have "exprV \<in> CGE" unfolding exprV_def by (clos_solve add: m)
  then show ?thesis by (simp add: V_expr)
qed

lemma K_in_GE [clos_rules]: "funK \<in> CGE"
proof -
  have "opMinus funI (funA \<circ> funV) \<in> CGE"
  proof (rule minus_in_GE)
    show "funI \<in> CGE" by clos_solve
    show "funA \<circ> funV \<in> CGE" by clos_solve
    fix x :: nat show "(funA \<circ> funV) x \<le> funI x"
      using sf_c_sum_le_arg[of x] by (simp add: funI_def funA_eq_sf funV_eq_c_sum)
  qed
  moreover have "opMinus funI (funA \<circ> funV) = funK"
    by (rule ext) (simp add: opMinus_def funI_def funK_def)
  ultimately show ?thesis by simp
qed

lemma L_in_GE [clos_rules]: "funL \<in> CGE"
proof -
  have "opMinus (funA \<circ> funS \<circ> funV) funS \<in> CGE"
  proof (rule minus_in_GE)
    show "funA \<circ> funS \<circ> funV \<in> CGE" by clos_solve
    show "funS \<in> CGE" by clos_solve
    fix x :: nat show "funS x \<le> (funA \<circ> funS \<circ> funV) x"
      using arg_less_sf_at_Suc_of_c_sum[of x] by (simp add: funS_def funA_eq_sf funV_eq_c_sum)
  qed
  moreover have "opMinus (funA \<circ> funS \<circ> funV) funS = funL"
    by (rule ext) (simp add: opMinus_def funS_def funL_def)
  ultimately show ?thesis by simp
qed

lemma GK_sub_GE: "CGK \<subseteq> CGE" by clos_subset_m
lemma GL_sub_GE: "CGL \<subseteq> CGE" by clos_subset_m

subsection \<open>\<open>E\<close> in \<open>clos \<langle>1, K, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

lemma S_in_GK [clos_rules]: "funS \<in> CGK" by (subst S_expr[symmetric]) clos_solve
lemma zero_in_GK [clos_rules]: "cst 0 \<in> CGK" by (subst zero_expr_K[symmetric]) clos_solve
lemma I_in_GK [clos_rules]: "funI \<in> CGK" by (subst I_expr[symmetric]) clos_solve
lemma D_in_GK [clos_rules]: "funD \<in> CGK" by (subst D_expr[symmetric]) clos_solve
lemma M3_in_GK [clos_rules]: "funM3 \<in> CGK" by (subst M3_expr[symmetric]) clos_solve

lemma surj_funK: "surj funK"
  by (rule surjI'[of _ "\<lambda>x. sf x + x"]) (rule funK_diag, simp)

text \<open>\<open>K\<^sup>-\<^sup>1 = Z\<close>.\<close>
lemma Kinv_eq_Z: "opInv funK = funZ"
proof (inv_eq surj: surj_funK add: funZ_sf funK_diag)
  fix x y assume y: "funK y = x"
  have "x \<le> funV y" using funK_le_V[of y] y by simp
  then have "sf x \<le> sf (funV y)" by (rule sf_mono)
  then show "funZ x \<le> y" using funK_decomp[of y] y by (simp add: funZ_sf)
qed

lemma Z_in_GK [clos_rules]: "funZ \<in> CGK" by (subst Kinv_eq_Z[symmetric]) clos_solve

lemma exprIminusF_in_GK [clos_rules]: "F \<in> CGK \<Longrightarrow> exprIminusF F \<in> CGK"
  unfolding exprIminusF_def by clos_solve

text \<open>\<open>A \<equiv> Z - I\<close>, i.e. \<open>A \<equiv> K S S S (Y Z K)\<^sup>+ Z\<close> where \<open>Y \<equiv> (Z Z\<^sup>+ K)\<^sup>+ Z\<close>
  (Robinson's difference with \<open>\<alpha> = Z(x)\<close>, \<open>\<beta> = x\<close>; the sums with \<open>Z(x)\<close> use its left inverse \<open>K\<close>).\<close>
definition exprAK :: ufun where
  "exprAK = funK \<circ> funS \<circ> funS \<circ> funS
              \<circ> opPlusI (opPlusI (funZ \<circ> opPlusI funZ \<circ> funK) \<circ> funZ \<circ> funK) \<circ> funZ"

lemma exprAK_in [clos_rules]: "exprAK \<in> CGK" unfolding exprAK_def by clos_solve

lemma KZ: "funK (funZ x) = x"
  by (simp add: funZ_sf funK_diag)

lemma A_expr_K: "exprAK = funA"
proof
  fix x :: nat
  let ?z = "funZ x"
  have i: "opPlusI (opPlusI (funZ \<circ> opPlusI funZ \<circ> funK) \<circ> funZ \<circ> funK) ?z = funZ (?z + x) + ?z + ?z"
    by (simp only: opPlusI_def comp_apply KZ)
  have "exprAK x = funK (funS (funS (funS (opPlusI (opPlusI (funZ \<circ> opPlusI funZ \<circ> funK) \<circ> funZ \<circ> funK) ?z))))"
    by (simp only: exprAK_def comp_apply)
  also have "\<dots> = funK (funZ (?z + x) + 2 * ?z + 3)"
    by (simp only: i funS_def) (rule arg_cong[where f = funK], arith)
  also have "\<dots> = ?z - x" by (rule robinson_diff_K) (simp add: funZ_sf)
  also have "\<dots> = funA x" by (simp add: funZ_sf funA_eq_sf)
  finally show "exprAK x = funA x" .
qed

lemma A_in_GK [clos_rules]: "funA \<in> CGK" by (subst A_expr_K[symmetric]) clos_solve

text \<open>\<open>F\<^sup>- \<equiv> K (S S S M\<^sub>3 F K)\<^sup>+ (A F\<^sup>+)\<^sup>+\<close> (if \<open>F(x) \<ge> x\<close>).\<close>
definition exprMinusIK :: uop where
  "exprMinusIK F = funK \<circ> opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funK) \<circ> opPlusI (funA \<circ> opPlusI F)"

lemma exprMinusIK_in [clos_rules]: "F \<in> CGK \<Longrightarrow> exprMinusIK F \<in> CGK"
  unfolding exprMinusIK_def by clos_solve

lemma exprMinusIK_val:
  assumes "x \<le> F x" shows "exprMinusIK F x = F x - x"
proof -
  define s where "s = F x + x"
  have p: "opPlusI (funA \<circ> opPlusI F) x = sf s + x"
    by (simp only: opPlusI_def comp_apply funA_eq_sf s_def)
  have k: "funK (sf s + x) = x" by (rule funK_diag) (simp add: s_def)
  have q: "opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funK) (sf s + x) = Suc (Suc (Suc (3 * F x))) + (sf s + x)"
    by (simp only: opPlusI_def comp_apply k funS_def funM3_def)
  have sf2: "sf (Suc (Suc s)) = sf s + 2 * s + 3" using sf_Suc[of s] sf_Suc[of "Suc s"] by simp
  have ar: "Suc (Suc (Suc (3 * F x))) + (sf s + x) = sf (Suc (Suc s)) + (F x - x)"
    using assms sf2 by (simp add: s_def)
  have "exprMinusIK F x = funK (opPlusI (funS \<circ> funS \<circ> funS \<circ> funM3 \<circ> F \<circ> funK) (opPlusI (funA \<circ> opPlusI F) x))"
    by (simp only: exprMinusIK_def comp_apply)
  also have "\<dots> = funK (sf (Suc (Suc s)) + (F x - x))" by (simp only: p q ar)
  also have "\<dots> = F x - x" by (rule funK_diag) (simp add: s_def)
  finally show ?thesis .
qed

lemma Sq_expr_GK: "exprMinusIK (exprMinusIK (exprMinusIK (funD \<circ> funZ))) = funSq"
proof
  fix x :: nat
  have a0: "funD (funZ x) = 2 * sf x + 2 * x" by (simp add: funD_def funZ_sf)
  have a: "funD (funZ x) = x * x + 3 * x" using a0 two_sf[of x] by linarith
  have b: "exprMinusIK (funD \<circ> funZ) x = x * x + 2 * x"
    by (subst exprMinusIK_val) (simp_all add: a)
  have c: "exprMinusIK (exprMinusIK (funD \<circ> funZ)) x = x * x + x"
    by (subst exprMinusIK_val) (simp_all add: b)
  show "exprMinusIK (exprMinusIK (exprMinusIK (funD \<circ> funZ))) x = funSq x"
    by (subst exprMinusIK_val) (simp_all add: c funSq_def)
qed

lemma Sq_in_GK [clos_rules]: "funSq \<in> CGK" by (subst Sq_expr_GK[symmetric]) clos_solve

text \<open>\<open>P \<equiv> K (K S)\<^sup>-\<^sup>1\<close>.\<close>
lemma surj_KS: "surj (funK \<circ> funS)"
proof (rule surjI'[of _ "\<lambda>x. sf (Suc x) + x - 1"])
  fix x :: nat
  have "1 \<le> sf (Suc x)" using sf_Suc[of x] by simp
  then have "Suc (sf (Suc x) + x - 1) = sf (Suc x) + x" by simp
  then show "(funK \<circ> funS) (sf (Suc x) + x - 1) = x" by (simp add: funS_def funK_diag)
qed

lemma P_expr_K: "funK \<circ> opInv (funK \<circ> funS) = funP"
proof
  fix x :: nat
  let ?y = "opInv (funK \<circ> funS) x"
  show "(funK \<circ> opInv (funK \<circ> funS)) x = funP x"
  proof (cases x)
    case 0
    have "?y \<le> 0" by (rule opInv_least[OF surj_KS]) (simp add: funS_def 0)
    then show ?thesis by (simp add: funK_0 funP_def 0)
  next
    case (Suc x')
    have y: "funK (Suc ?y) = x" using opInv_right[OF surj_KS, of x] by (simp add: funS_def)
    define t where "t = funV (Suc ?y)"
    have dec: "sf t + x = Suc ?y" using funK_decomp[of "Suc ?y"] y by (simp add: t_def)
    have xt: "x \<le> t" using funK_le_V[of "Suc ?y"] y by (simp add: t_def)
    have "?y = sf t + x'" using dec Suc by simp
    then have "funK ?y = x'" using xt Suc by (simp add: funK_diag)
    then show ?thesis by (simp add: funP_def Suc)
  qed
qed

lemma P_in_GK [clos_rules]: "funP \<in> CGK" by (subst P_expr_K[symmetric]) clos_solve

text \<open>\<open>U \<equiv> I - A K P (I - K)\<close>, \<open>U(y) = V(y) + K(y)\<close>.\<close>
definition exprU :: ufun where "exprU = exprIminusF (funA \<circ> funK \<circ> funP \<circ> exprIminusF funK)"

lemma exprU_in [clos_rules]: "exprU \<in> CGK" unfolding exprU_def by clos_solve

lemma IminusK: "exprIminusF funK y = sf (funV y)"
  using funK_decomp[of y] by (simp add: exprIminusF_val funK_le)

lemma KP_sf: "funK (funP (sf t)) = t - 1"
proof (cases t)
  case 0 then show ?thesis by (simp add: funP_def funK_0 sf_at_0)
next
  case (Suc t')
  then have "funP (sf t) = sf t' + t'" using sf_Suc[of t'] by (simp add: funP_def)
  then show ?thesis using Suc by (simp add: funK_diag)
qed

lemma exprU_val: "exprU y = funV y + funK y"
proof -
  let ?t = "funV y" and ?k = "funK y"
  have dec: "sf ?t + ?k = y" by (rule funK_decomp)
  have inner: "(funA \<circ> funK \<circ> funP \<circ> exprIminusF funK) y = sf (?t - 1)"
    by (simp add: IminusK KP_sf funA_eq_sf)
  have le: "sf (?t - 1) \<le> y" using sf_mono[of "?t - 1" ?t] dec by linarith
  have cond: "(funA \<circ> funK \<circ> funP \<circ> exprIminusF funK) y \<le> y" by (simp only: inner le)
  have "exprU y = y - (funA \<circ> funK \<circ> funP \<circ> exprIminusF funK) y"
    unfolding exprU_def by (rule exprIminusF_val[of "funA \<circ> funK \<circ> funP \<circ> exprIminusF funK" y, OF cond])
  also have "\<dots> = y - sf (?t - 1)" by (simp only: inner)
  also have "\<dots> = ?t + ?k"
  proof (cases "?t = 0")
    case True
    then have "?k = 0" using funK_le_V[of y] by simp
    then show ?thesis using True dec by simp
  next
    case False
    then show ?thesis using sf_Suc_pred[of ?t] dec by simp
  qed
  finally show ?thesis .
qed

lemma exprU_sf: "exprU (sf t) = t"
  using exprU_val[of "sf t"] funV_diag[of 0 t] funK_diag[of 0 t] by simp

text \<open>\<open>Hf \<equiv> K U\<^sup>-\<^sup>1\<close>: the least \<open>y = A(t) + k\<close> with \<open>t + k = x\<close> has \<open>t = \<lceil>x/2\<rceil>\<close>, \<open>k = \<lfloor>x/2\<rfloor>\<close>.\<close>
lemma exprU_pair: "k \<le> t \<Longrightarrow> exprU (sf t + k) = t + k"
  by (simp add: exprU_val funV_diag funK_diag)

lemma surj_exprU: "surj exprU"
  by (rule surjI'[of _ "\<lambda>x. sf (x - x div 2) + x div 2"]) (subst exprU_pair, simp_all)

lemma Hf_expr_K: "funK \<circ> opInv exprU = funHf"
proof
  fix x :: nat
  let ?y = "opInv exprU x"
  let ?t = "funV ?y" and ?k = "funK ?y"
  have u: "?t + ?k = x" using opInv_right[OF surj_exprU, of x] by (simp add: exprU_val)
  have kt: "?k \<le> ?t" by (rule funK_le_V)
  have dec: "sf ?t + ?k = ?y" by (rule funK_decomp)
  have "x div 2 \<le> ?k"
  proof (rule ccontr)
    assume "\<not> x div 2 \<le> ?k"
    then have lt: "x - x div 2 < ?t" using u by linarith
    have w: "exprU (sf (x - x div 2) + x div 2) = x" by (subst exprU_pair) simp_all
    have "?y \<le> sf (x - x div 2) + x div 2" by (rule opInv_least[OF surj_exprU w])
    also have "\<dots> < sf ?t"
      using sf_aux4[OF lt] by linarith
    finally show False using dec by linarith
  qed
  then show "(funK \<circ> opInv exprU) x = funHf x" using u kt by (simp add: funHf_def)
qed

lemma Hf_in_GK [clos_rules]: "funHf \<in> CGK" by (subst Hf_expr_K[symmetric]) clos_solve

text \<open>\<open>B \<equiv> I - (I - Sq (I - Hf) U) (I - K)\<close>, \<open>B(y) = K(y) + \<lceil>V(y)/2\<rceil>\<^sup>2\<close>.\<close>
definition exprB :: ufun where
  "exprB = exprIminusF (exprIminusF (funSq \<circ> exprIminusF funHf \<circ> exprU) \<circ> exprIminusF funK)"

lemma exprB_in [clos_rules]: "exprB \<in> CGK" unfolding exprB_def by clos_solve

lemma ceil_sq_le_sf: "(t - t div 2) * (t - t div 2) \<le> sf t"
proof -
  define c where "c = t - t div 2"
  have h1: "2 * c \<le> t + 1" and h2: "c \<le> t" by (simp_all add: c_def)
  have "c * (2 * c) \<le> c * (t + 1)" using h1 by (rule mult_le_mono2)
  moreover have "c * (t + 1) \<le> t * (t + 1)" using h2 by (rule mult_le_mono1)
  moreover have "t * (t + 1) = 2 * sf t" using two_sf[of t] by (simp add: algebra_simps)
  moreover have "c * (2 * c) = 2 * (c * c)" by (simp add: algebra_simps)
  ultimately have "c * c \<le> sf t" by linarith
  then show ?thesis by (simp only: c_def)
qed

lemma exprB_val: "exprB y = funK y + (funV y - funV y div 2) * (funV y - funV y div 2)"
proof -
  let ?t = "funV y" and ?k = "funK y"
  let ?c = "?t - ?t div 2"
  have dec: "sf ?t + ?k = y" by (rule funK_decomp)
  have hf: "exprIminusF funHf ?t = ?c" by (simp add: exprIminusF_val funHf_def)
  have inner: "exprIminusF (funSq \<circ> exprIminusF funHf \<circ> exprU) (sf ?t) = sf ?t - ?c * ?c"
    using ceil_sq_le_sf[of ?t] by (simp add: exprIminusF_val exprU_sf hf funSq_def)
  have "exprB y = y - (sf ?t - ?c * ?c)"
    unfolding exprB_def using dec by (subst exprIminusF_val) (simp_all add: IminusK inner)
  then show ?thesis using ceil_sq_le_sf[of ?t] dec by linarith
qed

text \<open>\<open>E \<equiv> K B\<^sup>-\<^sup>1\<close>: if \<open>B(y) = x\<close> then \<open>x = c\<^sup>2 + K(y)\<close> with \<open>K(y) \<le> V(y) \<le> 2c\<close>, so \<open>E(x) = K(y)\<close>.\<close>
lemma surj_exprB: "surj exprB"
proof (rule surjI'[of _ "\<lambda>x. sf (2 * funRt x) + funE x"])
  fix x :: nat
  have "exprB (sf (2 * funRt x) + funE x) = funE x + funRt x * funRt x"
    using funE_bound[of x] by (simp add: exprB_val funV_diag funK_diag)
  then show "exprB (sf (2 * funRt x) + funE x) = x" using funE_decomp[of x] by simp
qed

lemma E_expr_K: "funK \<circ> opInv exprB = funE"
proof
  fix x :: nat
  let ?y = "opInv exprB x"
  let ?t = "funV ?y" and ?k = "funK ?y"
  let ?c = "?t - ?t div 2"
  have b: "?k + ?c * ?c = x" using opInv_right[OF surj_exprB, of x] by (simp add: exprB_val)
  have "?k \<le> 2 * ?c" using funK_le_V[of ?y] by linarith
  then have "funE (?c * ?c + ?k) = ?k" by (rule funE_sq_add)
  then show "(funK \<circ> opInv exprB) x = funE x" using b by (simp add: add.commute)
qed

lemma E_in_GK [clos_rules]: "funE \<in> CGK" by (subst E_expr_K[symmetric]) clos_solve

lemma GE_sub_GK: "CGE \<subseteq> CGK" by clos_subset_m

subsection \<open>\<open>K\<close> in \<open>clos \<langle>1, L, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>\<close>

lemma K_in_GL [clos_rules]: "funK \<in> CGL" by (subst K_expr_L[symmetric]) clos_solve

lemma GK_sub_GL: "CGK \<subseteq> CGL" by clos_subset_m

theorem GR_K_eq_JR: "clos (basis_GR funK) = clos basis_JR"
  using GK_sub_GE GE_sub_GK GR_E_eq_JR by blast

theorem GR_L_eq_JR: "clos (basis_GR funL) = clos basis_JR"
  using GL_sub_GE GE_sub_GK GK_sub_GL GR_E_eq_JR by blast


section \<open>The constant cannot be dropped\<close>

text \<open>In \<open>\<langle>X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close> with \<open>X(0) = 0\<close> every function fixes \<open>0\<close>: \<open>F\<^sup>+(0) = F(0)\<close>, and
  \<open>F\<^sup>-\<^sup>1(0) = 0\<close> when \<open>F(0) = 0\<close>.\<close>
lemma GR0_fix0:
  assumes X: "X 0 = 0" and F: "F \<in> clos (basis_GR0 X)"
  shows "F 0 = 0"
  using F
proof (induct rule: clos_induct)
  case (init F) then show ?case using X by (simp add: clos_defs)
next
  case (unop u F)
  then have "u = opPlusI \<or> u = opInv" by (simp add: clos_defs)
  then show ?case
  proof
    assume "u = opPlusI" then show ?thesis using unop(3) by (simp add: applyU_def opPlusI_def)
  next
    assume "u = opInv" then show ?thesis using unop(3) by (simp add: applyU_def opInv_def)
  qed
next
  case (binop b F G) then show ?case by (simp add: clos_defs applyB_def)
qed

lemma funL_0: "funL 0 = 0"
  using funL_diag[of 0 0] by (simp add: sf_at_0)

theorem GR0_not_one:
  "cst 1 \<notin> clos (basis_GR0 funE)" "cst 1 \<notin> clos (basis_GR0 funK)" "cst 1 \<notin> clos (basis_GR0 funL)"
  using GR0_fix0[of funE "cst 1"] GR0_fix0[of funK "cst 1"] GR0_fix0[of funL "cst 1"]
  by (auto simp: cst_def funK_0 funL_0)


section \<open>Assuming Robinson's theorem\<close>

text \<open>J. Robinson's theorem (1950, Sec. 4, Thm. 3) is assumed: her basis generates the set
  \<open>GR\<close> of unary general recursive functions.\<close>
locale Robinson_1950 =
  fixes GR :: "ufun set"
  assumes Robinson_1950_sec4_thm3: "clos basis_JR = GR"
begin

theorem Ext_GR: "clos (basis_GR funE) = GR" "clos (basis_GR funK) = GR" "clos (basis_GR funL) = GR"
  using GR_E_eq_JR GR_K_eq_JR GR_L_eq_JR Robinson_1950_sec4_thm3 by simp_all

theorem Ext_GR0: "clos (basis_GR0 funE) \<noteq> GR" "clos (basis_GR0 funK) \<noteq> GR" "clos (basis_GR0 funL) \<noteq> GR"
proof -
  have "cst 1 \<in> GR" using one_in_JR Robinson_1950_sec4_thm3 by simp
  then show "clos (basis_GR0 funE) \<noteq> GR" "clos (basis_GR0 funK) \<noteq> GR" "clos (basis_GR0 funL) \<noteq> GR"
    using GR0_not_one by auto
qed

end

section \<open>Remark: \<open>1\<close> and \<open>S\<close> are interchangeable\<close>

text \<open>\<open>\<langle>S, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close> generates the same closure as \<open>\<langle>1, X, F\<^sup>+, FG, F\<^sup>-\<^sup>1\<rangle>\<close>:
  \<open>S = 1\<^sup>+\<close>, and \<open>1 = S 0\<close>, where \<open>0\<close> comes from \<open>S\<close>, \<open>X\<close>, composition and inversion alone:
  \<open>0 \<equiv> K S K\<^sup>-\<^sup>1\<close>, \<open>0 \<equiv> (E S E\<^sup>-\<^sup>1)\<^sup>2\<close>, \<open>0 \<equiv> L (L S)\<^sup>-\<^sup>1 S\<close>.\<close>

definition basis_GRS :: "ufun \<Rightarrow> basis" where
  "basis_GRS X = Basis {funS, X} {opPlusI, opInv} {(\<circ>)}"

lemmas basis_GRS_sel [clos_defs] =
  basis.sel[of "{funS, X}" "{opPlusI, opInv}" "{(\<circ>)}", folded basis_GRS_def] for X

lemma S_in_GR: "funS \<in> clos (basis_GR X)"
  by (subst S_expr[symmetric]) clos_solve

lemma GRS_sub_GR: "clos (basis_GRS X) \<subseteq> clos (basis_GR X)"
  by (clos_subset_m add: S_in_GR)

lemma GR_sub_GRS:
  assumes Z: "cst 0 \<in> clos (basis_GRS X)" shows "clos (basis_GR X) \<subseteq> clos (basis_GRS X)"
proof -
  have S: "funS \<in> clos (basis_GRS X)" by clos_solve
  have "funS \<circ> cst 0 \<in> clos (basis_GRS X)" by (clos_solve add: S Z)
  then have one: "cst 1 \<in> clos (basis_GRS X)" by (simp only: one_expr)
  show ?thesis by (clos_subset_m add: one)
qed

text \<open>\<open>0 \<equiv> K S K\<^sup>-\<^sup>1\<close>: \<open>K\<^sup>-\<^sup>1(x) + 1 = A(x) + x + 1 = A(x + 1)\<close>.\<close>
lemma zero_expr_GRS_K: "funK \<circ> funS \<circ> opInv funK = cst 0"
proof
  fix x :: nat
  have "Suc (funZ x) = sf (Suc x) + 0" using sf_Suc[of x] by (simp add: funZ_sf)
  then show "(funK \<circ> funS \<circ> opInv funK) x = cst 0 x"
    using funK_diag[of 0 "Suc x"] by (simp add: Kinv_eq_Z funS_def cst_def)
qed

text \<open>\<open>0 \<equiv> (E S E\<^sup>-\<^sup>1)\<^sup>2\<close>: \<open>E S E\<^sup>-\<^sup>1\<close> maps \<open>2j\<close> to \<open>0\<close> and \<open>2j + 1\<close> to \<open>2j + 2\<close>.\<close>
lemma ESEinv_val: "(funE \<circ> funS \<circ> opInv funE) x = (if even x then 0 else x + 1)"
proof (cases "even x")
  case True
  then obtain j where x: "x = 2 * j" by (auto elim: evenE)
  have "Suc (opInv funE x) = (j + 1) * (j + 1) + 0" using x by (simp add: Einv_val algebra_simps)
  then have "funE (Suc (opInv funE x)) = 0" using funE_sq_add[of 0 "j + 1"] by simp
  then show ?thesis using True by (simp add: funS_def)
next
  case False
  then obtain j where x: "x = 2 * j + 1" by (auto elim: oddE)
  have "(x + 1) div 2 = j + 1" using x by simp
  then have "Suc (opInv funE x) = (j + 1) * (j + 1) + (2 * j + 2)" using x by (simp add: Einv_val)
  moreover have "funE ((j + 1) * (j + 1) + (2 * j + 2)) = 2 * j + 2" by (rule funE_sq_add) simp
  ultimately show ?thesis using False x by (simp add: funS_def)
qed

lemma zero_expr_GRS_E:
  "(funE \<circ> funS \<circ> opInv funE) \<circ> (funE \<circ> funS \<circ> opInv funE) = cst 0"
proof
  fix x :: nat
  show "((funE \<circ> funS \<circ> opInv funE) \<circ> (funE \<circ> funS \<circ> opInv funE)) x = cst 0 x"
    by (cases "even x") (simp_all only: comp_apply[of "funE \<circ> funS \<circ> opInv funE"] ESEinv_val,
        simp_all add: cst_def)
qed

text \<open>\<open>0 \<equiv> L (L S)\<^sup>-\<^sup>1 S\<close>: the least \<open>y\<close> with \<open>L(y + 1) = x + 1\<close> is \<open>A(x) + x\<close>, and \<open>L\<close> of it is \<open>0\<close>.\<close>
lemma surj_LS: "surj (funL \<circ> funS)"
proof (rule surjI'[of _ "\<lambda>v. sf (Suc v)"])
  fix v
  show "(funL \<circ> funS) (sf (Suc v)) = v"
    using funL_diag[of 1 "Suc v"] by (simp add: funS_def)
qed

lemma LSinv_Suc: "opInv (funL \<circ> funS) (Suc x) = sf x + x"
proof -
  have "(LEAST y. (funL \<circ> funS) y = Suc x) = sf x + x"
  proof (rule Least_equality)
    have "Suc (sf x + x) = sf (Suc x) + 0" using sf_Suc[of x] by simp
    then show "(funL \<circ> funS) (sf x + x) = Suc x"
      using funL_diag[of 0 "Suc x"] by (simp add: funS_def del: add_0_right)
  next
    fix y assume y: "(funL \<circ> funS) y = Suc x"
    let ?t = "funV (Suc y)" and ?k = "funK (Suc y)"
    have dec: "sf ?t + ?k = Suc y" by (rule funK_decomp)
    have kt: "?k \<le> ?t" by (rule funK_le_V)
    have "funL (Suc y) = ?t - ?k" using funL_diag[OF kt] dec by simp
    then have "Suc x \<le> ?t" using y by (simp add: funS_def)
    then have "sf (Suc x) \<le> sf ?t" by (rule sf_mono)
    then show "sf x + x \<le> y" using dec sf_Suc[of x] by linarith
  qed
  then show ?thesis by (simp add: opInv_surj[OF surj_LS])
qed

lemma zero_expr_GRS_L: "funL \<circ> opInv (funL \<circ> funS) \<circ> funS = cst 0"
proof
  fix x :: nat
  show "(funL \<circ> opInv (funL \<circ> funS) \<circ> funS) x = cst 0 x"
    by (simp add: funS_def LSinv_Suc cst_def funL_diag)
qed

theorem GRS_eq_GR:
  "clos (basis_GRS funE) = clos (basis_GR funE)"
  "clos (basis_GRS funK) = clos (basis_GR funK)"
  "clos (basis_GRS funL) = clos (basis_GR funL)"
proof -
  have "(funE \<circ> funS \<circ> opInv funE) \<circ> (funE \<circ> funS \<circ> opInv funE) \<in> clos (basis_GRS funE)"
    by clos_solve
  then have "cst 0 \<in> clos (basis_GRS funE)" by (simp only: zero_expr_GRS_E)
  then show "clos (basis_GRS funE) = clos (basis_GR funE)"
    using GRS_sub_GR GR_sub_GRS by blast
next
  have "funK \<circ> funS \<circ> opInv funK \<in> clos (basis_GRS funK)" by clos_solve
  then have "cst 0 \<in> clos (basis_GRS funK)" by (simp only: zero_expr_GRS_K)
  then show "clos (basis_GRS funK) = clos (basis_GR funK)"
    using GRS_sub_GR GR_sub_GRS by blast
next
  have "funL \<circ> opInv (funL \<circ> funS) \<circ> funS \<in> clos (basis_GRS funL)" by clos_solve
  then have "cst 0 \<in> clos (basis_GRS funL)" by (simp only: zero_expr_GRS_L)
  then show "clos (basis_GRS funL) = clos (basis_GR funL)"
    using GRS_sub_GR GR_sub_GRS by blast
qed

context Robinson_1950
begin

theorem Ext_GRS: "clos (basis_GRS funE) = GR" "clos (basis_GRS funK) = GR" "clos (basis_GRS funL) = GR"
  using GRS_eq_GR Ext_GR by simp_all

end

end
