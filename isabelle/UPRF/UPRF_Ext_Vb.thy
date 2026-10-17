(*  Title:   UPRF_Ext_Vb.thy

    Removing the constant 1 from the basis of Theorem 6.7 by shifting the unary
    operator: for every fixed b \<ge> 1,

       \<langle>E, F\<^sup>+\<^sup>b, FG, F\<^sup>\<box>\<rangle>   with   F\<^sup>+\<^sup>b(x) = F(x) + x + b

    is a suitable basis, whereas for b = 0 (the basis of Theorem 6.7 without 1) it is not.

    The construction below works uniformly for every b \<ge> 1:
      \<overline>0 \<equiv> E\<^sup>\<box>,  A \<equiv> \<overline>0\<^sup>+\<^sup>b  (A(x) = x + b),  C \<equiv> E A\<^sup>b\<^sup>-\<^sup>1 \<overline>0  (the constant b - 1),
      B \<equiv> C\<^sup>+\<^sup>b  (B(x) = x + 2b - 1),  T \<equiv> B\<^sup>2\<^sup>b\<^sup>-\<^sup>2 A A  (T(x) = x + 4b\<^sup>2 - 4b + 2),
      G \<equiv> (A\<^sup>3 (E T)\<^sup>+\<^sup>b)\<^sup>\<box>  (G(n) = n\<^sup>2 + 4bn),
      P \<equiv> E A\<^sup>4\<^sup>b\<^sup>+\<^sup>1 ((G\<^sup>+\<^sup>b)\<^sup>+\<^sup>b)\<^sup>+\<^sup>b  (P(n) = n - 1 for n \<ge> 1),
      S \<equiv> P\<^sup>b\<^sup>-\<^sup>1 A,   \<overline>1 \<equiv> S \<overline>0,   F\<^sup>+ \<equiv> P\<^sup>b F\<^sup>+\<^sup>b.
    Here A\<^sup>k etc. are powers under composition (finitely many compositions).
*)

theory UPRF_Ext_Vb
  imports UPRF_Ext_a
begin

section \<open>The operator \<open>F(x) + x + b\<close>\<close>

definition opPlusIb :: "nat \<Rightarrow> uop" where "opPlusIb b F x = F x + x + b"

declare opPlusIb_def [eval_simps]

lemma opPlusIb_PR: "F \<in> PrimNN \<Longrightarrow> opPlusIb b F \<in> PrimNN"
  unfolding opPlusIb_def by prec

lemma opPlusIb_0: "opPlusIb 0 = opPlusI"
  by (intro ext) (simp add: opPlusIb_def opPlusI_def)

text \<open>\<open>\<langle>E, F\<^sup>+\<^sup>b, FG, F\<^sup>\<box>\<rangle>\<close>.\<close>
definition basis_Vb :: "nat \<Rightarrow> basis" where
  "basis_Vb b = Basis {funE} {opPlusIb b, opBox} {(\<circ>)}"

subsection \<open>Closure rules\<close>

lemmas basis_Vb_sel [clos_defs] =
  basis.sel[of "{funE}" "{opPlusIb b, opBox}" "{(\<circ>)}", folded basis_Vb_def] for b

lemma clos_plusIb_rule [clos_rules]:
  "F \<in> clos B \<Longrightarrow> opPlusIb b \<in> unops B \<Longrightarrow> opPlusIb b F \<in> clos B"
  using clos_unop[of "opPlusIb b" B F] by simp

declare opPlusIb_PR [prim_intros]

lemma Cb_E: "funE \<in> clos (basis_Vb b)" by clos_solve
lemma Cb_Vb: "F \<in> clos (basis_Vb b) \<Longrightarrow> opPlusIb b F \<in> clos (basis_Vb b)"
  and Cb_box: "F \<in> clos (basis_Vb b) \<Longrightarrow> opBox F \<in> clos (basis_Vb b)" by clos_solve+
lemma Cb_comp: "F \<in> clos (basis_Vb b) \<Longrightarrow> G \<in> clos (basis_Vb b) \<Longrightarrow> F \<circ> G \<in> clos (basis_Vb b)"
  by clos_solve
lemma Cb_powcomp: "F \<in> clos (basis_Vb b) \<Longrightarrow> G \<in> clos (basis_Vb b) \<Longrightarrow> (F ^^ k) \<circ> G \<in> clos (basis_Vb b)"
  by (rule clos_powcomp) (simp_all add: clos_defs)

lemmas Cb_intros = Cb_E Cb_Vb Cb_box Cb_comp Cb_powcomp

subsection \<open>The construction\<close>

definition zeroB :: ufun where "zeroB = opBox funE"
definition funAb :: "nat \<Rightarrow> ufun" where "funAb b = opPlusIb b zeroB"
definition constBm1 :: "nat \<Rightarrow> ufun" where "constBm1 b = funE \<circ> ((funAb b ^^ (b - 1)) \<circ> zeroB)"
definition funBb :: "nat \<Rightarrow> ufun" where "funBb b = opPlusIb b (constBm1 b)"
definition funTb :: "nat \<Rightarrow> ufun" where "funTb b = (funBb b ^^ (2 * b - 2)) \<circ> (funAb b \<circ> funAb b)"
definition funHb :: "nat \<Rightarrow> ufun" where "funHb b = (funAb b ^^ 3) \<circ> opPlusIb b (funE \<circ> funTb b)"
definition funGb :: "nat \<Rightarrow> ufun" where "funGb b = opBox (funHb b)"
definition funPb :: "nat \<Rightarrow> ufun" where
  "funPb b = funE \<circ> ((funAb b ^^ (4 * b + 1)) \<circ> opPlusIb b (opPlusIb b (opPlusIb b (funGb b))))"
definition funSb :: "nat \<Rightarrow> ufun" where "funSb b = (funPb b ^^ (b - 1)) \<circ> funAb b"
definition exprPlusIb :: "nat \<Rightarrow> uop" where "exprPlusIb b F = (funPb b ^^ b) \<circ> opPlusIb b F"

lemma zeroB_val: "zeroB x = 0"
  unfolding zeroB_def by (induct x) simp_all

lemma funAb_val: "funAb b x = x + b"
  by (simp add: funAb_def opPlusIb_def zeroB_val)

lemma constBm1_val: "constBm1 b x = b - 1"
proof -
  have "(b - 1) * b = (b - 1) * (b - 1) + (b - 1)" by (cases b) (simp_all add: algebra_simps)
  then have "funE ((b - 1) * b) = b - 1" by (simp add: funE_sq_add)
  then show ?thesis by (simp add: constBm1_def zeroB_val shift_pow[OF funAb_val])
qed

lemma funBb_val: "funBb b x = x + (b - 1 + b)"
  by (simp add: funBb_def opPlusIb_def constBm1_val)

text \<open>With \<open>b = c + 1\<close>: \<open>T(x) = x + d\<close> where \<open>d = 4c\<^sup>2 + 4c + 2 = 4b\<^sup>2 - 4b + 2\<close>.\<close>
lemma funTb_val: "funTb (Suc c) x = x + (4 * c * c + 4 * c + 2)"
proof -
  have "funTb (Suc c) x = x + 2 * Suc c + (2 * c) * (2 * c + 1)"
    by (simp add: funTb_def funAb_val shift_pow[OF funBb_val] algebra_simps)
  then show ?thesis by (simp add: algebra_simps)
qed

lemma funHb_val: "funHb b y = funE (funTb b y) + y + 4 * b"
  by (simp add: funHb_def opPlusIb_def shift_pow[OF funAb_val] algebra_simps)

lemma funGb_val: "funGb (Suc c) n = n * n + 4 * Suc c * n"
proof (induct n)
  case 0 then show ?case by (simp add: funGb_def)
next
  case (Suc n)
  let ?b = "Suc c"
  have e: "funE (funTb ?b (n * n + 4 * ?b * n)) = 2 * n + 1"
  proof -
    have "funTb ?b (n * n + 4 * ?b * n) = (n + 2 * c + 1) * (n + 2 * c + 1) + (2 * n + 1)"
      by (simp add: funTb_val algebra_simps)
    then show ?thesis by (simp add: funE_sq_add)
  qed
  have "funGb ?b (Suc n) = funHb ?b (funGb ?b n)" by (simp add: funGb_def)
  also have "\<dots> = (2 * n + 1) + (n * n + 4 * ?b * n) + 4 * ?b" by (simp only: funHb_val Suc e)
  also have "\<dots> = Suc n * Suc n + 4 * ?b * Suc n" by (simp add: algebra_simps)
  finally show ?case .
qed

text \<open>The predecessor: \<open>P(n) = E((n + 2b + 1)\<^sup>2 + n - 1)\<close>.\<close>
lemma funPb_Suc: "funPb (Suc c) (Suc k) = k"
proof -
  let ?b = "Suc c"
  have "funPb ?b (Suc k) = funE (funGb ?b (Suc k) + 3 * Suc k + 3 * ?b + (4 * ?b + 1) * ?b)"
    by (simp add: funPb_def opPlusIb_def shift_pow[OF funAb_val] algebra_simps)
  also have "funGb ?b (Suc k) + 3 * Suc k + 3 * ?b + (4 * ?b + 1) * ?b
               = (k + 2 * ?b + 2) * (k + 2 * ?b + 2) + k"
    by (simp add: funGb_val algebra_simps)
  also have "funE \<dots> = k" by (rule funE_sq_add) simp
  finally show ?thesis .
qed

lemma funSb_val: "1 \<le> b \<Longrightarrow> funSb b x = Suc x"
proof -
  assume "1 \<le> b"
  then obtain c where b: "b = Suc c" by (cases b) auto
  have "funSb (Suc c) x = (funPb (Suc c) ^^ c) (Suc x + c)" by (simp add: funSb_def funAb_val)
  also have "\<dots> = Suc x" by (rule pred_pow[of "funPb (Suc c)", OF funPb_Suc])
  finally show ?thesis using b by simp
qed

lemma exprPlusIb_val: "1 \<le> b \<Longrightarrow> exprPlusIb b F x = opPlusI F x"
proof -
  assume "1 \<le> b"
  then obtain c where b: "b = Suc c" by (cases b) auto
  have "exprPlusIb b F x = (funPb b ^^ b) ((F x + x) + b)" by (simp add: exprPlusIb_def opPlusIb_def)
  also have "\<dots> = F x + x" using b by (simp only: pred_pow funPb_Suc)
  finally show ?thesis by (simp add: opPlusI_def)
qed

subsection \<open>Membership in the closure\<close>

lemma zeroB_in: "zeroB \<in> clos (basis_Vb b)" unfolding zeroB_def by (intro Cb_intros)
lemma funAb_in: "funAb b \<in> clos (basis_Vb b)" unfolding funAb_def by (intro Cb_intros zeroB_in)
lemma constBm1_in: "constBm1 b \<in> clos (basis_Vb b)"
  unfolding constBm1_def by (intro Cb_intros zeroB_in funAb_in)
lemma funBb_in: "funBb b \<in> clos (basis_Vb b)" unfolding funBb_def by (intro Cb_intros constBm1_in)
lemma funTb_in: "funTb b \<in> clos (basis_Vb b)" unfolding funTb_def by (intro Cb_intros funBb_in funAb_in)
lemma funHb_in: "funHb b \<in> clos (basis_Vb b)" unfolding funHb_def by (intro Cb_intros funAb_in funTb_in)
lemma funGb_in: "funGb b \<in> clos (basis_Vb b)" unfolding funGb_def by (intro Cb_intros funHb_in)
lemma funPb_in: "funPb b \<in> clos (basis_Vb b)" unfolding funPb_def by (intro Cb_intros funAb_in funGb_in)
lemma funSb_in: "funSb b \<in> clos (basis_Vb b)" unfolding funSb_def by (intro Cb_intros funPb_in funAb_in)
lemma exprPlusIb_in: "F \<in> clos (basis_Vb b) \<Longrightarrow> exprPlusIb b F \<in> clos (basis_Vb b)"
  unfolding exprPlusIb_def by (intro Cb_intros funPb_in)

subsection \<open>Suitability for every \<open>b \<ge> 1\<close>\<close>

theorem Ext_Vb:
  assumes "1 \<le> b" shows "suitable (basis_Vb b)"
proof -
  let ?C = "clos (basis_Vb b)"
  have one: "funSb b \<circ> zeroB = cst 1"
    by (rule ext) (simp add: funSb_val[OF assms] zeroB_val cst_def)
  have plusI: "exprPlusIb b F = opPlusI F" for F
    by (rule ext) (simp add: exprPlusIb_val[OF assms])
  have one_in: "cst 1 \<in> ?C" unfolding one[symmetric] by (intro Cb_comp funSb_in zeroB_in)
  have plusI_in: "F \<in> ?C \<Longrightarrow> opPlusI F \<in> ?C" for F using exprPlusIb_in[of F b] by (simp add: plusI)
  show ?thesis by (simulate S: Theorem_6_7 add: one_in plusI_in)
qed

subsection \<open>\<open>b = 0\<close>: the constant \<open>1\<close> cannot be dropped\<close>

text \<open>Every function generated by \<open>\<langle>E, F\<^sup>+, FG, F\<^sup>\<box>\<rangle>\<close> fixes \<open>0\<close>, so \<open>\<overline>1\<close> is not generated.\<close>
lemma Vb0_fixes_zero: "F \<in> clos (basis_Vb 0) \<Longrightarrow> F 0 = 0"
proof (induct rule: clos_induct)
  case (init F) then show ?case by (simp add: basis_Vb_def)
next
  case (unop u F) then show ?case by (auto simp: basis_Vb_def applyU_def opPlusIb_def)
next
  case (binop c F G) then show ?case by (simp add: basis_Vb_def applyB_def)
qed

theorem Ext_Vb_0: "\<not> suitable (basis_Vb 0)"
proof
  assume "suitable (basis_Vb 0)"
  then have "cst 1 \<in> clos (basis_Vb 0)" using cst_PR[of 1] by (simp add: suitable_def)
  then show False using Vb0_fixes_zero[of "cst 1"] by (simp add: cst_def)
qed

text \<open>Summary: \<open>\<langle>E, F \<mapsto> F + I + \<overline>b, FG, F\<^sup>\<box>\<rangle>\<close> is suitable iff \<open>b \<ge> 1\<close>.\<close>
corollary Ext_Vb_iff: "suitable (basis_Vb b) \<longleftrightarrow> 1 \<le> b"
  using Ext_Vb Ext_Vb_0 by (cases b) auto

end
