(*  Title:   UPRF_Sec6_Thm68.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Section 6, Theorem 6.8: the bases \<langle>1, K, F\<^sup>+, FG, F\<^sup>\<box>\<rangle> and \<langle>1, L, F\<^sup>+, FG, F\<^sup>\<box>\<rangle>
    are suitable (K and L are the inverses of the Cantor pairing function).
*)

theory UPRF_Sec6_Thm68
  imports UPRF_Sec6_Thm67
begin

section \<open>Theorem 6.8: the bases with \<open>K\<close> and \<open>L\<close>\<close>

subsection \<open>The basis \<open>\<F>' = \<langle>\<overline>1, K, F\<^sup>+, FG, F\<^sup>\<box>\<rangle>\<close>\<close>

definition basis_6K :: basis where
  "basis_6K = Basis {cst 1, funK} {opPlusI, opBox} {(\<circ>)}"

abbreviation C6K :: "ufun set" where "C6K \<equiv> clos basis_6K"

lemma C6K_one: "cst 1 \<in> C6K" and C6K_K: "funK \<in> C6K"
  by (rule clos_init, simp add: basis_6K_def)+

lemma C6K_plusI: "F \<in> C6K \<Longrightarrow> opPlusI F \<in> C6K"
  and C6K_box: "F \<in> C6K \<Longrightarrow> opBox F \<in> C6K"
  using clos_unop[of opPlusI basis_6K F] clos_unop[of opBox basis_6K F] by (simp_all add: basis_6K_def)

lemma C6K_comp: "F \<in> C6K \<Longrightarrow> G \<in> C6K \<Longrightarrow> F \<circ> G \<in> C6K"
  using clos_binop[of "(\<circ>)" basis_6K F G] by (simp add: basis_6K_def)

lemmas C6K_intros = C6K_one C6K_K C6K_plusI C6K_box C6K_comp

text \<open>Auxiliary functions of the proof (following p. 664 of Robinson [16]).\<close>
definition funY :: ufun where "funY x = 2 * x - funRt x"          \<comment> \<open>\<open>Y(x) = 2x - \<lfloor>\<surd>x\<rfloor>\<close>\<close>
definition funZ :: ufun where "funZ x = x * (x + 3) div 2"        \<comment> \<open>\<open>Z(x) = x(x+3)/2\<close>\<close>

lemma funZ_sf: "funZ x = sf x + x"
proof -
  have "x * (x + 3) = 2 * (sf x + x)" using two_sf[of x] by (simp add: algebra_simps)
  then show ?thesis by (simp add: funZ_def)
qed

text \<open>\<open>K(1) = 0\<close>, \<open>K(0) = 0\<close>.\<close>
lemma funK_0: "funK 0 = 0"
proof -
  have "funK (sf 0 + 0) = 0" by (rule funK_diag) simp
  then show ?thesis by (simp only: sf_at_0 add_0_right)
qed

lemma funK_1: "funK 1 = 0"
proof -
  have "funK (sf 1 + 0) = 0" by (rule funK_diag) simp
  then show ?thesis by (simp only: sf_at_1 add_0_right)
qed

lemma funK_Suc_0 [simp]: "funK (Suc 0) = 0"
  using funK_1 by (simp only: One_nat_def)

lemma zero_expr_K: "funK \<circ> cst 1 = cst 0"
  by (rule ext) (simp add: cst_def funK_1)

text \<open>\<open>Z \<equiv> (S S K\<^sup>+)\<^sup>\<box>\<close>.\<close>
lemma Z_expr: "opBox (funS \<circ> funS \<circ> opPlusI funK) = funZ"
proof
  fix n show "opBox (funS \<circ> funS \<circ> opPlusI funK) n = funZ n"
  proof (induct n)
    case 0 then show ?case by (simp add: funZ_def)
  next
    case (Suc n)
    have "funK (sf n + n) = n" by (rule funK_diag) simp
    then show ?case using Suc sf_Suc[of n] by (simp add: funZ_sf funS_def opPlusI_def)
  qed
qed

text \<open>Robinson's formula: \<open>K((\<alpha> + \<beta>)(\<alpha> + \<beta> + 3)/2 + 2\<alpha> + 3) = \<alpha> - \<beta>\<close> if \<open>\<alpha> \<ge> \<beta>\<close>.\<close>
lemma robinson_diff_K:
  assumes "\<beta> \<le> \<alpha>"
  shows "funK (funZ (\<alpha> + \<beta>) + 2 * \<alpha> + 3) = \<alpha> - \<beta>"
proof -
  let ?t = "\<alpha> + \<beta>"
  have "sf (Suc (Suc ?t)) = sf ?t + 2 * ?t + 3" using sf_Suc[of ?t] sf_Suc[of "Suc ?t"] by simp
  then have "funZ ?t + 2 * \<alpha> + 3 = sf (Suc (Suc ?t)) + (\<alpha> - \<beta>)"
    using assms by (simp add: funZ_sf)
  moreover have "\<alpha> - \<beta> \<le> Suc (Suc ?t)" by simp
  ultimately show ?thesis by (simp add: funK_diag)
qed

text \<open>\<open>I - F \<equiv> K S S S ((Z F\<^sup>+)\<^sup>+)\<^sup>+\<close> (if \<open>x \<ge> F(x)\<close>) and
  \<open>D - F \<equiv> K S S S ((((Z (F\<^sup>+)\<^sup>+)\<^sup>+)\<^sup>+)\<^sup>+)\<^sup>+\<close> (if \<open>2x \<ge> F(x)\<close>).\<close>
definition exprIminusF :: uop where
  "exprIminusF F = funK \<circ> funS \<circ> funS \<circ> funS \<circ> opPlusI (opPlusI (funZ \<circ> opPlusI F))"

definition exprDminusF :: uop where
  "exprDminusF F = funK \<circ> funS \<circ> funS \<circ> funS \<circ>
     opPlusI (opPlusI (opPlusI (opPlusI (funZ \<circ> opPlusI (opPlusI F)))))"

lemma exprIminusF_val:
  assumes "F x \<le> x" shows "exprIminusF F x = x - F x"
proof -
  have e: "exprIminusF F x = funK (Suc (Suc (Suc (funZ (F x + x) + x + x))))"
    by (simp only: exprIminusF_def comp_apply opPlusI_def funS_def)
  have a1: "F x + x = x + F x" by (rule add.commute)
  have a2: "Suc (Suc (Suc (funZ (x + F x) + x + x))) = funZ (x + F x) + 2 * x + 3" by arith
  show ?thesis unfolding e a1 a2 using assms by (rule robinson_diff_K)
qed

lemma exprDminusF_val:
  assumes "F x \<le> 2 * x" shows "exprDminusF F x = 2 * x - F x"
proof -
  have e: "exprDminusF F x = funK (Suc (Suc (Suc (funZ (F x + x + x) + x + x + x + x))))"
    by (simp only: exprDminusF_def comp_apply opPlusI_def funS_def)
  have a1: "F x + x + x = 2 * x + F x" by arith
  have a2: "Suc (Suc (Suc (funZ (2 * x + F x) + x + x + x + x))) = funZ (2 * x + F x) + 2 * (2 * x) + 3"
    by arith
  show ?thesis unfolding e a1 a2 using assms by (rule robinson_diff_K)
qed

text \<open>\<open>Y \<equiv> ((Sgn K)\<^sup>+ S)\<^sup>\<box>\<close>, where \<open>Y(x) = 2x - \<lfloor>\<surd>x\<rfloor>\<close>.  The key fact is that
  \<open>Y(n) + 1\<close> is a triangular number iff \<open>n + 1\<close> is a square.\<close>
lemma Y_step_square:
  assumes "Suc (funRt n) * Suc (funRt n) = Suc n"
  shows "funK (Suc (funY n)) = 0"
proof -
  let ?r = "funRt n"
  have "Suc (funY n) = sf (Suc (2 * ?r))"
  proof -
    have "2 * sf (Suc (2 * ?r)) = 2 * (Suc (funY n))"
      using assms two_sf[of "Suc (2 * ?r)"] by (simp add: funY_def algebra_simps)
    then show ?thesis by simp
  qed
  then show ?thesis using funK_diag[of 0 "Suc (2 * ?r)"] by simp
qed

lemma Y_step_nonsquare:
  assumes "Suc (funRt n) * Suc (funRt n) \<noteq> Suc n"
  shows "funK (Suc (funY n)) \<noteq> 0"
proof
  let ?r = "funRt n"
  assume "funK (Suc (funY n)) = 0"
  then obtain t where t: "Suc (funY n) = sf t" using funK_zero_iff by blast
  have lo: "?r * ?r \<le> n" and hi: "n < Suc ?r * Suc ?r" by (rule funRt_sq_le, rule funRt_sq_gt)
  have hi': "Suc n < Suc ?r * Suc ?r" using hi assms by linarith
  \<comment> \<open>\<open>n \<ne> 0\<close>, hence \<open>r \<ge> 1\<close>\<close>
  have "?r \<noteq> 0"
  proof
    assume "?r = 0"
    with hi' show False by simp
  qed
  then obtain s where s: "?r = Suc s" by (cases ?r) auto
  have lo_s: "Suc s * Suc s \<le> n" and hi_s: "Suc n < Suc (Suc s) * Suc (Suc s)" using lo hi' s by simp_all
  have r_le: "?r \<le> 2 * n" using lo_s s by (simp add: algebra_simps)
  have tt: "t * t + t = 2 * Suc (funY n)" using t two_sf[of t] by simp
  have Y2: "2 * Suc (funY n) + 2 * Suc s = 4 * n + 2" using r_le s by (simp add: funY_def algebra_simps)
  \<comment> \<open>\<open>sf(2s+1) < Y(n) + 1 < sf(2s+3)\<close>, so \<open>t = 2s+2\<close>\<close>
  have "sf (Suc (2 * s)) < sf t"
  proof -
    have "2 * sf (Suc (2 * s)) < 2 * Suc (funY n)"
      using Y2 lo_s two_sf[of "Suc (2 * s)"] by (simp add: algebra_simps)
    then show ?thesis using t by simp
  qed
  moreover have "sf t < sf (Suc (Suc (Suc (2 * s))))"
  proof -
    have "2 * Suc (funY n) < 2 * sf (Suc (Suc (Suc (2 * s))))"
      using Y2 hi_s two_sf[of "Suc (Suc (Suc (2 * s)))"] by (simp add: algebra_simps)
    then show ?thesis using t by simp
  qed
  ultimately have "Suc (2 * s) < t" "t < Suc (Suc (Suc (2 * s)))" by (auto dest: sf_less_sfD)
  then have "t = Suc (Suc (2 * s))" by simp
  \<comment> \<open>but then \<open>4n = 4(s\<^sup>2 + 3s + 1) + 2\<close>, impossible\<close>
  with tt Y2 have "4 * n = 4 * (s * s + 3 * s + 1) + 2" by (simp add: algebra_simps)
  moreover obtain q where "q = s * s + 3 * s + 1" by simp
  ultimately have "4 * n = 4 * q + 2" by simp
  then show False by presburger
qed

lemma Y_step: "opPlusI (funSgn \<circ> funK) (funS (funY n)) = funY (Suc n)"
proof -
  let ?r = "funRt n"
  have r_le: "?r \<le> n" using funRt_sq_le[of n] by (metis le_square order.trans)
  show ?thesis
  proof (cases "Suc ?r * Suc ?r = Suc n")
    case True
    then have rt: "funRt (Suc n) = Suc ?r" using funRt_Suc[of n] by simp
    show ?thesis
      using Y_step_square[OF True] r_le rt by (simp add: opPlusI_def funS_def funSgn_def funY_def)
  next
    case False
    then have rt: "funRt (Suc n) = ?r" using funRt_Suc[of n] by simp
    show ?thesis
      using Y_step_nonsquare[OF False] r_le rt by (simp add: opPlusI_def funS_def funSgn_def funY_def)
  qed
qed

lemma Y_expr: "opBox (opPlusI (funSgn \<circ> funK) \<circ> funS) = funY"
proof
  fix n show "opBox (opPlusI (funSgn \<circ> funK) \<circ> funS) n = funY n"
  proof (induct n)
    case 0 then show ?case by (simp add: funY_def)
  next
    case (Suc n) then show ?case by (simp only: opBox_Suc) (subst comp_apply, rule Y_step)
  qed
qed

text \<open>\<open>Rt \<equiv> D - Y\<close>, \<open>Sq \<equiv> (((\<overline>1\<^sup>+)\<^sup>+ Rt)\<^sup>+)\<^sup>\<box>\<close>, \<open>E \<equiv> I - Sq Rt\<close>.\<close>
lemma Rt_expr_K: "exprDminusF funY = funRt"
proof
  fix x
  have "funRt x \<le> x" using funRt_sq_le[of x] by (metis le_square order.trans)
  then show "exprDminusF funY x = funRt x" by (simp add: exprDminusF_val funY_def)
qed

lemma Sq_expr_K: "opBox (opPlusI (opPlusI (opPlusI (cst 1)) \<circ> funRt)) = funSq"
proof
  fix n show "opBox (opPlusI (opPlusI (opPlusI (cst 1)) \<circ> funRt)) n = funSq n"
    by (induct n) (simp_all add: opPlusI_def cst_def funSq_def algebra_simps)
qed

lemma E_expr_K: "exprIminusF (funSq \<circ> funRt) = funE"
proof
  fix x
  have "funRt x * funRt x \<le> x" by (rule funRt_sq_le)
  then show "exprIminusF (funSq \<circ> funRt) x = funE x" by (simp add: exprIminusF_val funSq_def funE_alt)
qed

lemma S_in_K: "funS \<in> C6K" by (metis S_expr C6K_intros)
lemma Sgn_in_K: "funSgn \<in> C6K" by (metis Sgn_expr C6K_intros)
lemma zero_in_K: "cst 0 \<in> C6K" by (metis zero_expr_K C6K_intros)
lemma D_in_K: "funD \<in> C6K" by (metis D_expr zero_in_K C6K_intros)
lemma Y_in_K: "funY \<in> C6K" by (metis Y_expr Sgn_in_K S_in_K C6K_intros)
lemma Z_in_K: "funZ \<in> C6K" by (metis Z_expr S_in_K C6K_intros)

lemma exprIminusF_in_K: "F \<in> C6K \<Longrightarrow> exprIminusF F \<in> C6K"
  unfolding exprIminusF_def by (intro C6K_intros S_in_K Z_in_K)

lemma exprDminusF_in_K: "F \<in> C6K \<Longrightarrow> exprDminusF F \<in> C6K"
  unfolding exprDminusF_def by (intro C6K_intros S_in_K Z_in_K)

lemma Rt_in_K: "funRt \<in> C6K" by (metis Rt_expr_K exprDminusF_in_K Y_in_K)
lemma Sq_in_K: "funSq \<in> C6K" by (metis Sq_expr_K Rt_in_K C6K_intros)
lemma E_in_K: "funE \<in> C6K" by (metis E_expr_K exprIminusF_in_K Sq_in_K Rt_in_K C6K_intros)

theorem Theorem_6_8_K: "suitable basis_6K"
proof (rule suitable_by_simulation[OF Theorem_6_7])
  show "inits basis_6 \<subseteq> C6K" using C6K_one E_in_K by (simp add: basis_6_def)
  show "applyU u F \<in> C6K" if "u \<in> unops basis_6" "F \<in> C6K" for u F
    using that C6K_plusI C6K_box by (auto simp: basis_6_def applyU_def)
  show "applyB b F G \<in> C6K" if "b \<in> binops basis_6" "F \<in> C6K" "G \<in> C6K" for b F G
    using that C6K_comp[of F G] by (simp add: basis_6_def applyB_def comp_def)
  show "C6K \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_6K_def applyU_def applyB_def cst_PR funK_PR
             intro: opPlusI_PR opBox_PR comp_PR pr_comp1_1)
qed

subsection \<open>The basis \<open>\<F>'' = \<langle>\<overline>1, L, F\<^sup>+, FG, F\<^sup>\<box>\<rangle>\<close>\<close>

definition basis_6L :: basis where
  "basis_6L = Basis {cst 1, funL} {opPlusI, opBox} {(\<circ>)}"

abbreviation C6L :: "ufun set" where "C6L \<equiv> clos basis_6L"

lemma C6L_one: "cst 1 \<in> C6L" and C6L_L: "funL \<in> C6L"
  by (rule clos_init, simp add: basis_6L_def)+

lemma C6L_plusI: "F \<in> C6L \<Longrightarrow> opPlusI F \<in> C6L"
  and C6L_box: "F \<in> C6L \<Longrightarrow> opBox F \<in> C6L"
  using clos_unop[of opPlusI basis_6L F] clos_unop[of opBox basis_6L F] by (simp_all add: basis_6L_def)

lemma C6L_comp: "F \<in> C6L \<Longrightarrow> G \<in> C6L \<Longrightarrow> F \<circ> G \<in> C6L"
  using clos_binop[of "(\<circ>)" basis_6L F G] by (simp add: basis_6L_def)

lemmas C6L_intros = C6L_one C6L_L C6L_plusI C6L_box C6L_comp

text \<open>\<open>K \<equiv> L \<overline>1\<^sup>+ ((\<overline>1\<^sup>+)\<^sup>+ L)\<^sup>+\<close>, i.e. \<open>K(x) = L(x + 2L(x) + 2)\<close> (Robinson [16, p. 664]).\<close>
lemma K_expr_L: "funL \<circ> opPlusI (cst 1) \<circ> opPlusI (opPlusI (opPlusI (cst 1)) \<circ> funL) = funK"
proof
  fix x
  let ?t = "c_sum x" and ?k = "funK x"
  have x: "x = sf ?t + ?k" using sf_c_sum_plus_c_fst[of x] by (simp add: funK_eq_c_fst)
  have k: "?k \<le> ?t" using c_fst_le_c_sum[of x] by (simp add: funK_eq_c_fst)
  have Lx: "funL x = ?t - ?k" using funL_diag[OF k] x by simp
  have "x + 2 * funL x + 2 = sf (Suc ?t) + (?t - ?k + 1)"
    using k Lx sf_Suc[of ?t] x by simp
  then have "funL (x + 2 * funL x + 2) = Suc ?t - (?t - ?k + 1)"
    using funL_diag[of "?t - ?k + 1" "Suc ?t"] by simp
  also have "\<dots> = ?k" using k by simp
  finally have L: "funL (x + 2 * funL x + 2) = funK x" .
  have "(funL \<circ> opPlusI (cst 1) \<circ> opPlusI (opPlusI (opPlusI (cst 1)) \<circ> funL)) x
          = funL (x + 2 * funL x + 2)"
    by (simp only: comp_apply opPlusI_def cst_def) (rule arg_cong[where f = funL], arith)
  then show "(funL \<circ> opPlusI (cst 1) \<circ> opPlusI (opPlusI (opPlusI (cst 1)) \<circ> funL)) x = funK x"
    unfolding L .
qed

lemma K_in_L: "funK \<in> C6L"
  by (metis K_expr_L C6L_intros)

theorem Theorem_6_8_L: "suitable basis_6L"
proof (rule suitable_by_simulation[OF Theorem_6_8_K])
  show "inits basis_6K \<subseteq> C6L" using C6L_one K_in_L by (simp add: basis_6K_def)
  show "applyU u F \<in> C6L" if "u \<in> unops basis_6K" "F \<in> C6L" for u F
    using that C6L_plusI C6L_box by (auto simp: basis_6K_def applyU_def)
  show "applyB b F G \<in> C6L" if "b \<in> binops basis_6K" "F \<in> C6L" "G \<in> C6L" for b F G
    using that C6L_comp[of F G] by (simp add: basis_6K_def applyB_def comp_def)
  show "C6L \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_6L_def applyU_def applyB_def cst_PR funL_PR
             intro: opPlusI_PR opBox_PR comp_PR pr_comp1_1)
qed

text \<open>Theorem 6.8.\<close>
theorem Theorem_6_8: "suitable basis_6K" "suitable basis_6L"
  by (rule Theorem_6_8_K, rule Theorem_6_8_L)

end
