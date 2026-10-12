(*  Title:   UPRF_Sec6.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Section 6: Iteration and unary operator.

    Convention: for a function or operator defined in the paper by a formula
    "X \<equiv> expression", exprX is the expression (built only with the operators
    of the basis) and a lemma X_expr / exprX_val states that it computes X.
*)

theory UPRF_Sec6
  imports UPRF_Sec3_Preliminaries
begin

section \<open>Section 6: Iteration and unary operator\<close>

text \<open>The unary operator \<open>F\<^sup>+(x) = F(x) + x\<close>.\<close>
definition opPlusI :: uop where "opPlusI F x = F x + x"

lemma opPlusI_PR: "F \<in> PrimNN \<Longrightarrow> opPlusI F \<in> PrimNN"
  unfolding opPlusI_def by prec

text \<open>\<open>\<F> = \<langle>\<overline>1, E, F\<^sup>+, FG, F\<^sup>\<box>\<rangle>\<close>.\<close>
definition basis_6 :: basis where
  "basis_6 = Basis {cst 1, funE} {opPlusI, opBox} {(\<circ>)}"

abbreviation C6 :: "ufun set" where "C6 \<equiv> clos basis_6"

lemma C6_one: "cst 1 \<in> C6" and C6_E: "funE \<in> C6"
  by (rule clos_init, simp add: basis_6_def)+

lemma C6_plusI: "F \<in> C6 \<Longrightarrow> opPlusI F \<in> C6"
  and C6_box: "F \<in> C6 \<Longrightarrow> opBox F \<in> C6"
  using clos_unop[of opPlusI basis_6 F] clos_unop[of opBox basis_6 F] by (simp_all add: basis_6_def)

lemma C6_comp: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> F \<circ> G \<in> C6"
  using clos_binop[of "(\<circ>)" basis_6 F G] by (simp add: basis_6_def)

lemmas C6_intros = C6_one C6_E C6_plusI C6_box C6_comp

subsection \<open>First functions in \<open>clos \<F>\<close>\<close>

text \<open>Auxiliary functions named in this section of the paper.\<close>
definition funMod3 :: ufun where "funMod3 x = x mod 3"
definition funM3   :: ufun where "funM3 x = 3 * x"
definition funR    :: ufun where "funR x = x + 2 * funRt x"     \<comment> \<open>as in Lemma 5.7\<close>

lemma funRt_small [simp]: "funRt 0 = 0" "funRt 1 = 1" "funRt 2 = 1" "funRt 3 = 1" "funRt 4 = 2"
proof -
  show "funRt 0 = 0" by (simp add: funRt_def)
  show "funRt 1 = 1" by (rule funRt_unique) simp_all
  show "funRt 2 = 1" by (rule funRt_unique) simp_all
  show "funRt 3 = 1" by (rule funRt_unique) simp_all
  show "funRt 4 = 2" by (rule funRt_unique) simp_all
qed

lemma funRt_small_Suc [simp]: "funRt (Suc 0) = 1" "funRt (Suc (Suc 0)) = 1"
  "funRt (Suc (Suc (Suc 0))) = 1" "funRt (Suc (Suc (Suc (Suc 0)))) = 2"
  using funRt_small by (simp_all add: numeral_eq_Suc)

lemma funE_small [simp]: "funE 0 = 0" "funE 1 = 0" "funE 2 = 1" "funE 3 = 2" "funE 4 = 0"
  by (simp_all add: funE_alt)

lemma funE_small_Suc [simp]:
  "funE (Suc 0) = 0" "funE (Suc (Suc 0)) = 1" "funE (Suc (Suc (Suc 0))) = 2"
  "funE (Suc (Suc (Suc (Suc 0)))) = 0"
  using funE_small by (simp_all add: numeral_eq_Suc)

lemma S_expr: "opPlusI (cst 1) = funS"
  by (rule ext) (simp add: opPlusI_def cst_def funS_def)

lemma Sgn_expr: "opBox (cst 1) = funSgn"
proof
  fix x show "opBox (cst 1) x = funSgn x" by (cases x) (simp_all add: cst_def funSgn_def)
qed

lemma zero_expr: "funE \<circ> cst 1 = cst 0"
  by (rule ext) (simp add: cst_def funE_small)

lemma D_expr: "opPlusI (opPlusI (cst 0)) = funD"
  by (rule ext) (simp add: opPlusI_def cst_def funD_def)

lemma M3_expr: "opPlusI funD = funM3"
  by (rule ext) (simp add: opPlusI_def funD_def funM3_def)

lemma O_expr: "funE \<circ> funD \<circ> funS \<circ> funSgn = funO"
  by (rule ext) (simp add: funD_def funS_def funSgn_def funO_def funE_small)

lemma Q_expr: "funO \<circ> funE = funQ"
proof
  fix x
  have "funE x = 0 \<longleftrightarrow> funRt x * funRt x = x"
    using funRt_sq_le[of x] by (auto simp: funE_alt)
  then show "(funO \<circ> funE) x = funQ x" by (simp add: funO_def funQ_iff)
qed

lemma Mod3_expr: "opBox (funE \<circ> funS \<circ> funS) = funMod3"
proof
  fix n show "opBox (funE \<circ> funS \<circ> funS) n = funMod3 n"
  proof (induct n)
    case 0 then show ?case by (simp add: funMod3_def)
  next
    case (Suc n)
    have "n mod 3 = 0 \<or> n mod 3 = 1 \<or> n mod 3 = 2" by arith
    then show ?case using Suc
      by (auto simp: funMod3_def funS_def funE_small mod_Suc)
  qed
qed

text \<open>\<open>R(x) = x + 2\<lfloor>\<surd>x\<rfloor>\<close> (Lemma 5.7).\<close>
lemma R_step:
  "opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) (funS (funR n)) = funR (Suc n)"
proof -
  let ?r = "funRt n"
  define m where "m = Suc (Suc (Suc (Suc (funR n))))"
  have m_eq: "m = n + 2 * ?r + 4" by (simp add: m_def funR_def)
  have v: "opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) (funS (funR n)) = 2 * funQ m + Suc (funR n)"
    by (simp add: opPlusI_def funD_def funS_def m_def)
  have lo: "?r * ?r \<le> n" and hi: "n < Suc ?r * Suc ?r" by (rule funRt_sq_le, rule funRt_sq_gt)
  show ?thesis
  proof (cases "Suc ?r * Suc ?r = Suc n")
    case True
    then have "m = Suc (Suc ?r) * Suc (Suc ?r)" unfolding m_eq by (simp add: algebra_simps)
    then have q: "funQ m = 1" by (simp add: funQ_iff del: mult_Suc mult_Suc_right)
    have rt: "funRt (Suc n) = Suc ?r" using True funRt_Suc[of n] by simp
    show ?thesis unfolding v q by (simp add: funR_def rt)
  next
    case False
    then have "Suc n < Suc ?r * Suc ?r" using hi by linarith
    then have n_le: "n + 2 \<le> Suc ?r * Suc ?r" by simp
    have rt_m: "funRt m = Suc ?r"
      unfolding m_eq using lo n_le by (intro funRt_unique) (simp_all add: algebra_simps)
    have "Suc ?r * Suc ?r \<noteq> m"
      unfolding m_eq using lo by (simp add: algebra_simps)
    then have q: "funQ m = 0" by (simp add: funQ_iff rt_m)
    have rt: "funRt (Suc n) = ?r" using False funRt_Suc[of n] by simp
    show ?thesis unfolding v q by (simp add: funR_def rt)
  qed
qed

lemma R_expr: "opBox (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) \<circ> funS) = funR"
proof
  fix n show "opBox (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) \<circ> funS) n = funR n"
  proof (induct n)
    case 0 then show ?case by (simp add: funR_def)
  next
    case (Suc n) then show ?case by (simp only: opBox_Suc) (subst comp_apply, rule R_step)
  qed
qed

lemma Sq_expr: "opBox (funS \<circ> funR) = funSq"
proof
  fix n show "opBox (funS \<circ> funR) n = funSq n"
    by (induct n) (simp_all add: funS_def funR_def funSq_def algebra_simps)
qed

lemma S_in: "funS \<in> C6" by (metis S_expr C6_intros)
lemma Sgn_in: "funSgn \<in> C6" by (metis Sgn_expr C6_intros)
lemma zero_in: "cst 0 \<in> C6" by (metis zero_expr C6_intros)
lemma D_in: "funD \<in> C6" by (metis D_expr zero_in C6_intros)
lemma M3_in: "funM3 \<in> C6" by (metis M3_expr D_in C6_intros)
lemma O_in: "funO \<in> C6" by (metis O_expr D_in S_in Sgn_in C6_intros)
lemma Q_in: "funQ \<in> C6" by (metis Q_expr O_in C6_intros)
lemma Mod3_in: "funMod3 \<in> C6" by (metis Mod3_expr S_in C6_intros)
lemma R_in: "funR \<in> C6" by (metis R_expr D_in Q_in S_in C6_intros)
lemma Sq_in: "funSq \<in> C6" by (metis Sq_expr S_in R_in C6_intros)

subsection \<open>Definition 6.1\<close>

text \<open>The operators of Definition 6.1 (meaningful when \<open>F(x) \<ge> x\<close>, \<open>G(x) \<ge> x\<close>, and, for \<open>\<ominus>\<close>,
  \<open>F(x) \<ge> G\<^sup>2(x)\<close>; footnote 7: \<open>G\<^sup>2(x)\<close> is \<open>G(x)G(x)\<close>).\<close>
definition opMinusI :: uop where "opMinusI F x = F x - x"
definition opOplus  :: bop where "opOplus F G x = F x + G x * G x"
definition opOminus :: bop where "opOminus F G x = F x - G x * G x"
definition opOtimes :: bop where "opOtimes F G x = F x * G x"

subsection \<open>Lemma 6.2\<close>

text \<open>\<open>F\<^sup>- \<equiv> E S (M\<^sub>3 F E)\<^sup>+ (Sq F\<^sup>+)\<^sup>+\<close>.\<close>
definition exprMinusI :: uop where
  "exprMinusI F = funE \<circ> funS \<circ> opPlusI (funM3 \<circ> F \<circ> funE) \<circ> opPlusI (funSq \<circ> opPlusI F)"

lemma exprMinusI_in: "F \<in> C6 \<Longrightarrow> exprMinusI F \<in> C6"
  unfolding exprMinusI_def by (intro C6_intros S_in M3_in Sq_in)

text \<open>Pointwise correctness: needs \<open>F(x) \<ge> x\<close> only at the point \<open>x\<close>.\<close>
lemma exprMinusI_val:
  assumes "x \<le> F x"
  shows "exprMinusI F x = F x - x"
proof -
  define y where "y = (F x + x) * (F x + x) + x"
  have py: "opPlusI (funSq \<circ> opPlusI F) x = y" by (simp add: opPlusI_def funSq_def y_def)
  have ey: "funE y = x" unfolding y_def by (rule funE_sq_add) simp
  have "exprMinusI F x = funE (funS (opPlusI (funM3 \<circ> F \<circ> funE) (opPlusI (funSq \<circ> opPlusI F) x)))"
    by (simp only: exprMinusI_def comp_apply)
  also have "\<dots> = funE (funS (opPlusI (funM3 \<circ> F \<circ> funE) y))" by (simp only: py)
  also have "\<dots> = funE (Suc (3 * F x + y))"
    by (simp only: opPlusI_def comp_apply ey funM3_def funS_def)
  also have "\<dots> = funE ((F x + x) * (F x + x) + 3 * F x + x + 1)"
    by (simp add: y_def algebra_simps)
  also have "\<dots> = F x - x" using assms by (rule robinson_diff_E)
  finally show ?thesis .
qed

lemma Lemma_6_2:
  assumes "F \<in> C6" and "\<And>x. x \<le> F x"
  shows "opMinusI F \<in> C6"
proof -
  have "exprMinusI F = opMinusI F" by (rule ext) (simp add: exprMinusI_val assms(2) opMinusI_def)
  then show ?thesis using exprMinusI_in[OF assms(1)] by simp
qed

subsection \<open>Lemma 6.3\<close>

text \<open>\<open>Hf \<equiv> ((S Mod\<^sub>3\<^sup>+)\<^sup>\<box>)\<^sup>-\<close> and \<open>Rt \<equiv> Hf R\<^sup>-\<close>.\<close>
lemma Hf_aux: "opBox (funS \<circ> opPlusI funMod3) n = n + n div 2"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have m: "(n + n div 2) mod 3 = n mod 2" by presburger
  have d: "Suc n div 2 = n div 2 + n mod 2" by presburger
  from Suc m d show ?case by (simp add: funS_def opPlusI_def funMod3_def)
qed

definition exprHf :: ufun where "exprHf = exprMinusI (opBox (funS \<circ> opPlusI funMod3))"
definition exprRt :: ufun where "exprRt = funHf \<circ> exprMinusI funR"

lemma Hf_expr: "exprHf = funHf"
  by (rule ext) (simp add: exprHf_def exprMinusI_val Hf_aux funHf_def)

lemma Rt_expr: "exprRt = funRt"
  by (rule ext) (simp add: exprRt_def exprMinusI_val funR_def funHf_def)

lemma Lemma_6_3: "funHf \<in> C6" "funRt \<in> C6"
proof -
  show Hf: "funHf \<in> C6"
    unfolding Hf_expr[symmetric] exprHf_def by (intro exprMinusI_in C6_intros S_in Mod3_in)
  show "funRt \<in> C6"
    unfolding Rt_expr[symmetric] exprRt_def by (intro C6_comp Hf exprMinusI_in R_in)
qed

lemmas Hf_in = Lemma_6_3(1) and Rt_in = Lemma_6_3(2)

subsection \<open>Lemma 6.4\<close>

text \<open>\<open>F \<oplus> G \<equiv> (F\<^sup>- E)\<^sup>+ (Sq G)\<^sup>+\<close> and \<open>F \<ominus> G \<equiv> (F\<^sup>+ E)\<^sup>- (Sq G)\<^sup>+\<close>.\<close>
definition exprOplus :: bop where
  "exprOplus F G = opPlusI (exprMinusI F \<circ> funE) \<circ> opPlusI (funSq \<circ> G)"
definition exprOminus :: bop where
  "exprOminus F G = exprMinusI (opPlusI F \<circ> funE) \<circ> opPlusI (funSq \<circ> G)"

lemma exprOplus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> exprOplus F G \<in> C6"
  unfolding exprOplus_def by (intro C6_intros exprMinusI_in Sq_in)

lemma exprOminus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> exprOminus F G \<in> C6"
  unfolding exprOminus_def by (intro C6_intros exprMinusI_in Sq_in)

text \<open>If \<open>G(x) \<ge> x\<close> then \<open>E(G\<^sup>2(x) + x) = x\<close>.\<close>
lemma E_SqG: "x \<le> G x \<Longrightarrow> funE (G x * G x + x) = x"
  by (rule funE_sq_add) simp

lemma exprOplus_val:
  assumes "x \<le> F x" and "x \<le> G x"
  shows "exprOplus F G x = F x + G x * G x"
  using assms by (simp add: exprOplus_def opPlusI_def funSq_def E_SqG exprMinusI_val)

lemma exprOminus_val:
  assumes "x \<le> G x" and "G x * G x \<le> F x"
  shows "exprOminus F G x = F x - G x * G x"
proof -
  have "exprOminus F G x = exprMinusI (opPlusI F \<circ> funE) (G x * G x + x)"
    by (simp add: exprOminus_def opPlusI_def funSq_def)
  also have "\<dots> = (F x + x) - (G x * G x + x)"
    using assms by (simp add: exprMinusI_val opPlusI_def E_SqG)
  finally show ?thesis by simp
qed

lemma Lemma_6_4:
  assumes "F \<in> C6" "G \<in> C6" and "\<And>x. x \<le> F x" "\<And>x. x \<le> G x"
  shows "opOplus F G \<in> C6"
    and "(\<And>x. G x * G x \<le> F x) \<Longrightarrow> opOminus F G \<in> C6"
proof -
  have "exprOplus F G = opOplus F G"
    by (rule ext) (simp add: exprOplus_val assms opOplus_def)
  then show "opOplus F G \<in> C6" using exprOplus_in[OF assms(1,2)] by simp
next
  assume "\<And>x. G x * G x \<le> F x"
  then have "exprOminus F G = opOminus F G"
    by (intro ext) (simp add: exprOminus_val assms opOminus_def)
  then show "opOminus F G \<in> C6" using exprOminus_in[OF assms(1,2)] by simp
qed

subsection \<open>Lemma 6.5\<close>

text \<open>\<open>P\<^sup>^ \<equiv> ((Sq\<^sup>+)\<^sup>+)\<^sup>+ \<ominus> S\<close>, i.e. \<open>P\<^sup>^(x + 1) = x\<close>.\<close>
definition exprPhat :: ufun where
  "exprPhat = exprOminus (opPlusI (opPlusI (opPlusI funSq))) funS"

lemma Phat_in: "exprPhat \<in> C6"
  unfolding exprPhat_def by (intro exprOminus_in C6_intros Sq_in S_in)

lemma Phat_Suc: "exprPhat (Suc x) = x"
proof -
  let ?y = "Suc x"
  have "exprPhat ?y = (?y * ?y + 3 * ?y) - Suc ?y * Suc ?y"
    by (subst exprPhat_def, subst exprOminus_val)
       (simp_all add: opPlusI_def funSq_def funS_def algebra_simps)
  also have "\<dots> = x" by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>\<open>F \<otimes> G \<equiv> Rt((Hf Hf (Sq P\<^sup>^((Sq S Sq F \<oplus> G) \<ominus> Sq F) \<ominus> Sq G)) \<ominus> Sq F)\<close>.\<close>
definition exprOtimes :: bop where
  "exprOtimes F G =
     funRt \<circ> exprOminus
              (funHf \<circ> funHf \<circ>
                 exprOminus (funSq \<circ> exprPhat \<circ>
                               exprOminus (exprOplus (funSq \<circ> funS \<circ> funSq \<circ> F) G) (funSq \<circ> F))
                            (funSq \<circ> G))
              (funSq \<circ> F)"

lemma exprOtimes_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> exprOtimes F G \<in> C6"
  unfolding exprOtimes_def
  by (intro C6_comp exprOminus_in exprOplus_in Rt_in Hf_in Sq_in S_in Phat_in)

lemma exprOtimes_val:
  assumes Fx: "x \<le> F x" and Gx: "x \<le> G x"
  shows "exprOtimes F G x = F x * G x"
proof -
  define a where "a = F x"
  define b where "b = G x"
  have xa: "x \<le> a" and xb: "x \<le> b" using Fx Gx by (simp_all add: a_def b_def)
  have xaa: "x \<le> a * a" using xa by (metis le_square order.trans)
  have xbb: "x \<le> b * b" using xb by (metis le_square order.trans)
  \<comment> \<open>the intermediate functions of the formula, from the inside out\<close>
  define H1 where "H1 = exprOplus (funSq \<circ> funS \<circ> funSq \<circ> F) G"
  define H2 where "H2 = exprOminus H1 (funSq \<circ> F)"
  define H3 where "H3 = funSq \<circ> exprPhat \<circ> H2"
  define H4 where "H4 = exprOminus H3 (funSq \<circ> G)"
  define H5 where "H5 = funHf \<circ> funHf \<circ> H4"
  define H6 where "H6 = exprOminus H5 (funSq \<circ> F)"
  have otimes: "exprOtimes F G = funRt \<circ> H6"
    unfolding exprOtimes_def H6_def H5_def H4_def H3_def H2_def H1_def ..
  have SqF: "(funSq \<circ> F) x = a * a" and SqG: "(funSq \<circ> G) x = b * b"
    by (simp_all add: funSq_def a_def b_def)
  have cF: "x \<le> (funSq \<circ> F) x" and cG: "x \<le> (funSq \<circ> G) x" using xaa xbb by (simp_all only: SqF SqG)
  \<comment> \<open>\<open>(Sq S Sq F \<oplus> G)(x) = (a\<^sup>2 + 1)\<^sup>2 + b\<^sup>2\<close>\<close>
  have h1x: "x \<le> (funSq \<circ> funS \<circ> funSq \<circ> F) x"
    using xaa by (simp add: funSq_def funS_def a_def)
  have v1: "H1 x = Suc (a * a) * Suc (a * a) + b * b"
    unfolding H1_def using h1x Gx by (simp add: exprOplus_val funSq_def funS_def a_def b_def)
  \<comment> \<open>\<open>\<ominus> Sq F\<close> gives \<open>2a\<^sup>2 + 1 + b\<^sup>2\<close>\<close>
  have c2: "(funSq \<circ> F) x * (funSq \<circ> F) x \<le> H1 x" unfolding SqF v1 by (simp add: algebra_simps)
  have v2: "H2 x = Suc (2 * (a * a) + b * b)"
    unfolding H2_def exprOminus_val[of x "funSq \<circ> F" H1, OF cF c2] SqF v1 by (simp add: algebra_simps)
  \<comment> \<open>\<open>Sq P\<^sup>^\<close> gives \<open>(2a\<^sup>2 + b\<^sup>2)\<^sup>2\<close>\<close>
  let ?c = "2 * (a * a) + b * b"
  have v3: "H3 x = ?c * ?c" by (simp add: H3_def v2 Phat_Suc funSq_def)
  \<comment> \<open>\<open>\<ominus> Sq G\<close> gives \<open>4a\<^sup>4 + 4a\<^sup>2b\<^sup>2\<close>\<close>
  have c4: "(funSq \<circ> G) x * (funSq \<circ> G) x \<le> H3 x" unfolding SqG v3 by (intro mult_le_mono) simp_all
  have v4: "H4 x = 4 * ((a * a) * (a * a)) + 4 * ((a * a) * (b * b))"
    unfolding H4_def exprOminus_val[of x "funSq \<circ> G" H3, OF cG c4] SqG v3 by (simp add: algebra_simps)
  \<comment> \<open>\<open>Hf Hf\<close> gives \<open>a\<^sup>4 + a\<^sup>2b\<^sup>2\<close>; \<open>\<ominus> Sq F\<close> gives \<open>a\<^sup>2b\<^sup>2\<close>; finally \<open>Rt\<close> gives \<open>ab\<close>\<close>
  have v5: "H5 x = (a * a) * (a * a) + (a * a) * (b * b)" by (simp add: H5_def v4 funHf_def)
  have c6: "(funSq \<circ> F) x * (funSq \<circ> F) x \<le> H5 x" unfolding SqF v5 by simp
  have v6: "H6 x = (a * b) * (a * b)"
    unfolding H6_def exprOminus_val[of x "funSq \<circ> F" H5, OF cF c6] SqF v5 by (simp add: algebra_simps)
  show ?thesis unfolding otimes comp_apply v6 funRt_sq by (simp add: a_def b_def)
qed

lemma Lemma_6_5:
  assumes "F \<in> C6" "G \<in> C6" and "\<And>x. x \<le> F x" "\<And>x. x \<le> G x"
  shows "opOtimes F G \<in> C6"
proof -
  have "exprOtimes F G = opOtimes F G"
    by (rule ext) (simp add: exprOtimes_val assms opOtimes_def)
  then show ?thesis using exprOtimes_in[OF assms(1,2)] by simp
qed

subsection \<open>Lemma 6.6\<close>

text \<open>\<open>F + G \<equiv> ((Rt((D(F\<^sup>+ \<otimes> G\<^sup>+) \<oplus> F\<^sup>+) \<oplus> G\<^sup>+))\<^sup>-)\<^sup>-\<close>.\<close>
definition exprPlus :: bop where
  "exprPlus F G =
     exprMinusI (exprMinusI
       (funRt \<circ> exprOplus (exprOplus (funD \<circ> exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F)) (opPlusI G)))"

text \<open>\<open>F - G \<equiv> E S (Sq(F + G) + M\<^sub>3 F + G)\<close>.\<close>
definition exprMinus :: bop where
  "exprMinus F G = funE \<circ> funS \<circ> exprPlus (exprPlus (funSq \<circ> exprPlus F G) (funM3 \<circ> F)) G"

lemma exprPlus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> exprPlus F G \<in> C6"
  unfolding exprPlus_def
  by (intro exprMinusI_in C6_comp Rt_in exprOplus_in exprOtimes_in D_in C6_plusI)

lemma exprMinus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> exprMinus F G \<in> C6"
  unfolding exprMinus_def
  by (intro C6_comp exprPlus_in S_in Sq_in M3_in C6_E)

lemma exprPlus_val: "exprPlus F G x = F x + G x"
proof -
  define a where "a = F x + x"
  define b where "b = G x + x"
  have xa: "x \<le> a" and xb: "x \<le> b" by (simp_all add: a_def b_def)
  have pF: "opPlusI F x = a" and pG: "opPlusI G x = b" by (simp_all add: opPlusI_def a_def b_def)
  have t: "exprOtimes (opPlusI F) (opPlusI G) x = a * b"
    using exprOtimes_val[of x "opPlusI F" "opPlusI G"] by (simp add: opPlusI_def a_def b_def)
  have x2ab: "x \<le> 2 * (a * b)"
  proof (cases x)
    case 0 then show ?thesis by simp
  next
    case (Suc y)
    then have "1 \<le> b" using xb by simp
    then have "a * 1 \<le> a * b" by (rule mult_le_mono2)
    with xa show ?thesis by linarith
  qed
  have o1: "exprOplus (funD \<circ> exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F) x = 2 * (a * b) + a * a"
    using x2ab xa by (subst exprOplus_val) (simp_all add: funD_def t pF)
  have o2: "exprOplus (exprOplus (funD \<circ> exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F)) (opPlusI G) x
              = (a + b) * (a + b)"
    using x2ab xb by (subst exprOplus_val) (simp_all add: o1 pG algebra_simps)
  define H where "H = funRt \<circ> exprOplus (exprOplus (funD \<circ> exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F)) (opPlusI G)"
  have rH: "H x = a + b" by (simp add: H_def o2)
  have m1: "exprMinusI H x = a + b - x"
    using exprMinusI_val[of x H] rH xa by simp
  have m2: "exprMinusI (exprMinusI H) x = (a + b - x) - x"
    using exprMinusI_val[of x "exprMinusI H"] m1 xa xb by simp
  have "exprPlus F G = exprMinusI (exprMinusI H)" by (simp only: exprPlus_def H_def)
  then show ?thesis using m2 by (simp add: a_def b_def)
qed

lemma exprPlus_eq: "exprPlus F G = opPlus F G"
  by (rule ext) (simp add: exprPlus_val opPlus_def)

text \<open>The difference function computed by \<open>F - G\<close> (footnote 8: it is \<open>F - G\<close> where \<open>F \<ge> G\<close>,
  and some other value elsewhere).\<close>
definition dE :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dE \<alpha> \<beta> = funE ((\<alpha> + \<beta>) * (\<alpha> + \<beta>) + 3 * \<alpha> + \<beta> + 1)"

lemma dE_difference: "is_difference dE"
  unfolding is_difference_def dE_def by (intro allI impI, rule robinson_diff_E)

lemma dE_PR: "dE \<in> PrimRec2"
  unfolding dE_def using funE_PR by prec

lemma exprMinus_eq: "exprMinus F G = opDiff dE F G"
  by (rule ext)
     (simp add: exprMinus_def exprPlus_val opDiff_apply dE_def funSq_def funM3_def funS_def algebra_simps)

lemma Lemma_6_6:
  assumes "F \<in> C6" "G \<in> C6"
  shows "opPlus F G \<in> C6"
    and "(\<And>x. G x \<le> F x) \<Longrightarrow> opMinus F G \<in> C6"
proof -
  show "opPlus F G \<in> C6" using exprPlus_in[OF assms] by (simp add: exprPlus_eq)
next
  assume "\<And>x. G x \<le> F x"
  then have "exprMinus F G = opMinus F G"
    using dE_difference by (intro ext) (simp add: exprMinus_eq opDiff_apply opMinus_def is_difference_def)
  then show "opMinus F G \<in> C6" using exprMinus_in[OF assms] by simp
qed

end
