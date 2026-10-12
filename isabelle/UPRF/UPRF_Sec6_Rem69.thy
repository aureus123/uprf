(*  Title:   UPRF_Sec6_Rem69.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Section 6, Remark 6.9: with iteration starting from a = 1, the constant 1
    can be dropped:
      (I)   \<langle>E, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>
      (II)  \<langle>K, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>
      (III) \<langle>L, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>
    are suitable bases.
*)

theory UPRF_Sec6_Rem69
  imports UPRF_Sec6_Thm68
begin

section \<open>Remark 6.9: iteration starting from \<open>a = 1\<close>\<close>

text \<open>Keep the starting value \<open>1\<close> of \<open>F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close> as the numeral \<open>1\<close> (not \<open>Suc 0\<close>) during simplification.\<close>
declare One_nat_def [simp del]

text \<open>Recovering \<open>F\<^sup>\<box>\<close> from \<open>F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close> with a suitable predecessor \<open>P\<^sup>^\<close>, i.e. \<open>P\<^sup>^(x + 1) = x\<close>:
  \<open>F\<^sup>\<box> \<equiv> P\<^sup>^ (S F P\<^sup>^)\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close>.\<close>
lemma box_from_box1:
  assumes Phat: "\<And>x. Phat (Suc x) = x"
  shows "Phat \<circ> opBoxA 1 (funS \<circ> F \<circ> Phat) = opBox F"
proof
  have aux: "opBoxA 1 (funS \<circ> F \<circ> Phat) n = Suc (opBox F n)" for n
    by (induct n) (simp_all add: funS_def Phat)
  fix n show "(Phat \<circ> opBoxA 1 (funS \<circ> F \<circ> Phat)) n = opBox F n"
    by (simp add: aux Phat)
qed

subsection \<open>(I) The basis \<open>\<langle>E, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>\<close>\<close>

definition basis_69_I :: basis where
  "basis_69_I = Basis {funE} {opPlusI, opBoxA 1} {(\<circ>)}"

abbreviation CI :: "ufun set" where "CI \<equiv> clos basis_69_I"

lemma CI_E: "funE \<in> CI"
  by (rule clos_init) (simp add: basis_69_I_def)

lemma CI_plusI: "F \<in> CI \<Longrightarrow> opPlusI F \<in> CI"
  and CI_box1: "F \<in> CI \<Longrightarrow> opBoxA 1 F \<in> CI"
  using clos_unop[of opPlusI basis_69_I F] clos_unop[of "opBoxA 1" basis_69_I F]
  by (simp_all add: basis_69_I_def)

lemma CI_comp: "F \<in> CI \<Longrightarrow> G \<in> CI \<Longrightarrow> F \<circ> G \<in> CI"
  using clos_binop[of "(\<circ>)" basis_69_I F G] by (simp add: basis_69_I_def)

lemmas CI_intros = CI_E CI_plusI CI_box1 CI_comp

text \<open>\<open>O \<equiv> E\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close>, \<open>\<overline>0 \<equiv> E O\<close>, \<open>\<overline>1 \<equiv> O \<overline>0\<close>.\<close>
lemma O_expr_I: "opBoxA 1 funE = funO"
proof
  have Suc0: "opBoxA 1 funE (Suc m) = 0" for m
    by (induct m) simp_all
  fix n show "opBoxA 1 funE n = funO n"
    by (cases n) (simp_all add: funO_def Suc0 del: opBoxA.simps(2))
qed

lemma zero_expr_I: "funE \<circ> funO = cst 0"
  by (rule ext) (simp add: funO_def cst_def)

lemma one_expr_I: "funO \<circ> cst 0 = cst 1"
  by (rule ext) (simp add: funO_def cst_def)

text \<open>\<open>G \<equiv> (((D Q S S)\<^sup>+ S)\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>))\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close>, where \<open>G(x) = (x + 1)\<^sup>2\<close>.  The inner iteration
  computes \<open>R(x) + 1 = x + 2\<lfloor>\<surd>x\<rfloor> + 1\<close>.\<close>
lemma G_inner_step:
  "(opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS) (funS y)
     = funS (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) (funS y))"
  by (simp add: opPlusI_def funS_def)

lemma G_inner: "opBoxA 1 (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS) n = funS (funR n)"
proof (induct n)
  case 0 then show ?case by (simp add: funR_def funS_def)
next
  case (Suc n)
  have "opBoxA 1 (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS) (Suc n)
          = (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS) (funS (funR n))"
    by (simp only: opBoxA.simps Suc)
  also have "\<dots> = funS (funR (Suc n))" by (simp only: G_inner_step R_step)
  finally show ?case .
qed

definition funG :: ufun where "funG x = (x + 1) * (x + 1)"

lemma G_expr_I: "opBoxA 1 (opBoxA 1 (opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS)) = funG"
proof
  let ?T = "opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS) \<circ> funS"
  fix n show "opBoxA 1 (opBoxA 1 ?T) n = funG n"
  proof (induct n)
    case 0 then show ?case by (simp add: funG_def)
  next
    case (Suc n)
    have rt: "funRt (funG n) = Suc n" unfolding funG_def using funRt_sq[of "Suc n"] by simp
    have "opBoxA 1 (opBoxA 1 ?T) (Suc n) = opBoxA 1 ?T (opBoxA 1 (opBoxA 1 ?T) n)"
      by (simp only: opBoxA.simps)
    also have "\<dots> = opBoxA 1 ?T (funG n)" by (simp only: Suc.hyps)
    also have "\<dots> = funS (funR (funG n))" by (rule G_inner)
    also have "\<dots> = funG (Suc n)"
      by (simp only: funR_def rt funS_def) (simp add: funG_def algebra_simps)
    finally show ?case .
  qed
qed

text \<open>\<open>P\<^sup>^ \<equiv> E S S ((G\<^sup>+)\<^sup>+)\<^sup>+\<close>.\<close>
definition exprPhat_I :: ufun where
  "exprPhat_I = funE \<circ> funS \<circ> funS \<circ> opPlusI (opPlusI (opPlusI funG))"

lemma Phat_I_Suc: "exprPhat_I (Suc x) = x"
proof -
  have "exprPhat_I (Suc x) = funE (Suc (Suc (funG (Suc x) + Suc x + Suc x + Suc x)))"
    by (simp only: exprPhat_I_def comp_apply opPlusI_def funS_def)
  also have "\<dots> = funE ((x + 3) * (x + 3) + x)"
    by (rule arg_cong[where f = funE]) (simp add: funG_def algebra_simps)
  also have "\<dots> = x" by (rule funE_sq_add) simp
  finally show ?thesis .
qed

lemma O_in_I: "funO \<in> CI" by (metis O_expr_I CI_intros)
lemma zero_in_I: "cst 0 \<in> CI" by (metis zero_expr_I O_in_I CI_intros)
lemma one_in_I: "cst 1 \<in> CI" by (metis one_expr_I O_in_I zero_in_I CI_intros)
lemma S_in_I: "funS \<in> CI" by (metis S_expr one_in_I CI_intros)
lemma D_in_I: "funD \<in> CI" by (metis D_expr zero_in_I CI_intros)
lemma Q_in_I: "funQ \<in> CI" by (metis Q_expr O_in_I CI_intros)
lemma G_in_I: "funG \<in> CI" by (metis G_expr_I D_in_I Q_in_I S_in_I CI_intros)
lemma Phat_in_I: "exprPhat_I \<in> CI"
  unfolding exprPhat_I_def by (intro CI_intros S_in_I G_in_I)

lemma box_in_I: "F \<in> CI \<Longrightarrow> opBox F \<in> CI"
  using box_from_box1[of exprPhat_I F, OF Phat_I_Suc] by (metis Phat_in_I S_in_I CI_intros)

theorem Remark_6_9_I: "suitable basis_69_I"
proof (rule suitable_by_simulation[OF Theorem_6_7])
  show "inits basis_6 \<subseteq> CI" using one_in_I CI_E by (simp add: basis_6_def)
  show "applyU u F \<in> CI" if "u \<in> unops basis_6" "F \<in> CI" for u F
    using that CI_plusI box_in_I by (auto simp: basis_6_def applyU_def)
  show "applyB b F G \<in> CI" if "b \<in> binops basis_6" "F \<in> CI" "G \<in> CI" for b F G
    using that CI_comp[of F G] by (simp add: basis_6_def applyB_def comp_def)
  show "CI \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_69_I_def applyU_def applyB_def funE_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

subsection \<open>(II) The basis \<open>\<langle>K, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>\<close>\<close>

definition basis_69_II :: basis where
  "basis_69_II = Basis {funK} {opPlusI, opBoxA 1} {(\<circ>)}"

abbreviation CII :: "ufun set" where "CII \<equiv> clos basis_69_II"

lemma CII_K: "funK \<in> CII"
  by (rule clos_init) (simp add: basis_69_II_def)

lemma CII_plusI: "F \<in> CII \<Longrightarrow> opPlusI F \<in> CII"
  and CII_box1: "F \<in> CII \<Longrightarrow> opBoxA 1 F \<in> CII"
  using clos_unop[of opPlusI basis_69_II F] clos_unop[of "opBoxA 1" basis_69_II F]
  by (simp_all add: basis_69_II_def)

lemma CII_comp: "F \<in> CII \<Longrightarrow> G \<in> CII \<Longrightarrow> F \<circ> G \<in> CII"
  using clos_binop[of "(\<circ>)" basis_69_II F G] by (simp add: basis_69_II_def)

lemmas CII_intros = CII_K CII_plusI CII_box1 CII_comp

text \<open>\<open>O \<equiv> K\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close>, \<open>\<overline>0 \<equiv> K O\<close>, \<open>\<overline>1 \<equiv> O \<overline>0\<close>.\<close>
lemma O_expr_II: "opBoxA 1 funK = funO"
proof
  fix n show "opBoxA 1 funK n = funO n"
  proof (cases n)
    case 0 then show ?thesis by (simp add: funO_def)
  next
    case (Suc m)
    have Suc0: "opBoxA 1 funK (Suc k) = 0" for k
      by (induct k) (simp_all add: funK_0 funK_1)
    show ?thesis using Suc Suc0 by (simp add: funO_def del: opBoxA.simps(2))
  qed
qed

lemma zero_expr_II: "funK \<circ> funO = cst 0"
  by (rule ext) (simp add: funO_def cst_def funK_0 funK_1)

text \<open>\<open>H \<equiv> S (S K\<^sup>+ S)\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close>, where \<open>H(x) = (x + 1)(x + 4)/2\<close>.\<close>
definition funH :: ufun where "funH x = (x + 1) * (x + 4) div 2"

lemma funH_sf: "funH x = sf (Suc x) + x + 1"
proof -
  have "(x + 1) * (x + 4) = 2 * (sf (Suc x) + x + 1)"
    using two_sf[of "Suc x"] by (simp add: algebra_simps)
  then show ?thesis by (simp add: funH_def)
qed

lemma sf_Suc_0: "sf (Suc 0) = 1" by (simp add: sf_def)

lemma H_inner: "opBoxA 1 (funS \<circ> opPlusI funK \<circ> funS) n = sf (Suc n) + n"
proof (induct n)
  case 0 then show ?case by (simp add: sf_Suc_0)
next
  case (Suc n)
  have "funK (sf (Suc n) + Suc n) = Suc n" by (rule funK_diag) simp
  then show ?case using Suc sf_Suc[of "Suc n"] by (simp add: funS_def opPlusI_def)
qed

lemma H_expr_II: "funS \<circ> opBoxA 1 (funS \<circ> opPlusI funK \<circ> funS) = funH"
  by (rule ext) (simp add: H_inner funH_sf funS_def)

text \<open>\<open>P\<^sup>^ \<equiv> K S S S (H\<^sup>+)\<^sup>+\<close>.\<close>
definition exprPhat_II :: ufun where
  "exprPhat_II = funK \<circ> funS \<circ> funS \<circ> funS \<circ> opPlusI (opPlusI funH)"

lemma Phat_II_Suc: "exprPhat_II (Suc x) = x"
proof -
  have "exprPhat_II (Suc x) = funK (Suc (Suc (Suc (funH (Suc x) + Suc x + Suc x))))"
    by (simp only: exprPhat_II_def comp_apply opPlusI_def funS_def)
  also have "\<dots> = funK (sf (Suc (Suc (Suc (Suc x)))) + x)"
    by (rule arg_cong[where f = funK]) (simp add: funH_sf sf_Suc)
  also have "\<dots> = x" by (rule funK_diag) simp
  finally show ?thesis .
qed

lemma O_in_II: "funO \<in> CII" by (metis O_expr_II CII_intros)
lemma zero_in_II: "cst 0 \<in> CII" by (metis zero_expr_II O_in_II CII_intros)
lemma one_in_II: "cst 1 \<in> CII" by (metis one_expr_I O_in_II zero_in_II CII_intros)
lemma S_in_II: "funS \<in> CII" by (metis S_expr one_in_II CII_intros)
lemma H_in_II: "funH \<in> CII" by (metis H_expr_II S_in_II CII_intros)
lemma Phat_in_II: "exprPhat_II \<in> CII"
  unfolding exprPhat_II_def by (intro CII_intros S_in_II H_in_II)

lemma box_in_II: "F \<in> CII \<Longrightarrow> opBox F \<in> CII"
  using box_from_box1[of exprPhat_II F, OF Phat_II_Suc] by (metis Phat_in_II S_in_II CII_intros)

theorem Remark_6_9_II: "suitable basis_69_II"
proof (rule suitable_by_simulation[OF Theorem_6_8_K])
  show "inits basis_6K \<subseteq> CII" using one_in_II CII_K by (simp add: basis_6K_def)
  show "applyU u F \<in> CII" if "u \<in> unops basis_6K" "F \<in> CII" for u F
    using that CII_plusI box_in_II by (auto simp: basis_6K_def applyU_def)
  show "applyB b F G \<in> CII" if "b \<in> binops basis_6K" "F \<in> CII" "G \<in> CII" for b F G
    using that CII_comp[of F G] by (simp add: basis_6K_def applyB_def comp_def)
  show "CII \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_69_II_def applyU_def applyB_def funK_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

subsection \<open>(III) The basis \<open>\<langle>L, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<rangle>\<close>\<close>

definition basis_69_III :: basis where
  "basis_69_III = Basis {funL} {opPlusI, opBoxA 1} {(\<circ>)}"

abbreviation CIII :: "ufun set" where "CIII \<equiv> clos basis_69_III"

lemma CIII_L: "funL \<in> CIII"
  by (rule clos_init) (simp add: basis_69_III_def)

lemma CIII_plusI: "F \<in> CIII \<Longrightarrow> opPlusI F \<in> CIII"
  and CIII_box1: "F \<in> CIII \<Longrightarrow> opBoxA 1 F \<in> CIII"
  using clos_unop[of opPlusI basis_69_III F] clos_unop[of "opBoxA 1" basis_69_III F]
  by (simp_all add: basis_69_III_def)

lemma CIII_comp: "F \<in> CIII \<Longrightarrow> G \<in> CIII \<Longrightarrow> F \<circ> G \<in> CIII"
  using clos_binop[of "(\<circ>)" basis_69_III F G] by (simp add: basis_69_III_def)

lemmas CIII_intros = CIII_L CIII_plusI CIII_box1 CIII_comp

text \<open>\<open>\<overline>1 \<equiv> L\<^sup>\<box>\<^sup>(\<^sup>1\<^sup>)\<close> (since \<open>L(1) = 1\<close>) and \<open>K \<equiv> L \<overline>1\<^sup>+ ((\<overline>1\<^sup>+)\<^sup>+ L)\<^sup>+\<close>.\<close>
lemma funL_1: "funL 1 = 1"
proof -
  have "funL (sf 1 + 0) = 1 - 0" by (rule funL_diag) simp
  then show ?thesis by (simp only: sf_at_1 add_0_right diff_zero)
qed

lemma one_expr_III: "opBoxA 1 funL = cst 1"
proof
  fix n show "opBoxA 1 funL n = cst 1 n" by (induct n) (simp_all add: cst_def funL_1)
qed

lemma one_in_III: "cst 1 \<in> CIII" by (metis one_expr_III CIII_intros)
lemma K_in_III: "funK \<in> CIII" by (metis K_expr_L one_in_III CIII_intros)

theorem Remark_6_9_III: "suitable basis_69_III"
proof (rule suitable_by_simulation[OF Remark_6_9_II])
  show "inits basis_69_II \<subseteq> CIII" using K_in_III by (simp add: basis_69_II_def)
  show "applyU u F \<in> CIII" if "u \<in> unops basis_69_II" "F \<in> CIII" for u F
    using that CIII_plusI CIII_box1 by (auto simp: basis_69_II_def applyU_def)
  show "applyB b F G \<in> CIII" if "b \<in> binops basis_69_II" "F \<in> CIII" "G \<in> CIII" for b F G
    using that CIII_comp[of F G] by (simp add: basis_69_II_def applyB_def comp_def)
  show "CIII \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_69_III_def applyU_def applyB_def funL_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

end
