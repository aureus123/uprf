(*  Title:   UPRF_Sec6_Thm67.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Lemma 3.3 and Theorem 6.7, proved as in the paper from Robinson's theorem
    (proved in UPRF_Robinson).
*)

theory UPRF_Sec6_Thm67
  imports UPRF_Robinson
begin

section \<open>Lemma 3.3 and Theorem 6.7\<close>

subsection \<open>Lemma 3.3\<close>

text \<open>Lemma 3.3: the basis \<open>\<langle>S, Sq, O, Hf, Rt, F + G, F - G, FG, F\<^sup>\<box>\<rangle>\<close> is suitable,
  for every primitive recursive difference function used as \<open>F - G\<close>.
  The paper derives it from Lemma 3.1 and Theorem 2 of [15]; here we derive it
  from Theorem 3 of [15] (proved in UPRF_Robinson) via \<open>E \<equiv> I - Sq Rt\<close>.\<close>
lemma Lemma_3_3:
  assumes d_diff: "is_difference d" and d_PR: "d \<in> PrimRec2"
  shows "suitable (basis_L33 d)"
proof (rule suitable_by_simulation[OF Robinson_1947_sec7_thm3])
  let ?B = "basis_L33 d"
  have S: "funS \<in> clos ?B" by (rule clos_init) (simp add: basis_L33_def)
  have Sq: "funSq \<in> clos ?B" by (rule clos_init) (simp add: basis_L33_def)
  have Rt: "funRt \<in> clos ?B" by (rule clos_init) (simp add: basis_L33_def)
  have I: "funI \<in> clos ?B"
    using clos_unop[of opBox ?B funS] S by (simp add: basis_L33_def funI_eq_box_S)
  have SqRt: "funSq \<circ> funRt \<in> clos ?B"
    using clos_binop[of "(\<circ>)" ?B funSq funRt] Sq Rt by (simp add: basis_L33_def)
  have "funE = opDiff d funI (funSq \<circ> funRt)"
  proof
    fix x
    have "funRt x * funRt x \<le> x" by (rule funRt_sq_le)
    then show "funE x = opDiff d funI (funSq \<circ> funRt) x"
      using d_diff by (simp add: opDiff_apply funI_def funSq_def funE_alt is_difference_def)
  qed
  moreover have "opDiff d funI (funSq \<circ> funRt) \<in> clos ?B"
    using clos_binop[of "opDiff d" ?B funI "funSq \<circ> funRt"] I SqRt by (simp add: basis_L33_def)
  ultimately have E: "funE \<in> clos ?B" by simp
  show "inits basis_Robinson \<subseteq> clos ?B"
    using S E by (simp add: basis_Robinson_def)
  show "applyU u F \<in> clos ?B" if "u \<in> unops basis_Robinson" "F \<in> clos ?B" for u F
    using that clos_unop_app[of u ?B F] by (simp add: basis_Robinson_def basis_L33_def)
  show "applyB b F G \<in> clos ?B" if "b \<in> binops basis_Robinson" "F \<in> clos ?B" "G \<in> clos ?B" for b F G
    using that clos_binop_app[of b ?B F G] by (auto simp: basis_Robinson_def basis_L33_def)
  show "clos ?B \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_L33_def opDiff_def applyU_def applyB_def
             funS_PR funSq_PR funO_PR funHf_PR funRt_PR d_PR
             intro: opBox_PR opPlus_PR comp_PR opPointwise_PR)
qed

subsection \<open>Theorem 6.7\<close>

theorem Theorem_6_7: "suitable basis_6"
proof (rule suitable_by_simulation[OF Lemma_3_3[OF dE_difference dE_PR]])
  show "inits (basis_L33 dE) \<subseteq> C6"
    by (auto simp: basis_L33_def S_in Sq_in O_in Hf_in Rt_in)
  show "applyU u F \<in> C6" if "u \<in> unops (basis_L33 dE)" "F \<in> C6" for u F
    using that C6_box by (simp add: basis_L33_def applyU_def)
  show "applyB b F G \<in> C6" if "b \<in> binops (basis_L33 dE)" "F \<in> C6" "G \<in> C6" for b F G
    using that C6_comp exprPlus_in[of F G] exprMinus_in[of F G]
    by (auto simp: basis_L33_def applyB_def exprPlus_eq exprMinus_eq)
  show "C6 \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_6_def applyU_def applyB_def cst_PR funE_PR
             intro: opPlusI_PR opBox_PR comp_PR pr_comp1_1)
qed

end
