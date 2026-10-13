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
proof -
  let ?B = "basis_L33 d"
  have diff: "opDiff d F G \<in> clos ?B" if "F \<in> clos ?B" "G \<in> clos ?B" for F G
    using clos_binop[of "opDiff d" ?B F G] that by (simp add: basis_L33_sel)
  have "funE = opDiff d funI (funSq \<circ> funRt)"
  proof
    fix x
    have "funRt x * funRt x \<le> x" by (rule funRt_sq_le)
    then show "funE x = opDiff d funI (funSq \<circ> funRt) x"
      using d_diff by (simp add: opDiff_apply funI_def funSq_def funE_alt is_difference_def)
  qed
  moreover have "opDiff d funI (funSq \<circ> funRt) \<in> clos ?B"
    by (subst funI_eq_box_S[symmetric]) (clos_solve add: diff)
  ultimately have E: "funE \<in> clos ?B" by simp
  have diff_PR: "opDiff d F G \<in> PrimNN" if "F \<in> PrimNN" "G \<in> PrimNN" for F G
    using opPointwise_PR[OF d_PR that] by (simp add: opDiff_def)
  show ?thesis by (simulate S: Robinson_1947_sec7_thm3 add: E prim: diff_PR)
qed

subsection \<open>Theorem 6.7\<close>

theorem Theorem_6_7: "suitable basis_6"
proof -
  have diff: "opDiff dE F G \<in> C6" if "F \<in> C6" "G \<in> C6" for F G
    using exprMinus_in[OF that] by (simp add: exprMinus_eq)
  show ?thesis by (simulate S: Lemma_3_3[OF dE_difference dE_PR] add: diff)
qed

end
