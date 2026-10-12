(*  Title:   UPRF_Robinson.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Robinson [15] (R. M. Robinson, Primitive recursive functions, Bull. AMS 53 (1947)
    925-942), Section 7, Theorem 3: <S, E, F + G, FG, F^box> is suitable.

    This is not Robinson's proof.  We use the AFP characterisation PrimRec1 = PrimRec1'
    (0, S, K, L closed under composition, pairing J(F,G) and a unary recursion operator)
    and show that clos \<F> (the basis of Theorem 6.7) contains PrimRec1', using only
    Lemmas 6.2-6.6, which do not depend on Robinson's theorem.  The recursion operator is
    obtained from F^box by iterating one step function along the rows of a triangle.
    Finally clos \<F> is contained in the closure of Robinson's basis.
*)

theory UPRF_Robinson
  imports UPRF_Sec6 "Recursion-Theory-I.PRecFun2"
begin

section \<open>Robinson's theorem [15, \S7, Theorem 3]\<close>

subsection \<open>More functions and operators in \<open>clos \<F>\<close>\<close>

lemma I_in: "funI \<in> C6"
  using C6_box[OF S_in] by (simp add: funI_eq_box_S)

lemma plus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> opPlus F G \<in> C6"
  by (rule Lemma_6_6(1))

lemma minus_in: "F \<in> C6 \<Longrightarrow> G \<in> C6 \<Longrightarrow> (\<And>x. G x \<le> F x) \<Longrightarrow> opMinus F G \<in> C6"
  by (rule Lemma_6_6(2))

text \<open>Product without restrictions: \<open>FG = Hf((F + G)\<^sup>2 - (F\<^sup>2 + G\<^sup>2))\<close>.\<close>
lemma sq_sum_minus: "(a + b) * (a + b) - (a * a + b * b) = 2 * (a * b)" for a b :: nat
proof -
  have "(a + b) * (a + b) = (a * a + b * b) + 2 * (a * b)" by (simp add: algebra_simps)
  then show ?thesis by simp
qed

lemma times_in:
  assumes "F \<in> C6" "G \<in> C6"
  shows "opOtimes F G \<in> C6"
proof -
  let ?X = "opMinus (funSq \<circ> opPlus F G) (opPlus (funSq \<circ> F) (funSq \<circ> G))"
  have "?X \<in> C6"
  proof (rule minus_in)
    show "funSq \<circ> opPlus F G \<in> C6" by (intro C6_comp Sq_in plus_in assms)
    show "opPlus (funSq \<circ> F) (funSq \<circ> G) \<in> C6" by (intro C6_comp Sq_in plus_in assms)
    show "opPlus (funSq \<circ> F) (funSq \<circ> G) x \<le> (funSq \<circ> opPlus F G) x" for x
      by (simp add: opPlus_def funSq_def algebra_simps)
  qed
  moreover have "opOtimes F G = funHf \<circ> ?X"
    by (rule ext) (simp add: opOtimes_def opMinus_def opPlus_def funSq_def funHf_def sq_sum_minus)
  ultimately show ?thesis using Hf_in by (simp add: C6_comp)
qed

text \<open>Definition by cases: \<open>F(x)\<close> if \<open>C(x) \<noteq> 0\<close>, \<open>G(x)\<close> otherwise; it is
  \<open>Sgn C \<cdot> F + O C \<cdot> G\<close>.\<close>
definition opCond :: "ufun \<Rightarrow> ufun \<Rightarrow> ufun \<Rightarrow> ufun" where
  "opCond C F G x = (if C x = 0 then G x else F x)"

lemma cond_in:
  assumes "C \<in> C6" "F \<in> C6" "G \<in> C6"
  shows "opCond C F G \<in> C6"
proof -
  have "opCond C F G = opPlus (opOtimes (funSgn \<circ> C) F) (opOtimes (funO \<circ> C) G)"
    by (rule ext) (simp add: opCond_def opPlus_def opOtimes_def funSgn_def funO_def)
  then show ?thesis by (simp add: plus_in times_in C6_comp Sgn_in O_in assms)
qed

subsection \<open>The Cantor functions \<open>A\<close>, \<open>V\<close>, \<open>K\<close>, \<open>L\<close> and \<open>J(F, G)\<close>\<close>

lemma A_in: "funA \<in> C6"
proof -
  have "funA = funHf \<circ> opPlusI funSq"
    by (rule ext) (simp add: funA_def funHf_def opPlusI_def funSq_def)
  moreover have "funHf \<circ> opPlusI funSq \<in> C6" by (intro C6_comp C6_plusI Hf_in Sq_in)
  ultimately show ?thesis by simp
qed

text \<open>\<open>V(x) = Hf(P\<^sup>^(Rt(8x + 1)))\<close>.\<close>
lemma V_in: "funV \<in> C6"
proof -
  have "funV = funHf \<circ> exprPhat \<circ> funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD"
  proof
    fix x
    have "funRt (Suc (8 * x)) \<noteq> 0"
      using funRt_sq_gt[of "Suc (8 * x)"] by (intro notI) simp
    then obtain m where m: "funRt (Suc (8 * x)) = Suc m" by (cases "funRt (Suc (8 * x))") simp_all
    have "(funS \<circ> funD \<circ> funD \<circ> funD) x = Suc (8 * x)" by (simp add: funS_def funD_def)
    then show "funV x = (funHf \<circ> exprPhat \<circ> funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD) x"
      by (simp add: funV_def funHf_def m Phat_Suc)
  qed
  moreover have "funHf \<circ> exprPhat \<circ> funRt \<circ> funS \<circ> funD \<circ> funD \<circ> funD \<in> C6"
    by (intro C6_comp Hf_in Phat_in Rt_in S_in D_in)
  ultimately show ?thesis by simp
qed

lemma K_in: "funK \<in> C6"
proof -
  have "funK = opMinus funI (funA \<circ> funV)"
    by (rule ext) (simp add: funK_def opMinus_def funI_def)
  moreover have "opMinus funI (funA \<circ> funV) \<in> C6"
    by (rule minus_in[OF I_in C6_comp[OF A_in V_in]])
       (simp add: funI_def funA_eq_sf funV_eq_c_sum sf_c_sum_le_arg)
  ultimately show ?thesis by simp
qed

lemma L_in: "funL \<in> C6"
proof -
  have "funL = opMinus funV funK"
    by (rule ext) (simp add: opMinus_def funL_eq_c_snd funV_eq_c_sum funK_eq_c_fst c_snd_def)
  moreover have "opMinus funV funK \<in> C6"
    by (rule minus_in[OF V_in K_in]) (simp add: funV_eq_c_sum funK_eq_c_fst c_fst_le_c_sum)
  ultimately show ?thesis by simp
qed

text \<open>The operator \<open>J(F, G)(x) = J(F(x), G(x)) = A(F(x) + G(x)) + F(x)\<close>.\<close>
definition opJ :: bop where "opJ F G x = c_pair (F x) (G x)"

lemma J_in:
  assumes "F \<in> C6" "G \<in> C6"
  shows "opJ F G \<in> C6"
proof -
  have "opJ F G = opPlus (funA \<circ> opPlus F G) F"
    by (rule ext) (simp add: opJ_def opPlus_def c_pair_def funA_eq_sf)
  then show ?thesis by (simp add: plus_in C6_comp A_in assms)
qed

subsection \<open>Recursion from iteration\<close>

text \<open>The unary recursion operator of the AFP: \<open>UnaryRecOp g h (J(y, x)) = f(y, x)\<close>, where
  \<open>f(0, x) = g(x)\<close> and \<open>f(y + 1, x) = h(J(J(y, f(y, x)), x))\<close>.\<close>
definition recF :: "ufun \<Rightarrow> ufun \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "recF g h y x = PrimRecOp g (pr_conv_1_to_3 h) y x"

lemma recF_0: "recF g h 0 x = g x"
  by (simp add: recF_def)

lemma recF_Suc: "recF g h (Suc y) x = h (c_pair (c_pair y (recF g h y x)) x)"
  by (simp add: recF_def pr_conv_1_to_3_def)

lemma UnaryRecOp_eq: "UnaryRecOp g h z = recF g h (c_fst z) (c_snd z)"
  by (simp add: UnaryRecOp_def pr_conv_2_to_1_def recF_def)

text \<open>A state \<open>J(J(N, y), v)\<close> stands for row \<open>N\<close>, column \<open>y \<le> N\<close>, value \<open>v = f(y, L(N - 1))\<close>.
  The step function \<open>T\<close> moves to the next column, or to the start of the next row:
  \<open>T(J(J(N, y), v)) = J(J(N, y + 1), h(J(J(y, v), L(N - 1))))\<close> if \<open>y < N\<close>, and
  \<open>T(J(J(N, N), v)) = J(J(N + 1, 0), g(L(N)))\<close>.
  The condition \<open>y < N\<close> is tested with the difference \<open>N - y\<close> of Lemma 6.6.\<close>
definition stepT :: "ufun \<Rightarrow> ufun \<Rightarrow> ufun" where
  "stepT g h =
     opCond (exprMinus (funK \<circ> funK) (funL \<circ> funK))
       (opJ (opJ (funK \<circ> funK) (funS \<circ> funL \<circ> funK))
            (h \<circ> opJ (opJ (funL \<circ> funK) funL) (funL \<circ> exprPhat \<circ> funK \<circ> funK)))
       (opJ (opJ (funS \<circ> funK \<circ> funK) (cst 0)) (g \<circ> funL \<circ> funK \<circ> funK))"

lemma stepT_in: "g \<in> C6 \<Longrightarrow> h \<in> C6 \<Longrightarrow> stepT g h \<in> C6"
  unfolding stepT_def
  by (intro cond_in J_in C6_comp exprMinus_in K_in L_in S_in Phat_in zero_in)

lemma Phat_pos: "0 < n \<Longrightarrow> exprPhat n = n - 1"
  by (cases n) (simp_all add: Phat_Suc)

lemma stepT_val:
  assumes "y \<le> N"
  shows "stepT g h (c_pair (c_pair N y) v) =
           (if y < N then c_pair (c_pair N (Suc y)) (h (c_pair (c_pair y v) (c_snd (N - 1))))
            else c_pair (c_pair (Suc N) 0) (g (c_snd N)))"
proof -
  have d: "dE N y = N - y" using dE_difference assms by (simp add: is_difference_def)
  show ?thesis
  proof (cases "y < N")
    case True
    then have "exprPhat N = N - 1" by (intro Phat_pos) simp
    with True d show ?thesis
      by (simp add: stepT_def opCond_def opJ_def exprMinus_eq opDiff_apply
                    funK_eq_c_fst funL_eq_c_snd funS_def)
  next
    case False
    with assms d show ?thesis
      by (simp add: stepT_def opCond_def opJ_def exprMinus_eq opDiff_apply
                    funK_eq_c_fst funL_eq_c_snd funS_def cst_def)
  qed
qed

definition stT :: "ufun \<Rightarrow> ufun \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "stT g h N y = c_pair (c_pair N y) (recF g h y (c_snd (N - 1)))"

lemma step_start: "stepT g h 0 = stT g h 1 0"
  using stepT_val[of 0 0 g h 0] by (simp add: c_pair_at_0 stT_def recF_0)

lemma step_in_row: "y < N \<Longrightarrow> stepT g h (stT g h N y) = stT g h N (Suc y)"
  using stepT_val[of y N g h] by (simp add: stT_def recF_Suc)

lemma step_row_end: "stepT g h (stT g h N N) = stT g h (Suc N) 0"
  using stepT_val[of N N g h] by (simp add: stT_def recF_0)

lemma in_row:
  assumes start: "(stepT g h ^^ sf N) 0 = stT g h N 0"
  shows "y \<le> N \<Longrightarrow> (stepT g h ^^ (sf N + y)) 0 = stT g h N y"
proof (induct y)
  case 0 then show ?case using start by simp
next
  case (Suc y)
  then have "(stepT g h ^^ (sf N + Suc y)) 0 = stepT g h (stT g h N y)" by simp
  also have "\<dots> = stT g h N (Suc y)" using Suc(2) by (intro step_in_row) simp
  finally show ?case .
qed

lemma row_start: "1 \<le> N \<Longrightarrow> (stepT g h ^^ sf N) 0 = stT g h N 0"
proof (induct N)
  case 0 then show ?case by simp
next
  case (Suc N)
  show ?case
  proof (cases "N = 0")
    case True
    have "sf (Suc 0) = 1" by (simp add: sf_def)
    with True show ?thesis using step_start by simp
  next
    case False
    then have "(stepT g h ^^ (sf N + N)) 0 = stT g h N N"
      using Suc(1) by (intro in_row) simp_all
    moreover have "sf (Suc N) = Suc (sf N + N)" using sf_at_Suc[of N] by simp
    ultimately show ?thesis by (simp add: step_row_end)
  qed
qed

text \<open>\<open>f(K z, L z) = L(T\<^sup>\<box>(A(z + 1) + K z))\<close>: the pair \<open>z\<close> is computed in row \<open>z + 1\<close>.\<close>
lemma UnaryRecOp_expr: "UnaryRecOp g h = funL \<circ> opBox (stepT g h) \<circ> opPlus (funA \<circ> funS) funK"
proof
  fix z
  have "c_fst z \<le> Suc z" using c_fst_le_arg[of z] by simp
  then have "(stepT g h ^^ (sf (Suc z) + c_fst z)) 0 = stT g h (Suc z) (c_fst z)"
    by (intro in_row row_start) simp_all
  then show "UnaryRecOp g h z = (funL \<circ> opBox (stepT g h) \<circ> opPlus (funA \<circ> funS) funK) z"
    by (simp add: UnaryRecOp_eq opBox_def opBoxA_eq_funpow opPlus_def funA_eq_sf funS_def
                  funK_eq_c_fst funL_eq_c_snd stT_def)
qed

lemma UnaryRecOp_in: "g \<in> C6 \<Longrightarrow> h \<in> C6 \<Longrightarrow> UnaryRecOp g h \<in> C6"
  unfolding UnaryRecOp_expr
  by (intro C6_comp C6_box stepT_in plus_in L_in A_in S_in K_in)

subsection \<open>Every primitive recursive function is in \<open>clos \<F>\<close>\<close>

lemma PrimRec1'_in: "f \<in> PrimRec1' \<Longrightarrow> f \<in> C6"
proof (induct f rule: PrimRec1'.induct)
  case zero
  have "(\<lambda>x. 0) = cst 0" by (rule ext) (simp add: cst_def)
  then show ?case by (simp add: zero_in)
next
  case suc
  have "Suc = funS" by (rule ext) (simp add: funS_def)
  then show ?case by (simp add: S_in)
next
  case fst then show ?case using K_in by (simp add: funK_eq_c_fst)
next
  case snd then show ?case using L_in by (simp add: funL_eq_c_snd)
next
  case (comp f g)
  have "(\<lambda>x. f (g x)) = f \<circ> g" by (simp add: comp_def)
  then show ?case using comp by (simp add: C6_comp)
next
  case (pair f g)
  have "c_f_pair f g = opJ f g" by (rule ext) (simp add: c_f_pair_def opJ_def)
  then show ?case using pair by (simp add: J_in)
next
  case (un_rec f g) then show ?case by (simp add: UnaryRecOp_in)
qed

theorem PrimNN_sub_C6: "PrimNN \<subseteq> C6"
  using PrimRec1'_in by (auto simp: pr_1_eq_1')

subsection \<open>Robinson's basis generates \<open>\<F>\<close>\<close>

abbreviation CR :: "ufun set" where "CR \<equiv> clos basis_Robinson"

lemma CR_S: "funS \<in> CR" and CR_E: "funE \<in> CR"
  by (rule clos_init, simp add: basis_Robinson_def)+

lemma CR_box: "F \<in> CR \<Longrightarrow> opBox F \<in> CR"
  using clos_unop[of opBox basis_Robinson F] by (simp add: basis_Robinson_def)

lemma CR_plus: "F \<in> CR \<Longrightarrow> G \<in> CR \<Longrightarrow> opPlus F G \<in> CR"
  and CR_comp: "F \<in> CR \<Longrightarrow> G \<in> CR \<Longrightarrow> F \<circ> G \<in> CR"
  using clos_binop[of opPlus basis_Robinson F G] clos_binop[of "(\<circ>)" basis_Robinson F G]
  by (simp_all add: basis_Robinson_def)

lemma C6_sub_CR: "C6 \<subseteq> CR"
proof (rule clos_subset)
  have I: "funI \<in> CR" using CR_box[OF CR_S] by (simp add: funI_eq_box_S)
  have "opBox funE x = 0" for x by (induct x) simp_all
  then have "cst 1 = funS \<circ> opBox funE" by (intro ext) (simp add: cst_def funS_def)
  then have "cst 1 \<in> CR" by (simp add: CR_comp CR_box CR_S CR_E)
  then show "inits basis_6 \<subseteq> CR" using CR_E by (simp add: basis_6_def)
  show "applyU u F \<in> CR" if "u \<in> unops basis_6" "F \<in> CR" for u F
  proof -
    have "opPlusI F = opPlus F funI" by (rule ext) (simp add: opPlusI_def opPlus_def funI_def)
    then show ?thesis using that I by (auto simp: basis_6_def applyU_def CR_plus CR_box)
  qed
  show "applyB b F G \<in> CR" if "b \<in> binops basis_6" "F \<in> CR" "G \<in> CR" for b F G
  proof -
    have "b = (\<circ>)" using that(1) by (simp add: basis_6_def)
    then show ?thesis using CR_comp[OF that(2,3)] by (simp only: applyB_def)
  qed
qed

subsection \<open>Robinson's theorem\<close>

theorem Robinson_1947_sec7_thm3_complete: "PrimNN \<subseteq> clos basis_Robinson"
  using PrimNN_sub_C6 C6_sub_CR by (rule order_trans)

theorem Robinson_1947_sec7_thm3: "suitable basis_Robinson"
  using Robinson_1947_sec7_thm3_complete Robinson_sound by (rule suitableI)

end
