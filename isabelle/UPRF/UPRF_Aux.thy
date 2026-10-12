(*  Title:   UPRF_Aux.thy
    Auxiliary arithmetic facts used by the formalization of
    D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Nothing here is stated in the paper: these are the elementary facts about
    \<lfloor>\<surd>x\<rfloor>, E, Cantor pairing, ... that the paper uses silently, plus the proofs
    that the functions and operators of the paper are primitive recursive
    (needed for the inclusion clos \<F> \<subseteq> Prim(\<nat>,\<nat>), which the paper leaves implicit).
*)

theory UPRF_Aux
  imports UPRF_Basis
begin

section \<open>Integer square root and excess over a square\<close>

lemma funRt_sq_le: "funRt n * funRt n \<le> n"
  using floor_sqrt_power2_le[of n] by (simp add: funRt_def power2_eq_square)

lemma funRt_sq_gt: "n < Suc (funRt n) * Suc (funRt n)"
  using Suc_floor_sqrt_power2_gt[of n] by (simp add: funRt_def power2_eq_square)

lemma funRt_unique:
  assumes "r * r \<le> n" and "n < Suc r * Suc r"
  shows "funRt n = r"
proof -
  have "r \<le> funRt n"
  proof (rule ccontr)
    assume "\<not> r \<le> funRt n"
    then have "Suc (funRt n) \<le> r" by simp
    then have "Suc (funRt n) * Suc (funRt n) \<le> r * r" by (intro mult_le_mono)
    with assms(1) funRt_sq_gt[of n] show False by simp
  qed
  moreover have "funRt n \<le> r"
  proof (rule ccontr)
    assume "\<not> funRt n \<le> r"
    then have "Suc r \<le> funRt n" by simp
    then have "Suc r * Suc r \<le> funRt n * funRt n" by (intro mult_le_mono)
    with assms(2) funRt_sq_le[of n] show False by simp
  qed
  ultimately show ?thesis by simp
qed

text \<open>\<open>\<lfloor>\<surd>(m\<^sup>2 + k)\<rfloor> = m\<close> and \<open>E(m\<^sup>2 + k) = k\<close> whenever \<open>k \<le> 2m\<close>.\<close>
lemma funRt_sq_add: "k \<le> 2 * m \<Longrightarrow> funRt (m * m + k) = m"
  by (rule funRt_unique) auto

lemma funE_sq_add: "k \<le> 2 * m \<Longrightarrow> funE (m * m + k) = k"
  by (simp add: funE_def funRt_sq_add power2_eq_square)

lemma funE_alt: "funE x = x - funRt x * funRt x"
  by (simp add: funE_def power2_eq_square)

lemma funRt_sq [simp]: "funRt (m * m) = m"
  using funRt_sq_add[of 0 m] by simp

lemma funE_le: "funE x \<le> x"
  by (simp add: funE_def)

text \<open>The square indicator.\<close>
lemma funQ_iff: "funQ x = (if funRt x * funRt x = x then 1 else 0)"
proof -
  have "(\<exists>k. x = k\<^sup>2) \<longleftrightarrow> funRt x * funRt x = x"
  proof
    assume "\<exists>k. x = k\<^sup>2"
    then obtain k where "x = k * k" by (auto simp: power2_eq_square)
    then show "funRt x * funRt x = x" by simp
  next
    assume "funRt x * funRt x = x"
    then show "\<exists>k. x = k\<^sup>2" by (metis power2_eq_square)
  qed
  then show ?thesis by (simp add: funQ_def)
qed

text \<open>Recursive description of \<open>\<lfloor>\<surd>x\<rfloor>\<close>.\<close>
lemma funRt_Suc:
  "funRt (Suc n) = (if Suc (funRt n) * Suc (funRt n) = Suc n then Suc (funRt n) else funRt n)"
proof (cases "Suc (funRt n) * Suc (funRt n) = Suc n")
  case True
  then show ?thesis by (simp del: mult_Suc mult_Suc_right) (metis funRt_sq)
next
  case False
  have "funRt n * funRt n \<le> Suc n" using funRt_sq_le[of n] by simp
  moreover have "Suc n < Suc (funRt n) * Suc (funRt n)"
    using funRt_sq_gt[of n] False by linarith
  ultimately show ?thesis using False by (simp add: funRt_unique del: mult_Suc mult_Suc_right)
qed

text \<open>Robinson's difference formula (used in Lemma 6.2):
  if \<open>\<alpha> \<ge> \<beta>\<close> then \<open>\<alpha> - \<beta> = E((\<alpha>+\<beta>)\<^sup>2 + 3\<alpha> + \<beta> + 1)\<close>.\<close>
lemma robinson_diff_E:
  assumes "\<beta> \<le> \<alpha>"
  shows "funE ((\<alpha> + \<beta>) * (\<alpha> + \<beta>) + 3 * \<alpha> + \<beta> + 1) = \<alpha> - \<beta>"
proof -
  have eq: "(\<alpha> + \<beta>) * (\<alpha> + \<beta>) + 3 * \<alpha> + \<beta> + 1 = (\<alpha> + \<beta> + 1) * (\<alpha> + \<beta> + 1) + (\<alpha> - \<beta>)"
    using assms by (simp add: algebra_simps)
  show ?thesis unfolding eq by (rule funE_sq_add) simp
qed

section \<open>Cantor pairing functions\<close>

text \<open>The paper's Cantor functions coincide with those of the AFP entry:
  \<open>A = sf\<close>, \<open>V = c_sum\<close>, \<open>J = c_pair\<close>, \<open>K = c_fst\<close>, \<open>L = c_snd\<close>.\<close>

lemma funA_eq_sf: "funA = sf"
  by (rule ext) (simp add: funA_def sf_def algebra_simps)

lemma c_sum_unique:
  assumes "sf t \<le> u" and "u < sf (Suc t)"
  shows "c_sum u = t"
proof -
  have "c_sum u < Suc t"
    using assms(2) arg_less_sf_imp_c_sum_less_arg[of u "Suc t"] by simp
  moreover have "\<not> c_sum u < t"
  proof
    assume "c_sum u < t"
    then have "sf (c_sum u + 1) \<le> sf t" by (intro sf_mono) simp
    with arg_less_sf_at_Suc_of_c_sum[of u] assms(1) show False by simp
  qed
  ultimately show ?thesis by simp
qed

lemma funV_eq_c_sum: "funV = c_sum"
proof
  fix x
  let ?t = "c_sum x"
  have lo: "sf ?t \<le> x" by (rule sf_c_sum_le_arg)
  have hi: "x < sf (Suc ?t)" using arg_less_sf_at_Suc_of_c_sum[of x] by simp
  have sf2: "2 * sf t = t * t + t" for t by (simp add: sf_def algebra_simps)
  have sfS: "sf (Suc t) = sf t + t + 1" for t using sf_at_Suc[of t] by simp
  have "(2 * ?t + 1) * (2 * ?t + 1) \<le> 8 * x + 1"
    using lo sf2[of ?t] by (simp add: algebra_simps)
  moreover have "8 * x + 1 < (2 * ?t + 3) * (2 * ?t + 3)"
    using hi sf2[of ?t] sfS[of ?t] by (simp add: algebra_simps)
  ultimately have "funRt (8 * x + 1) = 2 * ?t + 1 \<or> funRt (8 * x + 1) = 2 * ?t + 2"
  proof -
    assume a: "(2 * ?t + 1) * (2 * ?t + 1) \<le> 8 * x + 1" and b: "8 * x + 1 < (2 * ?t + 3) * (2 * ?t + 3)"
    show ?thesis
    proof (cases "(2 * ?t + 2) * (2 * ?t + 2) \<le> 8 * x + 1")
      case True
      then have "funRt (8 * x + 1) = 2 * ?t + 2" using b by (intro funRt_unique) (simp_all add: algebra_simps)
      then show ?thesis by simp
    next
      case False
      then have "funRt (8 * x + 1) = 2 * ?t + 1" using a by (intro funRt_unique) (simp_all add: algebra_simps)
      then show ?thesis by simp
    qed
  qed
  then show "funV x = c_sum x" by (auto simp: funV_def)
qed

lemma funK_eq_c_fst: "funK = c_fst"
  by (rule ext) (simp add: funK_def c_fst_def funA_eq_sf funV_eq_c_sum)

lemma funL_eq_c_snd: "funL = c_snd"
proof
  fix x
  have "sf (c_sum x) + c_fst x = x" by (rule sf_c_sum_plus_c_fst)
  moreover have "sf (Suc (c_sum x)) = sf (c_sum x) + c_sum x + 1" using sf_at_Suc[of "c_sum x"] by simp
  ultimately show "funL x = c_snd x"
    by (simp add: funL_def c_snd_def funA_eq_sf funV_eq_c_sum)
qed

lemma funJ_eq_c_pair: "funJ = c_pair"
  by (intro ext) (simp add: funJ_def c_pair_def funA_eq_sf)

text \<open>Values on a diagonal of the Cantor table: for \<open>k \<le> t\<close>, \<open>K(A(t)+k) = k\<close> and \<open>L(A(t)+k) = t-k\<close>.\<close>
lemma funK_diag: "k \<le> t \<Longrightarrow> funK (sf t + k) = k"
  using funK_eq_c_fst c_fst_of_c_pair[of k "t - k"] by (simp add: c_pair_def)

lemma funL_diag: "k \<le> t \<Longrightarrow> funL (sf t + k) = t - k"
  using funL_eq_c_snd c_snd_of_c_pair[of k "t - k"] by (simp add: c_pair_def)

lemma sf_Suc: "sf (Suc t) = sf t + t + 1"
  using sf_at_Suc[of t] by simp

lemma two_sf: "2 * sf t = t * t + t"
  by (simp add: sf_def algebra_simps)

text \<open>\<open>K(x) = 0\<close> iff \<open>x\<close> is a triangular number.\<close>
lemma funK_zero_iff: "funK x = 0 \<longleftrightarrow> (\<exists>t. x = sf t)"
proof
  assume "funK x = 0"
  then have "sf (c_sum x) = x" using sf_c_sum_plus_c_fst[of x] by (simp add: funK_eq_c_fst)
  then show "\<exists>t. x = sf t" by metis
next
  assume "\<exists>t. x = sf t"
  then obtain t where "x = sf t" by blast
  then show "funK x = 0" using funK_diag[of 0 t] by simp
qed

section \<open>Primitive recursiveness of the functions and operators of the paper\<close>

lemma funS_PR: "funS \<in> PrimNN"
proof -
  have "funS = Suc" by (rule ext) (simp add: funS_def)
  then show ?thesis using pr_suc by simp
qed

lemma cst_PR: "cst n \<in> PrimNN"
  unfolding cst_def using const_is_pr[of n] by simp

lemma funI_PR: "funI \<in> PrimNN"
  unfolding funI_def using pr_id1_1 by simp

lemma funSq_PR: "funSq \<in> PrimNN"
  unfolding funSq_def by prec

lemma funO_PR: "funO \<in> PrimNN"
proof -
  have "funO = sgn2" by (rule ext) (simp add: funO_def sgn2_def split: nat.split)
  then show ?thesis using sgn2_is_pr by simp
qed

lemma funHf_PR: "funHf \<in> PrimNN"
proof (rule pr_rec1_scheme[where h = "\<lambda>y r. if r + r = y then r else r + 1" and a = 0])
  show "(\<lambda>y r. if r + r = y then r else r + 1) \<in> PrimRec2" by prec
  show "funHf 0 = 0" by (simp add: funHf_def)
  show "\<forall>y. funHf (Suc y) = (if funHf y + funHf y = y then funHf y else funHf y + 1)"
    by (simp add: funHf_def) presburger
qed

lemma funRt_PR: "funRt \<in> PrimNN"
proof (rule pr_rec1_scheme[where h = "\<lambda>y r. if (r + 1) * (r + 1) = y + 1 then r + 1 else r" and a = 0])
  show "(\<lambda>y r. if (r + 1) * (r + 1) = y + 1 then r + 1 else r) \<in> PrimRec2" by prec
  show "funRt 0 = 0" using funRt_sq[of 0] by simp
  show "\<forall>y. funRt (Suc y) = (if (funRt y + 1) * (funRt y + 1) = y + 1 then funRt y + 1 else funRt y)"
    using funRt_Suc by simp
qed

lemma funE_PR: "funE \<in> PrimNN"
proof -
  have "(\<lambda>x. x - funRt x * funRt x) \<in> PrimRec1"
    using funRt_PR by prec
  then show ?thesis by (simp add: funE_alt[abs_def])
qed

lemma funK_PR: "funK \<in> PrimNN"
  using c_fst_is_pr by (simp add: funK_eq_c_fst)

lemma funL_PR: "funL \<in> PrimNN"
  using c_snd_is_pr by (simp add: funL_eq_c_snd)

lemma comp_PR: "F \<in> PrimNN \<Longrightarrow> G \<in> PrimNN \<Longrightarrow> F \<circ> G \<in> PrimNN"
  using pr_comp1_1[of F G] by (simp add: comp_def)

lemma opPlus_PR: "F \<in> PrimNN \<Longrightarrow> G \<in> PrimNN \<Longrightarrow> opPlus F G \<in> PrimNN"
  unfolding opPlus_def by prec

text \<open>A pointwise binary operator built from a binary primitive recursive function \<open>d\<close>.\<close>
definition opPointwise :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bop" where
  "opPointwise d F G x = d (F x) (G x)"

lemma opPointwise_PR:
  "d \<in> PrimRec2 \<Longrightarrow> F \<in> PrimNN \<Longrightarrow> G \<in> PrimNN \<Longrightarrow> opPointwise d F G \<in> PrimNN"
  unfolding opPointwise_def by (rule pr_comp2_1)

lemma opBoxA_PR: "F \<in> PrimNN \<Longrightarrow> opBoxA a F \<in> PrimNN"
proof (rule pr_rec1_scheme[where h = "\<lambda>y r. F r" and a = a])
  assume "F \<in> PrimNN"
  then show "(\<lambda>y r. F r) \<in> PrimRec2" by prec
qed simp_all

lemma opBox_PR: "F \<in> PrimNN \<Longrightarrow> opBox F \<in> PrimNN"
  unfolding opBox_def by (rule opBoxA_PR)

end
