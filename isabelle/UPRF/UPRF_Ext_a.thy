(*  Title:   UPRF_Ext_a.thy

    Extension of Remark 6.9 of Severin (JSL 2008) to iteration from any fixed a \<ge> 2,
    answering the question left open at the end of Section 6:

       \<langle>X, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<rangle> is suitable for every a \<ge> 2 and X \<in> {E, K, L}.

    Together with Remark 6.9 (a = 1) this covers every a \<ge> 1.
*)

theory UPRF_Ext_a
  imports UPRF_Sec6_Rem69
begin

section \<open>Iteration from an arbitrary \<open>a \<ge> 2\<close>\<close>

subsection \<open>General facts\<close>

text \<open>The bases \<open>\<langle>X, F\<^sup>+, FG, F\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<rangle>\<close>.\<close>
definition basis_a :: "ufun \<Rightarrow> nat \<Rightarrow> basis" where
  "basis_a X a = Basis {X} {opPlusI, opBoxA a} {(\<circ>)}"

lemma basis_69_eq: "basis_69_I = basis_a funE 1" "basis_69_II = basis_a funK 1" "basis_69_III = basis_a funL 1"
  by (simp_all add: basis_69_I_def basis_69_II_def basis_69_III_def basis_a_def)

lemma Ca_X: "X \<in> clos (basis_a X a)"
  by (rule clos_init) (simp add: basis_a_def)

lemma Ca_plusI: "F \<in> clos (basis_a X a) \<Longrightarrow> opPlusI F \<in> clos (basis_a X a)"
  and Ca_boxA: "F \<in> clos (basis_a X a) \<Longrightarrow> opBoxA a F \<in> clos (basis_a X a)"
  using clos_unop[of opPlusI "basis_a X a" F] clos_unop[of "opBoxA a" "basis_a X a" F]
  by (simp_all add: basis_a_def)

lemma Ca_comp: "F \<in> clos (basis_a X a) \<Longrightarrow> G \<in> clos (basis_a X a) \<Longrightarrow> F \<circ> G \<in> clos (basis_a X a)"
  using clos_binop[of "(\<circ>)" "basis_a X a" F G] by (simp add: basis_a_def)

text \<open>Finite powers \<open>F\<^sup>k G\<close> (composition) stay in any closure containing \<open>(\<circ>)\<close>.\<close>
lemma clos_powcomp:
  assumes c: "(\<circ>) \<in> binops B" and F: "F \<in> clos B" and G: "G \<in> clos B"
  shows "(F ^^ k) \<circ> G \<in> clos B"
proof (induct k)
  case 0 then show ?case using G by simp
next
  case (Suc k)
  have eq: "(F ^^ Suc k) \<circ> G = F \<circ> ((F ^^ k) \<circ> G)" by (simp only: funpow.simps(2) comp_assoc)
  show ?case unfolding eq by (rule clos_binop[OF c F Suc])
qed

lemma Ca_powcomp: "F \<in> clos (basis_a X a) \<Longrightarrow> G \<in> clos (basis_a X a) \<Longrightarrow> (F ^^ k) \<circ> G \<in> clos (basis_a X a)"
  by (rule clos_powcomp) (simp_all add: basis_a_def)

lemmas Ca_intros = Ca_X Ca_plusI Ca_boxA Ca_comp Ca_powcomp

lemma comp_funI [simp]: "G \<circ> funI = G"
  by (rule ext) (simp add: funI_def)

lemma funS_pow: "(funS ^^ k) x = x + k"
  by (induct k) (simp_all add: funS_def)

lemma shift_pow: "(\<And>y. F y = y + c) \<Longrightarrow> (F ^^ k) x = x + k * c"
  by (induct k) simp_all

text \<open>A predecessor (\<open>P(x + 1) = x\<close>) undoes \<open>k\<close> successors.\<close>
lemma pred_pow:
  assumes "\<And>x. P (Suc x) = x"
  shows "(P ^^ k) (x + k) = x"
  by (induct k arbitrary: x) (simp_all add: assms funpow_Suc_right del: funpow.simps)

text \<open>Recovering iteration from \<open>0\<close> out of iteration from \<open>a\<close> (as in Remark 5.10 of the paper):
  \<open>F\<^sup>\<box> \<equiv> P\<^sup>a (S\<^sup>a F P\<^sup>a)\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close>.\<close>
lemma box_from_boxA:
  assumes P: "\<And>x. P (Suc x) = x"
  shows "(P ^^ a) \<circ> opBoxA a ((funS ^^ a) \<circ> F \<circ> (P ^^ a)) = opBox F"
proof
  have aux: "opBoxA a ((funS ^^ a) \<circ> F \<circ> (P ^^ a)) n = opBox F n + a" for n
    by (induct n) (simp_all add: funS_pow pred_pow[OF P])
  fix n show "((P ^^ a) \<circ> opBoxA a ((funS ^^ a) \<circ> F \<circ> (P ^^ a))) n = opBox F n"
    by (simp add: aux pred_pow[OF P])
qed

text \<open>\<open>M\<^sub>r \<equiv> (\<dots>(\<overline>0\<^sup>+)\<^sup>+\<dots>)\<^sup>+\<close> (\<open>r\<close> times), i.e. \<open>M\<^sub>r(x) = rx\<close>.\<close>
definition funM :: "nat \<Rightarrow> ufun" where "funM r = (opPlusI ^^ r) (cst 0)"

lemma funM_apply: "funM r x = r * x"
  by (induct r) (simp_all add: funM_def opPlusI_def cst_def)

text \<open>The chain \<open>N = T\<^sub>2 T\<^sub>3 \<cdots> T\<^sub>k\<^sub>+\<^sub>1\<close>.\<close>
primrec Nchain :: "(nat \<Rightarrow> ufun) \<Rightarrow> nat \<Rightarrow> ufun" where
  "Nchain T 0 = funI"
| "Nchain T (Suc k) = Nchain T k \<circ> T (k + 2)"

lemma Nchain_val:
  assumes "\<And>j. 2 \<le> j \<Longrightarrow> T j j = j - 1" and "\<And>j. 2 \<le> j \<Longrightarrow> T j 0 = 0"
  shows "Nchain T k (Suc k) = 1" "Nchain T k 0 = 0"
proof -
  show "Nchain T k (Suc k) = 1"
  proof (induct k)
    case 0 then show ?case by (simp add: funI_def)
  next
    case (Suc k)
    have "T (k + 2) (Suc (Suc k)) = Suc k" using assms(1)[of "k + 2"] by simp
    then show ?case using Suc by simp
  qed
  show "Nchain T k 0 = 0" by (induct k) (simp_all add: funI_def assms(2))
qed

subsection \<open>The common part of the three cases\<close>

text \<open>Data: the initial function \<open>X\<close>, the starting value \<open>a \<ge> 2\<close>, and multipliers \<open>m\<close> with
  \<open>X(m(j) \<cdot> j) = j - 1\<close>, so that \<open>T\<^sub>j \<equiv> X M\<^sub>m\<^sub>(\<^sub>j\<^sub>)\<close> maps \<open>j\<close> to \<open>j - 1\<close>.\<close>
locale ext_a =
  fixes X :: ufun and a :: nat and m :: "nat \<Rightarrow> nat"
  assumes a2: "2 \<le> a"
    and zero_in: "cst 0 \<in> clos (basis_a X a)"
    and X0: "X 0 = 0"
    and Xm: "\<And>j. 2 \<le> j \<Longrightarrow> X (m j * j) = j - 1"
begin

abbreviation Ca :: "ufun set" where "Ca \<equiv> clos (basis_a X a)"

definition T :: "nat \<Rightarrow> ufun" where "T j = X \<circ> funM (m j)"

lemma M_in: "funM r \<in> Ca"
  unfolding funM_def by (induct r) (simp_all add: zero_in Ca_plusI)

lemma I_in: "funI \<in> Ca"
proof -
  have "funM 1 = funI" by (rule ext) (simp add: funM_apply funI_def)
  then show ?thesis using M_in[of 1] by simp
qed

lemma D_in: "funD \<in> Ca"
proof -
  have "funM 2 = funD" by (rule ext) (simp add: funM_apply funD_def)
  then show ?thesis using M_in[of 2] by simp
qed

lemma T_in: "T j \<in> Ca" unfolding T_def by (intro Ca_comp Ca_X M_in)

lemma T_val: "2 \<le> j \<Longrightarrow> T j j = j - 1" "T j 0 = 0"
  by (simp_all add: T_def funM_apply Xm X0)

lemma pow_in: "F \<in> Ca \<Longrightarrow> F ^^ k \<in> Ca"
  using Ca_powcomp[of F X a funI k] I_in by simp

lemma Nchain_in: "Nchain T k \<in> Ca"
proof (induct k)
  case 0 show ?case by (simp add: I_in)
next
  case (Suc k) show ?case by (simp only: Nchain.simps) (rule Ca_comp[OF Suc T_in])
qed

text \<open>The constant \<open>a\<close> is \<open>I\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close>, and \<open>\<overline>1 \<equiv> N \<overline>a\<close> with \<open>N = T\<^sub>2 \<cdots> T\<^sub>a\<close>.\<close>
lemma const_a_expr: "opBoxA a funI = cst a"
proof
  fix n show "opBoxA a funI n = cst a n" by (induct n) (simp_all add: funI_def cst_def)
qed

lemma one_expr: "Nchain T (a - 1) \<circ> cst a = cst 1"
proof
  fix x
  have "Suc (a - 1) = a" using a2 by simp
  then show "(Nchain T (a - 1) \<circ> cst a) x = cst 1 x"
    using Nchain_val(1)[of T "a - 1", OF T_val] by (simp add: cst_def)
qed

text \<open>Cosignum: \<open>O \<equiv> N \<overline>0\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close> (the iteration of \<open>\<overline>0\<close> from \<open>a\<close> has values \<open>a, 0, 0, \<dots>\<close>).\<close>
lemma O_expr_a: "Nchain T (a - 1) \<circ> opBoxA a (cst 0) = funO"
proof
  fix n
  have Suc_a: "Suc (a - 1) = a" using a2 by simp
  show "(Nchain T (a - 1) \<circ> opBoxA a (cst 0)) n = funO n"
  proof (cases n)
    case 0 then show ?thesis
      using Nchain_val(1)[of T "a - 1", OF T_val] Suc_a by (simp add: funO_def)
  next
    case (Suc k) then show ?thesis
      using Nchain_val(2)[of T "a - 1", OF T_val] by (simp add: funO_def cst_def)
  qed
qed

lemma one_in: "cst 1 \<in> Ca"
  unfolding one_expr[symmetric] const_a_expr[symmetric] by (intro Ca_comp Ca_boxA Nchain_in I_in)

lemma S_in: "funS \<in> Ca" unfolding S_expr[symmetric] by (intro Ca_plusI one_in)

lemma O_in: "funO \<in> Ca"
  unfolding O_expr_a[symmetric] by (intro Ca_comp Ca_boxA Nchain_in zero_in)

text \<open>With any predecessor in the closure, iteration from \<open>0\<close> is available.\<close>
lemma box_in:
  assumes P_in: "P \<in> Ca" and P: "\<And>x. P (Suc x) = x" and F: "F \<in> Ca"
  shows "opBox F \<in> Ca"
proof -
  have "(P ^^ a) \<circ> opBoxA a ((funS ^^ a) \<circ> F \<circ> (P ^^ a)) \<in> Ca"
    by (intro Ca_comp Ca_boxA pow_in S_in F P_in)
  then show ?thesis by (simp only: box_from_boxA[OF P])
qed

end

subsection \<open>The case \<open>X = E\<close>\<close>

lemma le_funRt:
  assumes "k * k \<le> n" shows "k \<le> funRt n"
proof (rule ccontr)
  assume "\<not> k \<le> funRt n"
  then have h: "Suc (funRt n) \<le> k" by linarith
  have "Suc (funRt n) * Suc (funRt n) \<le> k * k" by (rule mult_le_mono[OF h h])
  with assms funRt_sq_gt[of n] show False by linarith
qed

lemma funE_less: "0 < y \<Longrightarrow> funE y < y"
proof -
  assume "0 < y"
  then have "1 * 1 \<le> y" by simp
  then have h: "1 \<le> funRt y" by (rule le_funRt)
  have "1 * 1 \<le> funRt y * funRt y" by (rule mult_le_mono[OF h h])
  moreover have "funRt y * funRt y \<le> y" by (rule funRt_sq_le)
  ultimately show ?thesis by (simp add: funE_alt)
qed

text \<open>For a function \<open>X\<close> with \<open>X(0) = 0\<close> and \<open>X(y) < y\<close> for \<open>y > 0\<close>:
  \<open>\<overline>0 \<equiv> X\<^sup>a X\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close>.\<close>
lemma decreasing_zero:
  assumes X0: "X 0 = 0" and Xlt: "\<And>y. 0 < y \<Longrightarrow> X y < y"
  shows "(X ^^ a) \<circ> opBoxA a X = cst 0"
proof
  have le: "opBoxA a X n \<le> a" for n
  proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n) then show ?case using X0 Xlt[of "opBoxA a X n"] by (cases "opBoxA a X n = 0") auto
  qed
  have pow: "y \<le> k \<Longrightarrow> (X ^^ k) y = 0" for y k
  proof (induct k arbitrary: y)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have "X y \<le> k" using Suc.prems X0 Xlt[of y] by (cases "y = 0") auto
    then show ?case using Suc.hyps by (simp add: funpow_Suc_right del: funpow.simps)
  qed
  fix n show "((X ^^ a) \<circ> opBoxA a X) n = cst 0 n" by (simp add: pow le cst_def)
qed

lemma zero_in_E: "cst 0 \<in> clos (basis_a funE a)"
proof -
  have "(funE ^^ a) \<circ> opBoxA a funE \<in> clos (basis_a funE a)" by (rule Ca_powcomp[OF Ca_X Ca_boxA[OF Ca_X]])
  then show ?thesis by (simp only: decreasing_zero[OF funE_small(1) funE_less])
qed

lemma Xm_E: "2 \<le> j \<Longrightarrow> funE ((j - 1) * j) = j - 1"
proof -
  assume "2 \<le> j"
  then have "(j - 1) * j = (j - 1) * (j - 1) + (j - 1)" by (cases j) (simp_all add: algebra_simps)
  then show ?thesis by (simp add: funE_sq_add)
qed

lemma locE: "2 \<le> a \<Longrightarrow> ext_a funE a (\<lambda>j. j - 1)"
  by (unfold_locales) (simp_all add: zero_in_E Xm_E)

text \<open>The construction for \<open>E\<close>: with \<open>c = a\<^sup>2 + a + 4\<close>,
  \<open>B \<equiv> (S (D Q S\<^sup>c)\<^sup>+)\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close> satisfies \<open>B(n) + a\<^sup>2 + a = R(n + a\<^sup>2)\<close>, i.e. \<open>B(n) = n + 2\<lfloor>\<surd>(n + a\<^sup>2)\<rfloor> - a\<close>;
  \<open>G \<equiv> (S\<^sup>a\<^sup>+\<^sup>1 B)\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close> satisfies \<open>G(n) = n\<^sup>2 + 2an + a\<close>; and \<open>P \<equiv> E S\<^sup>d G\<^sup>+\<close>, \<open>d = a\<^sup>2 - a - 1\<close>,
  is a predecessor.\<close>
definition HE :: "nat \<Rightarrow> ufun" where
  "HE a = funS \<circ> opPlusI (funD \<circ> funQ \<circ> (funS ^^ (a * a + a + 4)))"
definition BE :: "nat \<Rightarrow> ufun" where "BE a = opBoxA a (HE a)"
definition GE :: "nat \<Rightarrow> ufun" where "GE a = opBoxA a ((funS ^^ (a + 1)) \<circ> BE a)"
definition PE :: "nat \<Rightarrow> ufun" where "PE a = funE \<circ> (funS ^^ (a * a - a - 1)) \<circ> opPlusI (GE a)"

lemma R_rec: "funR (Suc t) = 2 * funQ (funR t + 4) + funR t + 1"
proof -
  have "funR (Suc t) = opPlusI (funD \<circ> funQ \<circ> funS \<circ> funS \<circ> funS) (funS (funR t))"
    by (rule R_step[symmetric])
  also have "\<dots> = 2 * funQ (funR t + 4) + funR t + 1"
    by (simp add: opPlusI_def funD_def funS_def numeral_eq_Suc)
  finally show ?thesis .
qed

lemma HE_val: "HE a y = 2 * funQ (y + (a * a + a + 4)) + y + 1"
  by (simp add: HE_def opPlusI_def funD_def funS_pow funS_def)

lemma BE_val: "BE a n + a * a + a = funR (n + a * a)"
proof (induct n)
  case 0
  have "funR (a * a) = a * a + 2 * a" by (simp add: funR_def)
  then show ?case by (simp add: BE_def)
next
  case (Suc n)
  have arg: "BE a n + (a * a + a + 4) = funR (n + a * a) + 4" using Suc by simp
  have "BE a (Suc n) = HE a (BE a n)" by (simp add: BE_def)
  also have "\<dots> = 2 * funQ (funR (n + a * a) + 4) + BE a n + 1" by (simp only: HE_val arg)
  finally have "BE a (Suc n) + a * a + a = 2 * funQ (funR (n + a * a) + 4) + funR (n + a * a) + 1"
    using Suc by simp
  also have "\<dots> = funR (Suc n + a * a)" using R_rec[of "n + a * a"] by simp
  finally show ?case .
qed

lemma GE_val: "GE a n = n * n + 2 * a * n + a"
proof (induct n)
  case 0 then show ?case by (simp add: GE_def)
next
  case (Suc n)
  let ?g = "n * n + 2 * a * n + a"
  have rt: "funRt (?g + a * a) = n + a"
  proof -
    have eq: "?g + a * a = (n + a) * (n + a) + a" by (simp add: algebra_simps)
    show ?thesis unfolding eq by (rule funRt_sq_add) simp
  qed
  have "BE a ?g + a * a + a = ?g + a * a + 2 * (n + a)" using BE_val[of a ?g] rt by (simp add: funR_def)
  then have b: "BE a ?g = n * n + 2 * a * n + 2 * n + 2 * a" by (simp add: algebra_simps)
  have "GE a (Suc n) = BE a ?g + (a + 1)" using Suc by (simp add: GE_def funS_pow)
  also have "\<dots> = Suc n * Suc n + 2 * a * Suc n + a" by (simp only: b) (simp add: algebra_simps)
  finally show ?case .
qed

lemma PE_Suc:
  assumes "2 \<le> a" shows "PE a (Suc k) = k"
proof -
  define d where "d = a * a - a - 1"
  have aa: "a * a = d + a + 1"
  proof -
    have "2 * a \<le> a * a" using assms by (simp add: mult_le_mono1)
    then show ?thesis using assms unfolding d_def by arith
  qed
  have "PE a (Suc k) = funE (GE a (Suc k) + Suc k + d)"
    by (simp add: PE_def opPlusI_def funS_pow d_def algebra_simps)
  also have "GE a (Suc k) + Suc k + d = (Suc k + a) * (Suc k + a) + k"
    using aa by (simp add: GE_val algebra_simps)
  also have "funE \<dots> = k" by (rule funE_sq_add) simp
  finally show ?thesis .
qed

lemma PE_in: "2 \<le> a \<Longrightarrow> PE a \<in> clos (basis_a funE a)"
proof -
  assume a: "2 \<le> a"
  note L = locE[OF a]
  have Q: "funQ \<in> clos (basis_a funE a)"
    unfolding Q_expr[symmetric] by (intro Ca_comp Ca_X ext_a.O_in[OF L])
  have "HE a \<in> clos (basis_a funE a)"
    unfolding HE_def by (intro Ca_comp Ca_plusI ext_a.S_in[OF L] ext_a.D_in[OF L] Q ext_a.pow_in[OF L])
  then have "GE a \<in> clos (basis_a funE a)"
    unfolding GE_def BE_def by (intro Ca_boxA Ca_comp ext_a.pow_in[OF L] ext_a.S_in[OF L])
  then show ?thesis
    unfolding PE_def by (intro Ca_comp Ca_X Ca_plusI ext_a.pow_in[OF L] ext_a.S_in[OF L])
qed

theorem Ext_a_E: assumes "2 \<le> a" shows "suitable (basis_a funE a)"
proof (rule suitable_by_simulation[OF Theorem_6_7])
  let ?C = "clos (basis_a funE a)"
  have P: "\<And>x. PE a (Suc x) = x" using PE_Suc[OF assms] .
  note L = locE[OF assms]
  show "inits basis_6 \<subseteq> ?C" using ext_a.one_in[OF L] Ca_X by (simp add: basis_6_def)
  show "applyU u F \<in> ?C" if "u \<in> unops basis_6" "F \<in> ?C" for u F
    using that Ca_plusI ext_a.box_in[OF L PE_in[OF assms] P] by (auto simp: basis_6_def applyU_def)
  show "applyB b F G \<in> ?C" if "b \<in> binops basis_6" "F \<in> ?C" "G \<in> ?C" for b F G
    using that Ca_comp[of F funE a G] by (simp add: basis_6_def applyB_def comp_def)
  show "?C \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_a_def applyU_def applyB_def funE_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

subsection \<open>The case \<open>X = K\<close>\<close>

lemma zero_in_K: "cst 0 \<in> clos (basis_a funK a)"
proof -
  have lt: "\<And>y. 0 < y \<Longrightarrow> funK y < y" using c_fst_less_arg by (simp add: funK_eq_c_fst)
  have dz: "(funK ^^ a) \<circ> opBoxA a funK = cst 0" by (rule decreasing_zero[OF funK_0 lt])
  have "(funK ^^ a) \<circ> opBoxA a funK \<in> clos (basis_a funK a)" by (rule Ca_powcomp[OF Ca_X Ca_boxA[OF Ca_X]])
  then show ?thesis by (simp only: dz)
qed

lemma Xm_K: "2 \<le> j \<Longrightarrow> funK ((2 * j - 2) * j) = j - 1"
proof -
  assume "2 \<le> j"
  then obtain i where j: "j = Suc i" by (cases j) auto
  have eq: "(2 * j - 2) * j = sf (2 * i) + i" using two_sf[of "2 * i"] j by (simp add: algebra_simps)
  show ?thesis unfolding eq using funK_diag[of i "2 * i"] j by simp
qed

lemma locK: "2 \<le> a \<Longrightarrow> ext_a funK a (\<lambda>j. 2 * j - 2)"
  by (unfold_locales) (simp_all add: zero_in_K Xm_K funK_0)

text \<open>The construction for \<open>K\<close>: with \<open>c = A(a)\<close>, \<open>B \<equiv> (S\<^sup>2 (K S\<^sup>c)\<^sup>+)\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close> satisfies
  \<open>B(n) + A(a) + 1 = A(n + a + 1)\<close>, and \<open>P \<equiv> K S\<^sup>c B\<^sup>+\<close> is a predecessor.\<close>
definition BK :: "nat \<Rightarrow> ufun" where
  "BK a = opBoxA a ((funS ^^ 2) \<circ> opPlusI (funK \<circ> (funS ^^ sf a)))"
definition PK :: "nat \<Rightarrow> ufun" where "PK a = funK \<circ> (funS ^^ sf a) \<circ> opPlusI (BK a)"

lemma BK_val: "BK a n + sf a + 1 = sf (Suc (n + a))"
proof (induct n)
  case 0 then show ?case using sf_Suc[of a] by (simp add: BK_def)
next
  case (Suc n)
  have arg: "BK a n + sf a = sf (n + a) + (n + a)" using Suc sf_Suc[of "n + a"] by simp
  have k: "funK (BK a n + sf a) = n + a" unfolding arg by (rule funK_diag) simp
  have "BK a (Suc n) = funK (BK a n + sf a) + BK a n + 2"
    by (simp add: BK_def opPlusI_def funS_pow)
  then show ?case using k Suc sf_Suc[of "Suc (n + a)"] by simp
qed

lemma PK_Suc: "PK a (Suc k) = k"
proof -
  have "PK a (Suc k) = funK (BK a (Suc k) + Suc k + sf a)"
    by (simp add: PK_def opPlusI_def funS_pow algebra_simps)
  also have "BK a (Suc k) + Suc k + sf a = sf (Suc (Suc (k + a))) + k"
    using BK_val[of a "Suc k"] by simp
  also have "funK \<dots> = k" by (rule funK_diag) simp
  finally show ?thesis .
qed

lemma PK_in: "2 \<le> a \<Longrightarrow> PK a \<in> clos (basis_a funK a)"
proof -
  assume a: "2 \<le> a"
  note L = locK[OF a]
  have "BK a \<in> clos (basis_a funK a)"
    unfolding BK_def by (intro Ca_boxA Ca_comp Ca_plusI Ca_X ext_a.pow_in[OF L] ext_a.S_in[OF L])
  then show ?thesis
    unfolding PK_def by (intro Ca_comp Ca_X Ca_plusI ext_a.pow_in[OF L] ext_a.S_in[OF L])
qed

theorem Ext_a_K: assumes "2 \<le> a" shows "suitable (basis_a funK a)"
proof (rule suitable_by_simulation[OF Theorem_6_8_K])
  let ?C = "clos (basis_a funK a)"
  note L = locK[OF assms]
  show "inits basis_6K \<subseteq> ?C" using ext_a.one_in[OF L] Ca_X by (simp add: basis_6K_def)
  show "applyU u F \<in> ?C" if "u \<in> unops basis_6K" "F \<in> ?C" for u F
    using that Ca_plusI ext_a.box_in[OF L PK_in[OF assms] PK_Suc] by (auto simp: basis_6K_def applyU_def)
  show "applyB b F G \<in> ?C" if "b \<in> binops basis_6K" "F \<in> ?C" "G \<in> ?C" for b F G
    using that Ca_comp[of F funK a G] by (simp add: basis_6K_def applyB_def comp_def)
  show "?C \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_a_def applyU_def applyB_def funK_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

subsection \<open>The case \<open>X = L\<close>\<close>

text \<open>\<open>\<overline>0 \<equiv> L L\<^sup>+\<close>, because \<open>L(x + L(x)) = 0\<close>.\<close>
lemma zero_expr_L: "funL \<circ> opPlusI funL = cst 0"
proof
  fix x
  let ?t = "c_sum x" and ?k = "funK x"
  have x: "x = sf ?t + ?k" using sf_c_sum_plus_c_fst[of x] by (simp add: funK_eq_c_fst)
  have k: "?k \<le> ?t" using c_fst_le_c_sum[of x] by (simp add: funK_eq_c_fst)
  have "funL x = ?t - ?k" using funL_diag[OF k] x by simp
  then have e: "funL x + x = sf ?t + ?t" using x k by simp
  show "(funL \<circ> opPlusI funL) x = cst 0 x"
    by (simp only: comp_apply opPlusI_def e) (simp add: funL_diag cst_def)
qed

lemma zero_in_L: "cst 0 \<in> clos (basis_a funL a)"
  unfolding zero_expr_L[symmetric] by (intro Ca_comp Ca_X Ca_plusI)

lemma Xm_L: "2 \<le> j \<Longrightarrow> funL (2 * j * j) = j - 1"
proof -
  assume "2 \<le> j"
  then obtain i where j: "j = Suc i" by (cases j) auto
  have eq: "2 * j * j = sf (2 * i + 1) + (i + 1)" using two_sf[of "2 * i + 1"] j by (simp add: algebra_simps)
  show ?thesis unfolding eq using funL_diag[of "i + 1" "2 * i + 1"] j by simp
qed

lemma funL_0: "funL 0 = 0" using funL_eq_c_snd c_snd_at_0 by simp

lemma locL: "2 \<le> a \<Longrightarrow> ext_a funL a (\<lambda>j. 2 * j)"
  by (unfold_locales) (simp_all add: zero_in_L Xm_L funL_0)

text \<open>\<open>K \<equiv> L \<overline>1\<^sup>+ ((\<overline>1\<^sup>+)\<^sup>+ L)\<^sup>+\<close> as in Theorem 6.8, so the case of \<open>L\<close> reduces to that of \<open>K\<close>.\<close>
lemma K_in_La: "2 \<le> a \<Longrightarrow> funK \<in> clos (basis_a funL a)"
  unfolding K_expr_L[symmetric] by (intro Ca_comp Ca_plusI Ca_X ext_a.one_in[OF locL])

theorem Ext_a_L: assumes "2 \<le> a" shows "suitable (basis_a funL a)"
proof (rule suitable_by_simulation[OF Ext_a_K[OF assms]])
  let ?C = "clos (basis_a funL a)"
  show "inits (basis_a funK a) \<subseteq> ?C" using K_in_La[OF assms] by (simp add: basis_a_def)
  show "applyU u F \<in> ?C" if "u \<in> unops (basis_a funK a)" "F \<in> ?C" for u F
    using that Ca_plusI Ca_boxA by (auto simp: basis_a_def applyU_def)
  show "applyB b F G \<in> ?C" if "b \<in> binops (basis_a funK a)" "F \<in> ?C" "G \<in> ?C" for b F G
    using that Ca_comp[of F funL a G] by (simp add: basis_a_def applyB_def comp_def)
  show "?C \<subseteq> PrimNN"
    by (rule clos_sound)
       (auto simp: basis_a_def applyU_def applyB_def funL_PR
             intro: opPlusI_PR opBoxA_PR comp_PR pr_comp1_1)
qed

subsection \<open>Every starting value \<open>a \<ge> 1\<close>\<close>

theorem Ext_a_all:
  assumes "1 \<le> a" and "X \<in> {funE, funK, funL}"
  shows "suitable (basis_a X a)"
proof (cases "a = 1")
  case True
  then show ?thesis
    using assms(2) Remark_6_9_I Remark_6_9_II Remark_6_9_III by (auto simp: basis_69_eq)
next
  case False
  then have "2 \<le> a" using assms(1) by simp
  then show ?thesis using assms(2) Ext_a_E Ext_a_K Ext_a_L by auto
qed

end
