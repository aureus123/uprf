(*  Title:   UPRF_Basis.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Bases and closures (end of Section 2) and suitability (Definition 3.2).
    Only one-argument bases are needed for Section 6, i.e. bases
       \<langle>F\<^sub>1, ..., F\<^sub>n, F\<^sup>\<oplus>, ..., F \<otimes> G, ...\<rangle>
    made of initial one-argument functions, unary operators and binary
    operators on one-argument functions.
*)

theory UPRF_Basis
  imports UPRF_Sec2_Notation
begin

section \<open>Bases and closures\<close>

text \<open>A basis \<open>\<langle>F\<^sub>1,\<dots>,F\<^sub>n, F\<^sup>\<oplus>,\<dots>, F \<otimes> G,\<dots>\<rangle>\<close>: initial functions, unary operators, binary operators.\<close>
datatype basis = Basis (inits: "ufun set") (unops: "uop set") (binops: "bop set")

text \<open>Application of an operator of a basis to functions.  \<open>applyU u F\<close> is just \<open>u F\<close>; the
  constant is used in the general closure lemmas below only for a technical reason: it keeps
  Isabelle's unification first-order when the operator \<open>u\<close> is itself a variable.\<close>
definition applyU :: "uop \<Rightarrow> ufun \<Rightarrow> ufun" where "applyU u F = u F"
definition applyB :: "bop \<Rightarrow> ufun \<Rightarrow> ufun \<Rightarrow> ufun" where "applyB b F G = b F G"

text \<open>A set of functions is closed under the basis \<open>B\<close> if it contains the initial functions
  and is closed under its operators.\<close>
definition closed_under :: "basis \<Rightarrow> ufun set \<Rightarrow> bool" where
  "closed_under B X \<longleftrightarrow> inits B \<subseteq> X
     \<and> (\<forall>u \<in> unops B. \<forall>F \<in> X. applyU u F \<in> X)
     \<and> (\<forall>b \<in> binops B. \<forall>F \<in> X. \<forall>G \<in> X. applyB b F G \<in> X)"

text \<open>\<open>clos \<F>\<close>: the closure of the basis \<open>\<F>\<close>, i.e. the least set closed under it.\<close>
definition clos :: "basis \<Rightarrow> ufun set" where
  "clos B = \<Inter> {X. closed_under B X}"

lemma clos_init:
  assumes "F \<in> inits B" shows "F \<in> clos B"
  unfolding clos_def
proof (rule InterI)
  fix X assume "X \<in> {X. closed_under B X}"
  then have "inits B \<subseteq> X" by (simp add: closed_under_def)
  then show "F \<in> X" using assms by (rule subsetD)
qed

lemma clos_unop_app:
  assumes u: "u \<in> unops B" and F: "F \<in> clos B" shows "applyU u F \<in> clos B"
  unfolding clos_def
proof (rule InterI)
  fix X assume cX: "X \<in> {X. closed_under B X}"
  then have FX: "F \<in> X" using F unfolding clos_def by (rule InterD[rotated])
  from cX have "\<forall>u \<in> unops B. \<forall>F \<in> X. applyU u F \<in> X" by (simp add: closed_under_def)
  then have "\<forall>F \<in> X. applyU u F \<in> X" using u by (rule bspec)
  then show "applyU u F \<in> X" using FX by (rule bspec)
qed

lemma clos_binop_app:
  assumes b: "b \<in> binops B" and F: "F \<in> clos B" and G: "G \<in> clos B" shows "applyB b F G \<in> clos B"
  unfolding clos_def
proof (rule InterI)
  fix X assume cX: "X \<in> {X. closed_under B X}"
  then have FX: "F \<in> X" using F unfolding clos_def by (rule InterD[rotated])
  from cX have GX: "G \<in> X" using G unfolding clos_def by (rule InterD[rotated])
  from cX have "\<forall>b \<in> binops B. \<forall>F \<in> X. \<forall>G \<in> X. applyB b F G \<in> X" by (simp add: closed_under_def)
  then have "\<forall>F \<in> X. \<forall>G \<in> X. applyB b F G \<in> X" using b by (rule bspec)
  then have "\<forall>G \<in> X. applyB b F G \<in> X" using FX by (rule bspec)
  then show "applyB b F G \<in> X" using GX by (rule bspec)
qed

text \<open>The two closure rules in their natural form (\<open>u F\<close>, \<open>b F G\<close>).\<close>
lemma clos_unop: "u \<in> unops B \<Longrightarrow> F \<in> clos B \<Longrightarrow> u F \<in> clos B"
  using clos_unop_app[of u B F] by (simp add: applyU_def)

lemma clos_binop: "b \<in> binops B \<Longrightarrow> F \<in> clos B \<Longrightarrow> G \<in> clos B \<Longrightarrow> b F G \<in> clos B"
  using clos_binop_app[of b B F G] by (simp add: applyB_def)

lemma clos_least: "closed_under B X \<Longrightarrow> clos B \<subseteq> X"
  unfolding clos_def by (rule Inter_lower) simp

text \<open>Induction over the closure.\<close>
lemma clos_induct [consumes 1, case_names init unop binop]:
  assumes F: "F \<in> clos B"
    and I: "\<And>F. F \<in> inits B \<Longrightarrow> P F"
    and U: "\<And>u F. u \<in> unops B \<Longrightarrow> F \<in> clos B \<Longrightarrow> P F \<Longrightarrow> P (applyU u F)"
    and Bi: "\<And>b F G. b \<in> binops B \<Longrightarrow> F \<in> clos B \<Longrightarrow> P F \<Longrightarrow> G \<in> clos B \<Longrightarrow> P G
               \<Longrightarrow> P (applyB b F G)"
  shows "P F"
proof -
  define X where "X = {F \<in> clos B. P F}"
  have mem: "H \<in> X \<longleftrightarrow> H \<in> clos B \<and> P H" for H by (simp add: X_def)
  have "inits B \<subseteq> X"
  proof (rule subsetI)
    fix H assume H: "H \<in> inits B"
    show "H \<in> X" unfolding mem using clos_init[OF H] I[OF H] by (rule conjI)
  qed
  moreover have "\<forall>u \<in> unops B. \<forall>H \<in> X. applyU u H \<in> X"
  proof (intro ballI)
    fix u H assume u: "u \<in> unops B" and H: "H \<in> X"
    from H have Hc: "H \<in> clos B" and PH: "P H" unfolding mem by (rule conjunct1, rule conjunct2)
    show "applyU u H \<in> X" unfolding mem using clos_unop_app[OF u Hc] U[OF u Hc PH] by (rule conjI)
  qed
  moreover have "\<forall>b \<in> binops B. \<forall>H \<in> X. \<forall>K \<in> X. applyB b H K \<in> X"
  proof (intro ballI)
    fix b H K assume b: "b \<in> binops B" and H: "H \<in> X" and K: "K \<in> X"
    from H have Hc: "H \<in> clos B" and PH: "P H" unfolding mem by (rule conjunct1, rule conjunct2)
    from K have Kc: "K \<in> clos B" and PK: "P K" unfolding mem by (rule conjunct1, rule conjunct2)
    show "applyB b H K \<in> X" unfolding mem using clos_binop_app[OF b Hc Kc] Bi[OF b Hc PH Kc PK]
      by (rule conjI)
  qed
  ultimately have "closed_under B X" unfolding closed_under_def by (intro conjI)
  then have "clos B \<subseteq> X" by (rule clos_least)
  then have "F \<in> X" using F by (rule subsetD)
  then show ?thesis unfolding mem by (rule conjunct2)
qed

text \<open>\<open>Prim(\<nat>,\<nat>)\<close>: the one-argument primitive recursive functions, as defined in
  the AFP entry \<^emph>\<open>Recursion Theory I\<close> (M. Nedzelsky).\<close>
abbreviation PrimNN :: "ufun set" where "PrimNN \<equiv> PrimRec1"

text \<open>Definition 3.2.\<close>
definition suitable :: "basis \<Rightarrow> bool" where
  "suitable B \<longleftrightarrow> clos B = PrimNN"

subsection \<open>General facts about closures (not in the paper)\<close>

text \<open>If the initial functions of \<open>B\<^sub>1\<close> lie in \<open>clos B\<^sub>2\<close> and \<open>clos B\<^sub>2\<close> is closed under
  the operators of \<open>B\<^sub>1\<close>, then \<open>clos B\<^sub>1 \<subseteq> clos B\<^sub>2\<close>.\<close>
lemma clos_subset:
  assumes I: "inits B1 \<subseteq> clos B2"
    and U: "\<And>u F. u \<in> unops B1 \<Longrightarrow> F \<in> clos B2 \<Longrightarrow> applyU u F \<in> clos B2"
    and Bi: "\<And>b F G. b \<in> binops B1 \<Longrightarrow> F \<in> clos B2 \<Longrightarrow> G \<in> clos B2 \<Longrightarrow> applyB b F G \<in> clos B2"
  shows "clos B1 \<subseteq> clos B2"
proof (rule subsetI)
  fix F assume "F \<in> clos B1"
  then show "F \<in> clos B2"
  proof (induct rule: clos_induct)
    case (init F) show ?case using I init by (rule subsetD)
  next
    case (unop u F) show ?case using unop(1) unop(3) by (rule U)
  next
    case (binop b F G) show ?case using binop(1) binop(3) binop(5) by (rule Bi)
  qed
qed

text \<open>Soundness: a basis made of primitive recursive initial functions and of operators
  preserving primitive recursiveness only generates primitive recursive functions.\<close>
lemma clos_sound:
  assumes I: "inits B \<subseteq> PrimNN"
    and U: "\<And>u F. u \<in> unops B \<Longrightarrow> F \<in> PrimNN \<Longrightarrow> applyU u F \<in> PrimNN"
    and Bi: "\<And>b F G. b \<in> binops B \<Longrightarrow> F \<in> PrimNN \<Longrightarrow> G \<in> PrimNN \<Longrightarrow> applyB b F G \<in> PrimNN"
  shows "clos B \<subseteq> PrimNN"
proof (rule subsetI)
  fix F assume "F \<in> clos B"
  then show "F \<in> PrimNN"
  proof (induct rule: clos_induct)
    case (init F) show ?case using I init by (rule subsetD)
  next
    case (unop u F) show ?case using unop(1) unop(3) by (rule U)
  next
    case (binop b F G) show ?case using binop(1) binop(3) binop(5) by (rule Bi)
  qed
qed

lemma suitableI:
  assumes "PrimNN \<subseteq> clos B" and "clos B \<subseteq> PrimNN"
  shows "suitable B"
  unfolding suitable_def using assms(2,1) by (rule equalityI)

text \<open>To prove that \<open>B\<^sub>2\<close> is suitable it is enough to generate inside \<open>clos B\<^sub>2\<close> a suitable basis \<open>B\<^sub>1\<close>
  (this is how every suitability proof of the paper proceeds).\<close>
lemma suitable_by_simulation:
  assumes S: "suitable B1"
    and I: "inits B1 \<subseteq> clos B2"
    and U: "\<And>u F. u \<in> unops B1 \<Longrightarrow> F \<in> clos B2 \<Longrightarrow> applyU u F \<in> clos B2"
    and Bi: "\<And>b F G. b \<in> binops B1 \<Longrightarrow> F \<in> clos B2 \<Longrightarrow> G \<in> clos B2 \<Longrightarrow> applyB b F G \<in> clos B2"
    and P: "clos B2 \<subseteq> PrimNN"
  shows "suitable B2"
proof (rule suitableI)
  have "clos B1 \<subseteq> clos B2" using I U Bi by (rule clos_subset)
  then show "PrimNN \<subseteq> clos B2" using S by (simp add: suitable_def)
  show "clos B2 \<subseteq> PrimNN" by (rule P)
qed

end
