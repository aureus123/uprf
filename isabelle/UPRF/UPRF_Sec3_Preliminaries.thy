(*  Title:   UPRF_Sec3_Preliminaries.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions", JSL 2008.

    Section 3 (Preliminaries): the definitions needed by Section 6.

    Robinson's theorem [15, Section 7, Theorem 3] and Lemma 3.3, which depends on it,
    are proved later, in UPRF_Robinson and UPRF_Sec6_Thm67, because the proof of
    Robinson's theorem reuses the constructions of Lemmas 6.2-6.6.
*)

theory UPRF_Sec3_Preliminaries
  imports UPRF_Methods
begin

section \<open>Section 3: Preliminaries\<close>

subsection \<open>Robinson's basis\<close>

text \<open>Robinson [15, \S7, Theorem 3]: all one-argument primitive recursive functions are
  obtained from \<open>S\<close> and \<open>E\<close> by \<open>F + G\<close>, \<open>FG\<close> and \<open>F\<^sup>\<box>\<close>, i.e. \<open>\<langle>S, E, F + G, FG, F\<^sup>\<box>\<rangle>\<close> is a
  suitable basis.  (This is also the first sentence of Section 6 of the paper.)
  The inclusion \<open>clos \<subseteq> Prim\<close> is easy and is proved here; the converse is proved in
  UPRF_Robinson.\<close>
definition basis_Robinson :: basis where
  "basis_Robinson = Basis {funS, funE} {opBox} {opPlus, (\<circ>)}"

lemmas basis_Robinson_sel [clos_defs] =
  basis.sel[of "{funS, funE}" "{opBox}" "{opPlus, (\<circ>)}", folded basis_Robinson_def]

lemma Robinson_sound: "clos basis_Robinson \<subseteq> PrimNN"
  by clos_sound_m

subsection \<open>Difference functions\<close>

text \<open>Footnote 3: \<open>x - y\<close> (without dot or bars) stands for any function \<open>d(x, y)\<close> equal to
  \<open>x - y\<close> whenever \<open>x \<ge> y\<close>, regardless of its value when \<open>x < y\<close>.\<close>
definition is_difference :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_difference d \<longleftrightarrow> (\<forall>\<alpha> \<beta>. \<beta> \<le> \<alpha> \<longrightarrow> d \<alpha> \<beta> = \<alpha> - \<beta>)"

text \<open>The operator \<open>F - G\<close> of Lemma 3.3 for a given difference function \<open>d\<close>.\<close>
definition opDiff :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bop" where
  "opDiff d = opPointwise d"

lemma opDiff_apply: "opDiff d F G x = d (F x) (G x)"
  by (simp add: opDiff_def opPointwise_def)

subsection \<open>The basis of Lemma 3.3\<close>

definition basis_L33 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> basis" where
  "basis_L33 d = Basis {funS, funSq, funO, funHf, funRt} {opBox} {opPlus, opDiff d, (\<circ>)}"

lemmas basis_L33_sel [clos_defs] = basis.sel[of "{funS, funSq, funO, funHf, funRt}" "{opBox}"
  "{opPlus, opDiff d, (\<circ>)}", folded basis_L33_def] for d

text \<open>\<open>I \<equiv> S\<^sup>\<box>\<close>.\<close>
lemma funI_eq_box_S: "opBox funS = funI"
proof
  fix x show "opBox funS x = funI x" by (induct x) (simp_all add: funS_def funI_def)
qed

end
