(*  Title:   UPRF_Sec2_Notation.thy
    Paper:   D. E. Severin, "Unary primitive recursive functions",
             J. Symbolic Logic 73(4), 2008.  arXiv:cs/0603063v3.

    Section 2 (Notation) of the paper.

    Naming convention: a function called X in the paper is called funX here
    (e.g. S is funS, Rt is funRt); an operator on functions is called opX
    (e.g. F^+ is opPlusI F, F^\<box> is opBox F).  The constant function
    \<overline>n of the paper is cst n.  Juxtaposition FG of the paper is the
    usual composition F \<circ> G of Isabelle.
*)

theory UPRF_Sec2_Notation
  imports
    "Recursion-Theory-I.PRecFun"
    "HOL-Library.Discrete_Functions"
begin

section \<open>Section 2: Notation\<close>

type_synonym ufun = "nat \<Rightarrow> nat"              \<comment> \<open>one-argument functions \<open>\<nat> \<rightarrow> \<nat>\<close>\<close>
type_synonym uop  = "ufun \<Rightarrow> ufun"            \<comment> \<open>unary operators, e.g. \<open>F\<^sup>+\<close>, \<open>F\<^sup>\<box>\<close>\<close>
type_synonym bop  = "ufun \<Rightarrow> ufun \<Rightarrow> ufun"    \<comment> \<open>binary operators, e.g. \<open>F + G\<close>, \<open>FG\<close>\<close>

subsection \<open>Basic functions\<close>

definition funI :: ufun where "funI x = x"                 \<comment> \<open>identity\<close>
definition cst :: "nat \<Rightarrow> ufun" where "cst n x = n"         \<comment> \<open>constants \<open>\<overline>n\<close>\<close>
definition funS :: ufun where "funS x = Suc x"             \<comment> \<open>successor\<close>
definition funP :: ufun where "funP x = x - 1"             \<comment> \<open>predecessor\<close>

subsection \<open>Arithmetic functions\<close>

definition funD  :: ufun where "funD x = 2 * x"            \<comment> \<open>double\<close>
definition funSq :: ufun where "funSq x = x * x"           \<comment> \<open>square\<close>
definition funHf :: ufun where "funHf x = x div 2"         \<comment> \<open>half\<close>
definition funPw :: ufun where "funPw x = 2 ^ x"           \<comment> \<open>power of two\<close>
definition funRt :: ufun where "funRt x = floor_sqrt x"    \<comment> \<open>integer square root \<open>\<lfloor>\<surd>x\<rfloor>\<close>\<close>

subsection \<open>Cantor pairing functions\<close>

definition funA :: ufun where "funA x = (x * x + x) div 2"                      \<comment> \<open>\<open>x\<close>-th triangular number\<close>
definition funV :: ufun where "funV x = (funRt (8 * x + 1) - 1) div 2"          \<comment> \<open>inverse of \<open>A\<close>\<close>
definition funJ :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "funJ x y = funA (x + y) + x"   \<comment> \<open>pairing function\<close>
definition funK :: ufun where "funK x = x - funA (funV x)"                      \<comment> \<open>first inverse\<close>
definition funL :: ufun where "funL x = funA (funV x + 1) - x - 1"              \<comment> \<open>second inverse\<close>

subsection \<open>Other functions\<close>

definition funO   :: ufun where "funO x = (if x = 0 then 1 else 0)"      \<comment> \<open>power of zero, cosignum\<close>
definition funSgn :: ufun where "funSgn x = (if x = 0 then 0 else 1)"    \<comment> \<open>signum\<close>
definition funN   :: ufun where "funN x = x mod 2"                       \<comment> \<open>characteristic of odd numbers\<close>
definition funE   :: ufun where "funE x = x - (funRt x)\<^sup>2"               \<comment> \<open>excess over a square\<close>
definition funQ   :: ufun where "funQ x = (if \<exists>k. x = k\<^sup>2 then 1 else 0)"   \<comment> \<open>characteristic of squares\<close>

subsection \<open>Operators\<close>

text \<open>Pointwise sum, arithmetic difference and distance of functions (Miscellaneous 1--3).\<close>
definition opPlus :: bop where "opPlus F G x = F x + G x"
definition opMinus :: bop where "opMinus F G x = F x - G x"
definition opDist :: bop where "opDist F G x = (if F x \<ge> G x then F x - G x else G x - F x)"

text \<open>Restricted forms of primitive recursion (2) and (3): \<open>F\<^sup>\<box>\<^sup>(\<^sup>a\<^sup>)\<close> and \<open>F\<^sup>\<box> = F\<^sup>\<box>\<^sup>(\<^sup>0\<^sup>)\<close>
  (pure iteration without parameters, scheme \<open>rec\<^sub>6\<close> and \<open>rec\<^sub>8\<close> of Section 3).\<close>
primrec opBoxA :: "nat \<Rightarrow> uop" where
  "opBoxA a F 0 = a"
| "opBoxA a F (Suc x) = F (opBoxA a F x)"

definition opBox :: uop where "opBox F = opBoxA 0 F"

lemma opBoxA_eq_funpow: "opBoxA a F n = (F ^^ n) a"
  by (induct n) simp_all

lemma opBox_0 [simp]: "opBox F 0 = 0"
  and opBox_Suc [simp]: "opBox F (Suc x) = F (opBox F x)"
  by (simp_all add: opBox_def)

text \<open>Composition \<open>FG\<close> of the paper is \<open>F \<circ> G\<close>; the power \<open>F\<^sup>n\<close> is \<open>F ^^ n\<close>.\<close>

lemmas fun_defs =
  funI_def cst_def funS_def funP_def funD_def funSq_def funHf_def funPw_def
  funO_def funSgn_def funN_def opPlus_def opMinus_def

end
