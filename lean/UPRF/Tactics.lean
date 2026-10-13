/-
  Tactics for the three mechanisms that recur in the proofs:

  - `clos_solve` : membership in a closure, `Clos B F`. The function is decomposed with the
    closure rules (composition, sum, `F⁺`, `F^□`, `F^□(1)`), the registered membership lemmas
    (`clos_hint`), the hypotheses (also used as rules) and the initial functions of the basis. All applications
    run with reducible transparency, so the paper's functions are never unfolded during
    unification. Membership in the basis is decided by `simp only` with the basis definitions
    (attribute `clos_defs`).
  - `prim_sound` : soundness of a closure (`clos_sound`, a case analysis of the basis and the
    primitive recursiveness lemmas, together with the hypotheses).
  - `simulate S` : a whole `suitable_by_simulation` proof from the suitable basis `S`.

  `clos_hint` is extensible: a later file registers a membership lemma `h` with
  `macro_rules | `(tactic| clos_hint) => `(tactic| apply h)`.
-/
import UPRF.Attr
import UPRF.Basic

namespace UPRF

/-- membership in a basis (`x ∈ B.inits`, `x ∈ B.unops`, `x ∈ B.binops`) -/
macro "clos_mem" : tactic =>
  `(tactic| (simp only [clos_defs, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
      or_true]; done))

/-- registered membership lemmas; extended with `macro_rules` in later files -/
syntax "clos_hint" : tactic
macro_rules | `(tactic| clos_hint) => `(tactic| fail "no closure hint applies")

/-- the generic closure rules, one per operator -/
syntax "clos_rule" : tactic
macro_rules
  | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.binop (b := fun f g => f ∘ g))
macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.binop (b := opPlus))
macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opPlusI))
macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opBox))
macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opBoxA 1))

/-- membership in a closure -/
syntax "clos_solve" : tactic
macro_rules
  | `(tactic| clos_solve) => `(tactic|
      first
      | assumption
      | clos_mem
      | (clos_hint <;> clos_solve)
      | (with_reducible apply_assumption <;> clos_solve)
      | (clos_rule <;> clos_solve)
      | (apply Clos.init; clos_mem))

/-- splitting a disjunction of equations `x = a ∨ x = b ∨ …` and substituting -/
syntax "split_eqs " ident : tactic
macro_rules
  | `(tactic| split_eqs $h) => `(tactic|
      first
      | subst $h:ident
      | (rcases $h:ident with $h:ident | $h:ident <;> split_eqs $h))

/-- a basis-membership hypothesis `h` is turned into the possible cases -/
syntax "basis_cases " ident : tactic
macro_rules
  | `(tactic| basis_cases $h) => `(tactic|
      (simp only [clos_defs, Set.mem_insert_iff, Set.mem_singleton_iff] at $h:ident;
       split_eqs $h))

/-- primitive recursiveness of the functions and operators of the paper -/
syntax "prim_rules" : tactic
macro_rules
  | `(tactic| prim_rules) => `(tactic|
      solve_by_elim [cst_PR, funS_PR, funRt_PR, funE_PR, funSq_PR, funHf_PR, funO_PR,
        funA_PR, funV_PR, funK_PR, funL_PR, comp_PR, opPlus_PR, opPlusI_PR, opBoxA_PR,
        opBox_PR])

/-- soundness of a closure: every generated function is primitive recursive -/
macro "prim_sound" : tactic =>
  `(tactic| exact clos_sound
      (fun F hF => by basis_cases hF <;> prim_rules)
      (fun u hu F hF => by basis_cases hu <;> prim_rules)
      (fun b hb F G hF hG => by basis_cases hb <;> prim_rules))

/-- a suitability proof by simulation of the suitable basis `S` -/
macro "simulate " S:term : tactic =>
  `(tactic| exact suitable_by_simulation $S
      (fun F hF => by basis_cases hF <;> clos_solve)
      (fun u hu F hF => by basis_cases hu <;> clos_solve)
      (fun b hb F G hF hG => by basis_cases hb <;> clos_solve)
      (by prim_sound))

end UPRF
