/-
  The simp attribute `clos_defs`: the definitions of the bases, unfolded by the closure
  tactics of `UPRF.Tactics` to decide membership in a basis.
-/
import Mathlib.Tactic.Attr.Register

register_simp_attr clos_defs
