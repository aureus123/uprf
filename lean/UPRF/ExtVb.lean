/-
  Removing the constant 1 from the basis of Theorem 6.7 by shifting the unary operator:
  for every fixed b ≥ 1,
    ⟨E, F⁺ᵇ, FG, F^□⟩   with   F⁺ᵇ(x) = F(x) + x + b
  is a suitable basis, whereas for b = 0 (the basis of Theorem 6.7 without 1) it is not.

  The construction works uniformly for every b ≥ 1:
    0̄ ≡ E^□,  A ≡ 0̄⁺ᵇ (A(x) = x + b),  C ≡ E A^{b-1} 0̄ (the constant b - 1),
    B ≡ C⁺ᵇ (B(x) = x + 2b - 1),  T ≡ B^{2b-2} A A (T(x) = x + 4b² - 4b + 2),
    G ≡ (A³ (E T)⁺ᵇ)^□ (G(n) = n² + 4bn),
    P^ ≡ E A^{4b+1} ((G⁺ᵇ)⁺ᵇ)⁺ᵇ (P^(n) = n - 1 for n ≥ 1),
    S ≡ P^^{b-1} A,  1̄ ≡ S 0̄,  F⁺ ≡ P^^b F⁺ᵇ.
  Here A^k etc. are powers under composition (finitely many compositions).
-/
import UPRF.ExtA

namespace UPRF

/-- F⁺ᵇ(x) = F(x) + x + b -/
def opPlusIb (b : ℕ) (F : UFun) : UFun := fun x => F x + x + b

lemma opPlusIb_zero : opPlusIb 0 = opPlusI := rfl

lemma opPlusIb_PR (b : ℕ) {F : UFun} (hF : PrimNN F) : PrimNN (opPlusIb b F) :=
  prim_of (Primrec.nat_add.comp (Primrec.nat_add.comp (primrec_of hF) Primrec.id)
    (Primrec.const b))

macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opPlusIb _))
macro_rules | `(tactic| prim_rules) => `(tactic| exact opPlusIb_PR _ ‹_›)

/-- the basis ⟨E, F⁺ᵇ, FG, F^□⟩ -/
@[clos_defs] def basisVb (b : ℕ) : Basis := ⟨{funE}, {opPlusIb b, opBox}, {(· ∘ ·)}⟩

/-! ## The construction -/

def zeroB : UFun := opBox funE
def funAb (b : ℕ) : UFun := opPlusIb b zeroB
def constBm1 (b : ℕ) : UFun := funE ∘ (funAb b)^[b - 1] ∘ zeroB
def funBb (b : ℕ) : UFun := opPlusIb b (constBm1 b)
def funTb (b : ℕ) : UFun := (funBb b)^[2 * b - 2] ∘ funAb b ∘ funAb b
def funHb (b : ℕ) : UFun := (funAb b)^[3] ∘ opPlusIb b (funE ∘ funTb b)
def funGb (b : ℕ) : UFun := opBox (funHb b)
def exprPb (b : ℕ) : UFun :=
  funE ∘ (funAb b)^[4 * b + 1] ∘ opPlusIb b (opPlusIb b (opPlusIb b (funGb b)))
def exprSb (b : ℕ) : UFun := (exprPb b)^[b - 1] ∘ funAb b
def exprPlusIb (b : ℕ) (F : UFun) : UFun := (exprPb b)^[b] ∘ opPlusIb b F

lemma zeroB_val (x : ℕ) : zeroB x = 0 := by
  induction x with
  | zero => rfl
  | succ x ih => rw [zeroB, opBox_succ, ← zeroB, ih]; exact funE_small.1

lemma funAb_val (b x : ℕ) : funAb b x = x + b := by
  simp [funAb, opPlusIb, zeroB_val]

lemma constBm1_val (b x : ℕ) : constBm1 b x = b - 1 := by
  simp only [constBm1, Function.comp, zeroB_val, shift_pow (funAb_val b), Nat.zero_add]
  rcases b with _ | c
  · exact funE_small.1
  · rw [Nat.add_sub_cancel, show c * (c + 1) = c * c + c by ring, funE_sq_add (by omega)]

lemma funBb_val (b x : ℕ) : funBb b x = x + (b - 1 + b) := by
  simp only [funBb, opPlusIb, constBm1_val]; ring

/-- with b = c + 1: T(x) = x + d where d = 4c² + 4c + 2 = 4b² - 4b + 2 -/
lemma funTb_val (c x : ℕ) : funTb (c + 1) x = x + (4 * c * c + 4 * c + 2) := by
  simp only [funTb, Function.comp, funAb_val, shift_pow (funBb_val (c + 1)),
    show 2 * (c + 1) - 2 = 2 * c by omega, Nat.add_sub_cancel]
  ring

lemma funHb_val (b y : ℕ) : funHb b y = funE (funTb b y) + y + 4 * b := by
  simp only [funHb, Function.comp, opPlusIb, shift_pow (funAb_val b)]; ring

lemma funGb_val (c n : ℕ) : funGb (c + 1) n = n * n + 4 * (c + 1) * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : funE (funTb (c + 1) (n * n + 4 * (c + 1) * n)) = 2 * n + 1 := by
      rw [funTb_val, show n * n + 4 * (c + 1) * n + (4 * c * c + 4 * c + 2)
        = (n + 2 * c + 1) * (n + 2 * c + 1) + (2 * n + 1) by ring, funE_sq_add (by omega)]
    rw [funGb, opBox_succ, ← funGb, ih, funHb_val, e]; ring

/-- the predecessor: P^(n) = E((n + 2b + 1)² + n - 1) -/
lemma exprPb_succ (c k : ℕ) : exprPb (c + 1) (k + 1) = k := by
  simp only [exprPb, Function.comp, opPlusIb, shift_pow (funAb_val (c + 1)), funGb_val]
  rw [show (k + 1) * (k + 1) + 4 * (c + 1) * (k + 1) + (k + 1) + (c + 1) + (k + 1) + (c + 1)
      + (k + 1) + (c + 1) + (4 * (c + 1) + 1) * (c + 1)
      = (k + 2 * (c + 1) + 2) * (k + 2 * (c + 1) + 2) + k by ring, funE_sq_add (by omega)]

lemma exprSb_val {b : ℕ} (hb : 1 ≤ b) (x : ℕ) : exprSb b x = x + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [exprSb, Function.comp, funAb_val, Nat.add_sub_cancel]
  rw [show x + (c + 1) = x + 1 + c by ring, pred_pow (exprPb_succ c)]

lemma exprPlusIb_eq {b : ℕ} (hb : 1 ≤ b) (F : UFun) : exprPlusIb b F = opPlusI F := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  funext x
  simp only [exprPlusIb, Function.comp, opPlusIb, opPlusI]
  exact pred_pow (exprPb_succ c) _ _

/-! ## Suitability for every b ≥ 1 -/

theorem Ext_Vb {b : ℕ} (hb : 1 ≤ b) : Suitable (basisVb b) := by
  have zero : Clos (basisVb b) zeroB := by unfold zeroB; clos_solve
  have A : Clos (basisVb b) (funAb b) := by unfold funAb; clos_solve
  have T : Clos (basisVb b) (funTb b) := by unfold funTb funBb constBm1; clos_solve
  have P : Clos (basisVb b) (exprPb b) := by unfold exprPb funGb funHb; clos_solve
  have one : Clos (basisVb b) (cst 1) := by
    rw [show cst 1 = exprSb b ∘ zeroB from funext fun x => by
      simp [exprSb_val hb, zeroB_val, cst]]
    unfold exprSb; clos_solve
  have plusI : ∀ F, Clos (basisVb b) F → Clos (basisVb b) (opPlusI F) := fun F hF => by
    rw [← exprPlusIb_eq hb]; unfold exprPlusIb; clos_solve
  simulate Theorem_6_7

/-! ## b = 0: the constant 1 cannot be dropped -/

/-- every function generated by ⟨E, F⁺, FG, F^□⟩ fixes 0, so 1̄ is not generated -/
lemma Vb0_fixes_zero {F : UFun} (h : Clos (basisVb 0) F) : F 0 = 0 := by
  induction h with
  | init hF =>
    simp only [basisVb, Set.mem_singleton_iff] at hF; subst hF; exact funE_small.1
  | unop hu _ ih =>
    simp only [basisVb, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simp [opPlusIb, ih]
    · rfl
  | binop hb _ _ ih₁ ih₂ =>
    simp only [basisVb, Set.mem_singleton_iff] at hb; subst hb
    simp [ih₁, ih₂]

theorem Ext_Vb_zero : ¬ Suitable (basisVb 0) := fun S =>
  absurd (Vb0_fixes_zero ((S (cst 1)).2 (cst_PR 1))) (by simp [cst])

/-- ⟨E, F ↦ F + I + b̄, FG, F^□⟩ is suitable iff b ≥ 1 -/
theorem Ext_Vb_iff (b : ℕ) : Suitable (basisVb b) ↔ 1 ≤ b := by
  refine ⟨fun S => ?_, Ext_Vb⟩
  rcases Nat.eq_zero_or_pos b with rfl | h
  · exact absurd S Ext_Vb_zero
  · exact h

end UPRF
