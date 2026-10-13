/-
  Remark 6.9: with iteration starting from a = 1, the constant 1 can be dropped:
    (I)   ⟨E, F⁺, FG, F^□⁽¹⁾⟩
    (II)  ⟨K, F⁺, FG, F^□⁽¹⁾⟩
    (III) ⟨L, F⁺, FG, F^□⁽¹⁾⟩
  are suitable bases.
-/
import UPRF.Thm68

namespace UPRF

/-- recovering F^□ from F^□⁽¹⁾ with a predecessor P^ (P^(x+1) = x): F^□ ≡ P^ (S F P^)^□⁽¹⁾ -/
lemma box_from_box1 {P F : UFun} (hP : ∀ x, P (x + 1) = x) :
    P ∘ opBoxA 1 (funS ∘ F ∘ P) = opBox F := by
  have aux : ∀ n, opBoxA 1 (funS ∘ F ∘ P) n = opBox F n + 1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [opBoxA_succ, ih, opBox_succ]; simp [funS, hP]
  funext n; simp [aux, hP]

/-- a basis ⟨G, F⁺, FG, F^□⁽¹⁾⟩ -/
@[clos_defs] def basis69 (G : UFun) : Basis := ⟨{G}, {opPlusI, opBoxA 1}, {(· ∘ ·)}⟩

section
variable {G : UFun}

/-- ⟨G, F⁺, FG, F^□⁽¹⁾⟩ is suitable when it simulates ⟨1, G, F⁺, FG, F^□⟩ (suitable) and G is
  primitive recursive -/
lemma suitable69 (S : Suitable ⟨{cst 1, G}, {opPlusI, opBox}, {(· ∘ ·)}⟩) (hG : PrimNN G)
    {P : UFun} (hP : ∀ x, P (x + 1) = x) (hPin : Clos (basis69 G) P)
    (one : Clos (basis69 G) (cst 1)) : Suitable (basis69 G) := by
  have hS : Clos (basis69 G) funS := by rw [← S_expr]; clos_solve
  have box : ∀ F, Clos (basis69 G) F → Clos (basis69 G) (opBox F) := fun F hF => by
    rw [← box_from_box1 hP]; clos_solve
  simulate S

end

/-- O ≡ G^□⁽¹⁾, 0̄ ≡ G O and 1̄ ≡ O 0̄ whenever G(0) = G(1) = 0 -/
lemma O_expr_box1 {G : UFun} (h0 : G 0 = 0) (h1 : G 1 = 0) : opBoxA 1 G = funO := by
  have : ∀ m, opBoxA 1 G (m + 1) = 0 := by
    intro m; induction m with
    | zero => simp [h1]
    | succ m ih => rw [opBoxA_succ, ih, h0]
  funext n; cases n with
  | zero => rfl
  | succ m => rw [this m]; rfl

lemma zero_expr_O {G : UFun} (h0 : G 0 = 0) (h1 : G 1 = 0) : G ∘ funO = cst 0 := by
  funext x; by_cases h : x = 0 <;> simp [funO, cst, h, h0, h1]

lemma one_expr_O : funO ∘ cst 0 = cst 1 := rfl

lemma one_in69 {G : UFun} (h0 : G 0 = 0) (h1 : G 1 = 0) : Clos (basis69 G) (cst 1) := by
  have O : Clos (basis69 G) funO := by rw [← O_expr_box1 h0 h1]; clos_solve
  rw [← one_expr_O, ← zero_expr_O h0 h1]; clos_solve

/-! ## (I) ⟨E, F⁺, FG, F^□⁽¹⁾⟩ -/

/-- G(x) = (x + 1)², G ≡ (((D Q S S)⁺ S)^□⁽¹⁾)^□⁽¹⁾; the inner iteration computes R(x) + 1 -/
def funG : UFun := fun x => (x + 1) * (x + 1)

lemma G_inner (n : ℕ) :
    opBoxA 1 (opPlusI (funD ∘ funQ ∘ funS ∘ funS) ∘ funS) n = funS (funR n) := by
  induction n with
  | zero => simp [funS, funR, funRt]
  | succ n ih =>
    rw [opBoxA_succ, ih, ← R_step]; simp [opPlusI, funS, Function.comp]; ring

lemma G_expr : opBoxA 1 (opBoxA 1 (opPlusI (funD ∘ funQ ∘ funS ∘ funS) ∘ funS)) = funG := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBoxA_succ, ih, G_inner]
    simp only [funG, funS, funR, funRt_sq]; ring

/-- P^ ≡ E S S ((G⁺)⁺)⁺ -/
def exprPhatI : UFun := funE ∘ funS ∘ funS ∘ opPlusI (opPlusI (opPlusI funG))

lemma PhatI_succ (x : ℕ) : exprPhatI (x + 1) = x := by
  simp only [exprPhatI, Function.comp, funS, opPlusI, funG]
  rw [show (x + 1 + 1) * (x + 1 + 1) + (x + 1) + (x + 1) + (x + 1) + 1 + 1
    = (x + 3) * (x + 3) + x by ring, funE_sq_add (by omega)]

theorem Remark_6_9_I : Suitable (basis69 funE) := by
  have h0 := funE_small.1; have h1 := funE_small.2.1
  have one := one_in69 h0 h1
  have S : Clos (basis69 funE) funS := by rw [← S_expr]; clos_solve
  have O : Clos (basis69 funE) funO := by rw [← O_expr_box1 h0 h1]; clos_solve
  have zero : Clos (basis69 funE) (cst 0) := by rw [← zero_expr_O h0 h1]; clos_solve
  have D : Clos (basis69 funE) funD := by rw [← D_expr]; clos_solve
  have Q : Clos (basis69 funE) funQ := by rw [← Q_expr]; clos_solve
  have G : Clos (basis69 funE) funG := by rw [← G_expr]; clos_solve
  have P : Clos (basis69 funE) exprPhatI := by unfold exprPhatI; clos_solve
  exact suitable69 Theorem_6_7 funE_PR PhatI_succ P one

/-! ## (II) ⟨K, F⁺, FG, F^□⁽¹⁾⟩ -/

/-- H(x) = (x + 1)(x + 4)/2 = A(x+1) + x + 1, H ≡ S (S K⁺ S)^□⁽¹⁾ -/
def funH : UFun := fun x => funA (x + 1) + x + 1

lemma two_funH (x : ℕ) : 2 * funH x = (x + 1) * (x + 4) := by
  have := two_funA (x + 1); simp only [funH]; nlinarith

lemma H_inner (n : ℕ) : opBoxA 1 (funS ∘ opPlusI funK ∘ funS) n = funA (n + 1) + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBoxA_succ, ih]
    have := funK_diag (k := n + 1) (t := n + 1) le_rfl
    simp only [Function.comp, funS, opPlusI]
    rw [show funA (n + 1) + n + 1 = funA (n + 1) + (n + 1) by ring, this, funA_succ (n + 1)]
    ring

lemma H_expr : funS ∘ opBoxA 1 (funS ∘ opPlusI funK ∘ funS) = funH := by
  funext x; simp [H_inner, funS, funH]

/-- P^ ≡ K S S S (H⁺)⁺ -/
def exprPhatII : UFun := funK ∘ funS ∘ funS ∘ funS ∘ opPlusI (opPlusI funH)

lemma PhatII_succ (x : ℕ) : exprPhatII (x + 1) = x := by
  simp only [exprPhatII, Function.comp, funS, opPlusI, funH]
  have e : funA (x + 1 + 1) + (x + 1) + 1 + (x + 1) + (x + 1) + 1 + 1 + 1 = funA (x + 4) + x := by
    simp only [funA_succ]; ring
  rw [e, funK_diag (by omega)]

theorem Remark_6_9_II : Suitable (basis69 funK) := by
  have one := one_in69 funK_zero funK_one
  have S : Clos (basis69 funK) funS := by rw [← S_expr]; clos_solve
  have H : Clos (basis69 funK) funH := by rw [← H_expr]; clos_solve
  have P : Clos (basis69 funK) exprPhatII := by unfold exprPhatII; clos_solve
  exact suitable69 Theorem_6_8_K funK_PR PhatII_succ P one

/-! ## (III) ⟨L, F⁺, FG, F^□⁽¹⁾⟩: 1̄ ≡ L^□⁽¹⁾ (since L(1) = 1) and K ≡ L 1⁺ ((1⁺)⁺ L)⁺ -/

lemma funL_one : funL 1 = 1 := by
  simpa [funA_one] using funL_diag (k := 0) (t := 1) (by omega)

lemma one_expr_III : opBoxA 1 funL = cst 1 := by
  funext n; induction n with
  | zero => rfl
  | succ n ih => rw [opBoxA_succ, ih]; exact funL_one

theorem Remark_6_9_III : Suitable (basis69 funL) := by
  have one : Clos (basis69 funL) (cst 1) := by rw [← one_expr_III]; clos_solve
  have K : Clos (basis69 funL) funK := by rw [← K_expr_L]; clos_solve
  simulate Remark_6_9_II

end UPRF
