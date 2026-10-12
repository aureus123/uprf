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
def basis69 (G : UFun) : Basis := ⟨{G}, {opPlusI, opBoxA 1}, {(· ∘ ·)}⟩

section
variable {G : UFun}

lemma CB_G : Clos (basis69 G) G := .init rfl
lemma CB_plusI {F} (h : Clos (basis69 G) F) : Clos (basis69 G) (opPlusI F) :=
  .unop (u := opPlusI) (by simp [basis69]) h
lemma CB_box1 {F} (h : Clos (basis69 G) F) : Clos (basis69 G) (opBoxA 1 F) :=
  .unop (u := opBoxA 1) (by simp [basis69]) h
lemma CB_comp {F H} (hF : Clos (basis69 G) F) (hH : Clos (basis69 G) H) :
    Clos (basis69 G) (F ∘ H) := .binop (b := (· ∘ ·)) (by simp [basis69]) hF hH

lemma CB_box {P F} (hP : ∀ x, P (x + 1) = x) (hPin : Clos (basis69 G) P)
    (hS : Clos (basis69 G) funS) (hF : Clos (basis69 G) F) : Clos (basis69 G) (opBox F) :=
  box_from_box1 hP ▸ CB_comp hPin (CB_box1 (CB_comp hS (CB_comp hF hPin)))

/-- ⟨G, F⁺, FG, F^□⁽¹⁾⟩ is suitable when it simulates ⟨1, G, F⁺, FG, F^□⟩ (suitable) and G is
  primitive recursive -/
lemma suitable69 (S : Suitable ⟨{cst 1, G}, {opPlusI, opBox}, {(· ∘ ·)}⟩) (hG : PrimNN G)
    {P : UFun} (hP : ∀ x, P (x + 1) = x) (hPin : Clos (basis69 G) P)
    (one : Clos (basis69 G) (cst 1)) : Suitable (basis69 G) := by
  have hS : Clos (basis69 G) funS := S_expr ▸ CB_plusI one
  refine suitable_by_simulation S ?_ ?_ ?_ ?_
  · rintro F (rfl | rfl); exacts [one, CB_G]
  · rintro u (rfl | rfl) F hF; exacts [CB_plusI hF, CB_box hP hPin hS hF]
  · rintro b rfl F H hF hH; exact CB_comp hF hH
  · exact clos_sound (by rintro F rfl; exact hG)
      (by rintro u (rfl | rfl) F hF; exacts [opPlusI_PR hF, opBoxA_PR 1 hF])
      (by rintro b rfl F H hF hH; exact comp_PR hF hH)

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
  have O : Clos (basis69 G) funO := O_expr_box1 h0 h1 ▸ CB_box1 CB_G
  exact one_expr_O ▸ CB_comp O (zero_expr_O h0 h1 ▸ CB_comp CB_G O)

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
  have one := one_in69 funE_small.1 funE_small.2.1
  have S : Clos (basis69 funE) funS := S_expr ▸ CB_plusI one
  have O : Clos (basis69 funE) funO := O_expr_box1 funE_small.1 funE_small.2.1 ▸ CB_box1 CB_G
  have zero : Clos (basis69 funE) (cst 0) :=
    zero_expr_O funE_small.1 funE_small.2.1 ▸ CB_comp CB_G O
  have D : Clos (basis69 funE) funD := D_expr ▸ CB_plusI (CB_plusI zero)
  have Q : Clos (basis69 funE) funQ := Q_expr ▸ CB_comp O CB_G
  have G : Clos (basis69 funE) funG := G_expr ▸ CB_box1 (CB_box1 (CB_comp (CB_plusI
    (CB_comp D (CB_comp Q (CB_comp S S)))) S))
  have P : Clos (basis69 funE) exprPhatI := CB_comp CB_G (CB_comp S (CB_comp S
    (CB_plusI (CB_plusI (CB_plusI G)))))
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
  have h0 : funK 0 = 0 := funK_zero
  have one := one_in69 h0 funK_one
  have S : Clos (basis69 funK) funS := S_expr ▸ CB_plusI one
  have H : Clos (basis69 funK) funH :=
    H_expr ▸ CB_comp S (CB_box1 (CB_comp S (CB_comp (CB_plusI CB_G) S)))
  have P : Clos (basis69 funK) exprPhatII :=
    CB_comp CB_G (CB_comp S (CB_comp S (CB_comp S (CB_plusI (CB_plusI H)))))
  exact suitable69 Theorem_6_8_K funK_PR PhatII_succ P one

/-! ## (III) ⟨L, F⁺, FG, F^□⁽¹⁾⟩: 1̄ ≡ L^□⁽¹⁾ (since L(1) = 1) and K ≡ L 1⁺ ((1⁺)⁺ L)⁺ -/

lemma funL_one : funL 1 = 1 := by
  simpa [funA_one] using funL_diag (k := 0) (t := 1) (by omega)

lemma one_expr_III : opBoxA 1 funL = cst 1 := by
  funext n; induction n with
  | zero => rfl
  | succ n ih => rw [opBoxA_succ, ih]; exact funL_one

theorem Remark_6_9_III : Suitable (basis69 funL) := by
  have one : Clos (basis69 funL) (cst 1) := one_expr_III ▸ CB_box1 CB_G
  have K : Clos (basis69 funL) funK :=
    K_expr_L ▸ CB_comp CB_G (CB_comp (CB_plusI one)
      (CB_plusI (CB_comp (CB_plusI (CB_plusI one)) CB_G)))
  refine suitable_by_simulation Remark_6_9_II ?_ ?_ ?_ ?_
  · rintro F rfl; exact K
  · rintro u (rfl | rfl) F hF; exacts [CB_plusI hF, CB_box1 hF]
  · rintro b rfl F H hF hH; exact CB_comp hF hH
  · exact clos_sound (by rintro F rfl; exact funL_PR)
      (by rintro u (rfl | rfl) F hF; exacts [opPlusI_PR hF, opBoxA_PR 1 hF])
      (by rintro b rfl F H hF hH; exact comp_PR hF hH)

end UPRF
