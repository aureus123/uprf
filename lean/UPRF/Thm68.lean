/-
  Theorem 6.8: the bases ⟨1, K, F⁺, FG, F^□⟩ and ⟨1, L, F⁺, FG, F^□⟩ are suitable
  (K and L are the inverses of the Cantor pairing function).
-/
import UPRF.Thm67

namespace UPRF

/-! ## The basis 𝓕' = ⟨1, K, F⁺, FG, F^□⟩ -/

def basis6K : Basis := ⟨{cst 1, funK}, {opPlusI, opBox}, {(· ∘ ·)}⟩
abbrev C6K (F : UFun) : Prop := Clos basis6K F

lemma C6K_one : C6K (cst 1) := .init (by simp [basis6K])
lemma C6K_K : C6K funK := .init (by simp [basis6K])
lemma C6K_plusI {F} (h : C6K F) : C6K (opPlusI F) := .unop (u := opPlusI) (by simp [basis6K]) h
lemma C6K_box {F} (h : C6K F) : C6K (opBox F) := .unop (u := opBox) (by simp [basis6K]) h
lemma C6K_comp {F G} (hF : C6K F) (hG : C6K G) : C6K (F ∘ G) :=
  .binop (b := (· ∘ ·)) (by simp [basis6K]) hF hG

/-- auxiliary functions of the proof (Robinson [16, p. 664]):
  Y(x) = 2x - Rt(x) and Z(x) = x(x+3)/2 = A(x) + x -/
def funY : UFun := fun x => 2 * x - funRt x
def funZ : UFun := fun x => funA x + x

lemma two_funZ (x : ℕ) : 2 * funZ x = x * (x + 3) := by
  have := two_funA x; simp only [funZ]; nlinarith

lemma funA_zero : funA 0 = 0 := rfl
lemma funA_one : funA 1 = 1 := rfl

lemma funK_one : funK 1 = 0 := by
  simpa [funA_one] using funK_diag (k := 0) (t := 1) (by omega)

lemma zero_expr_K : funK ∘ cst 1 = cst 0 := by funext x; exact funK_one

/-- Z ≡ (S S K⁺)^□ -/
lemma Z_expr : opBox (funS ∘ funS ∘ opPlusI funK) = funZ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBox_succ, ih]
    have := funK_diag (k := n) (t := n) le_rfl
    simp only [Function.comp, funS, opPlusI, funZ, this, funA_succ]; omega

/-- Robinson's formula: K((a + b)(a + b + 3)/2 + 2a + 3) = a - b if a ≥ b -/
lemma robinson_diff_K {a b : ℕ} (h : b ≤ a) : funK (funZ (a + b) + 2 * a + 3) = a - b := by
  have e : funZ (a + b) + 2 * a + 3 = funA (a + b + 2) + (a - b) := by
    simp only [funZ, funA_succ]; omega
  rw [e, funK_diag (by omega)]

/-- I - F ≡ K S S S ((Z F⁺)⁺)⁺ (if x ≥ F(x)) and
  D - F ≡ K S S S ((((Z (F⁺)⁺)⁺)⁺)⁺)⁺ (if 2x ≥ F(x)) -/
def exprIminusF (F : UFun) : UFun :=
  funK ∘ funS ∘ funS ∘ funS ∘ opPlusI (opPlusI (funZ ∘ opPlusI F))

def exprDminusF (F : UFun) : UFun :=
  funK ∘ funS ∘ funS ∘ funS ∘
    opPlusI (opPlusI (opPlusI (opPlusI (funZ ∘ opPlusI (opPlusI F)))))

lemma exprIminusF_val {F : UFun} {x : ℕ} (h : F x ≤ x) : exprIminusF F x = x - F x := by
  rw [← robinson_diff_K h]
  simp only [exprIminusF, Function.comp, funS, opPlusI]
  congr 1; rw [Nat.add_comm (F x) x]; ring

lemma exprDminusF_val {F : UFun} {x : ℕ} (h : F x ≤ 2 * x) :
    exprDminusF F x = 2 * x - F x := by
  rw [← robinson_diff_K h]
  simp only [exprDminusF, Function.comp, funS, opPlusI]
  congr 1; rw [show F x + x + x = 2 * x + F x by ring]; ring

/-- Y ≡ ((Sgn K)⁺ S)^□; the key fact is that Y(n) + 1 is triangular iff n + 1 is a square -/
lemma funRt_le (n : ℕ) : funRt n ≤ n := le_trans (Nat.le_mul_self _) (funRt_sq_le n)

lemma Y_add (n : ℕ) : funY n + funRt n = 2 * n := by
  have := funRt_le n; simp only [funY]; omega

lemma Y_step_square {n : ℕ} (h : (funRt n + 1) * (funRt n + 1) = n + 1) :
    funK (funY n + 1) = 0 := by
  set r := funRt n
  have ya := Y_add n
  have := two_funA (2 * r + 1)
  have e : funY n + 1 = funA (2 * r + 1) + 0 := by nlinarith
  rw [e, funK_diag (by omega)]

lemma Y_step_nonsquare {n : ℕ} (h : (funRt n + 1) * (funRt n + 1) ≠ n + 1) :
    funK (funY n + 1) ≠ 0 := by
  set r := funRt n with hr
  set m := funY n + 1
  intro hK
  have lo := funRt_sq_le n; have hi := funRt_lt n
  rw [← hr] at lo hi
  have hi' : n + 1 < (r + 1) * (r + 1) := by omega
  have r0 : r ≠ 0 := by rintro h0; rw [h0] at hi'; omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero r0
  have ya := Y_add n
  have ms : m + s = 2 * n := by omega
  obtain ⟨hd, -⟩ := decomp m
  set u := funV m
  have mu : m = funA u := by rw [hK] at hd; omega
  have a1 := two_funA (2 * s + 1); have a2 := two_funA (2 * s + 3)
  have lo' : (s + 1) * (s + 1) ≤ n := by rw [hs] at lo; exact lo
  have hi'' : n + 2 ≤ (s + 2) * (s + 2) := by rw [hs] at hi'; nlinarith
  have l1 : funA (2 * s + 1) < funA u := by rw [← mu]; nlinarith
  have l2 : funA u < funA (2 * s + 3) := by rw [← mu]; nlinarith
  have u2 : u = 2 * s + 2 := by
    have := funA_lt_imp l1; have := funA_lt_imp l2; omega
  have a3 := two_funA u
  rw [u2] at a3 mu
  have e : 2 * n = 2 * (s * s + 3 * s + 1) + 1 := by nlinarith
  generalize s * s + 3 * s + 1 = q at e
  omega

lemma Y_step (n : ℕ) : opPlusI (funSgn ∘ funK) (funS (funY n)) = funY (n + 1) := by
  set r := funRt n with hr
  have lo := funRt_sq_le n; have hi := funRt_lt n
  rw [← hr] at lo hi
  have y1 := Y_add n; have y2 := Y_add (n + 1)
  simp only [opPlusI, Function.comp, funS, funSgn]
  by_cases h : (r + 1) * (r + 1) = n + 1
  · have rt : funRt (n + 1) = r + 1 := funRt_unique (by omega) (by nlinarith)
    simp only [Y_step_square h, ↓reduceIte]; omega
  · have rt : funRt (n + 1) = r := funRt_unique (by nlinarith) (by omega)
    simp only [Y_step_nonsquare h, ↓reduceIte]; omega

lemma Y_expr : opBox (opPlusI (funSgn ∘ funK) ∘ funS) = funY := by
  funext n
  induction n with
  | zero => simp [funY, funRt]
  | succ n ih => rw [opBox_succ, ih, Function.comp_apply, Y_step]

/-- Rt ≡ D - Y, Sq ≡ (((1⁺)⁺ Rt)⁺)^□, E ≡ I - Sq Rt -/
lemma Rt_expr_K : exprDminusF funY = funRt := by
  funext x
  have := funRt_le x
  rw [exprDminusF_val (by simp [funY])]; simp only [funY]; omega

lemma Sq_expr_K : opBox (opPlusI (opPlusI (opPlusI (cst 1)) ∘ funRt)) = funSq := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBox_succ, ih]; simp only [opPlusI, Function.comp, funSq, funRt_sq, cst]; ring

lemma E_expr_K : exprIminusF (funSq ∘ funRt) = funE := by
  funext x; rw [exprIminusF_val (funRt_sq_le x)]; rfl

lemma S_in_K : C6K funS := S_expr ▸ C6K_plusI C6K_one
lemma Sgn_in_K : C6K funSgn := Sgn_expr ▸ C6K_box C6K_one
lemma Z_in_K : C6K funZ := Z_expr ▸ C6K_box (C6K_comp S_in_K (C6K_comp S_in_K (C6K_plusI C6K_K)))
lemma Y_in_K : C6K funY :=
  Y_expr ▸ C6K_box (C6K_comp (C6K_plusI (C6K_comp Sgn_in_K C6K_K)) S_in_K)

lemma KSSS_in_K : C6K (funK ∘ funS ∘ funS ∘ funS) :=
  C6K_comp C6K_K (C6K_comp S_in_K (C6K_comp S_in_K S_in_K))

lemma exprIminusF_in_K {F} (h : C6K F) : C6K (exprIminusF F) :=
  C6K_comp C6K_K (C6K_comp S_in_K (C6K_comp S_in_K (C6K_comp S_in_K
    (C6K_plusI (C6K_plusI (C6K_comp Z_in_K (C6K_plusI h)))))))

lemma exprDminusF_in_K {F} (h : C6K F) : C6K (exprDminusF F) :=
  C6K_comp C6K_K (C6K_comp S_in_K (C6K_comp S_in_K (C6K_comp S_in_K
    (C6K_plusI (C6K_plusI (C6K_plusI (C6K_plusI
      (C6K_comp Z_in_K (C6K_plusI (C6K_plusI h))))))))))

lemma Rt_in_K : C6K funRt := Rt_expr_K ▸ exprDminusF_in_K Y_in_K
lemma Sq_in_K : C6K funSq :=
  Sq_expr_K ▸ C6K_box (C6K_plusI (C6K_comp (C6K_plusI (C6K_plusI C6K_one)) Rt_in_K))
lemma E_in_K : C6K funE := E_expr_K ▸ exprIminusF_in_K (C6K_comp Sq_in_K Rt_in_K)

theorem Theorem_6_8_K : Suitable basis6K := by
  refine suitable_by_simulation Theorem_6_7 ?_ ?_ ?_ ?_
  · rintro F (rfl | rfl); exacts [C6K_one, E_in_K]
  · rintro u (rfl | rfl) F hF; exacts [C6K_plusI hF, C6K_box hF]
  · rintro b rfl F G hF hG; exact C6K_comp hF hG
  · exact clos_sound (by rintro F (rfl | rfl); exacts [cst_PR 1, funK_PR])
      (by rintro u (rfl | rfl) F hF; exacts [opPlusI_PR hF, opBox_PR hF])
      (by rintro b rfl F G hF hG; exact comp_PR hF hG)

/-! ## The basis 𝓕'' = ⟨1, L, F⁺, FG, F^□⟩ -/

def basis6L : Basis := ⟨{cst 1, funL}, {opPlusI, opBox}, {(· ∘ ·)}⟩
abbrev C6L (F : UFun) : Prop := Clos basis6L F

lemma C6L_one : C6L (cst 1) := .init (by simp [basis6L])
lemma C6L_L : C6L funL := .init (by simp [basis6L])
lemma C6L_plusI {F} (h : C6L F) : C6L (opPlusI F) := .unop (u := opPlusI) (by simp [basis6L]) h
lemma C6L_box {F} (h : C6L F) : C6L (opBox F) := .unop (u := opBox) (by simp [basis6L]) h
lemma C6L_comp {F G} (hF : C6L F) (hG : C6L G) : C6L (F ∘ G) :=
  .binop (b := (· ∘ ·)) (by simp [basis6L]) hF hG

/-- K ≡ L 1⁺ ((1⁺)⁺ L)⁺, i.e. K(x) = L(x + 2L(x) + 2) (Robinson [16, p. 664]) -/
lemma K_expr_L : funL ∘ opPlusI (cst 1) ∘ opPlusI (opPlusI (opPlusI (cst 1)) ∘ funL) = funK := by
  funext x
  obtain ⟨hx, hk⟩ := decomp x
  set t := funV x; set k := funK x
  have Lx : funL x = t - k := funL_eq x
  have e : x + 2 * funL x + 2 = funA (t + 1) + (t - k + 1) := by
    rw [Lx, funA_succ]; omega
  simp only [Function.comp, opPlusI, cst]
  rw [show 1 + (1 + funL x + funL x + x) = x + 2 * funL x + 2 by ring, e,
    funL_diag (by omega)]
  omega

lemma K_in_L : C6L funK :=
  K_expr_L ▸ C6L_comp C6L_L (C6L_comp (C6L_plusI C6L_one)
    (C6L_plusI (C6L_comp (C6L_plusI (C6L_plusI C6L_one)) C6L_L)))

theorem Theorem_6_8_L : Suitable basis6L := by
  refine suitable_by_simulation Theorem_6_8_K ?_ ?_ ?_ ?_
  · rintro F (rfl | rfl); exacts [C6L_one, K_in_L]
  · rintro u (rfl | rfl) F hF; exacts [C6L_plusI hF, C6L_box hF]
  · rintro b rfl F G hF hG; exact C6L_comp hF hG
  · exact clos_sound (by rintro F (rfl | rfl); exacts [cst_PR 1, funL_PR])
      (by rintro u (rfl | rfl) F hF; exacts [opPlusI_PR hF, opBox_PR hF])
      (by rintro b rfl F G hF hG; exact comp_PR hF hG)

/-- Theorem 6.8 -/
theorem Theorem_6_8 : Suitable basis6K ∧ Suitable basis6L := ⟨Theorem_6_8_K, Theorem_6_8_L⟩

end UPRF
