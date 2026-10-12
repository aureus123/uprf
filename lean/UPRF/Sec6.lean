/-
  Section 6: iteration and the unary operator F⁺.
  The basis is 𝓕 = ⟨1, E, F⁺, FG, F^□⟩.

  Convention: for a function or operator defined in the paper by a formula
  `X ≡ expression`, `exprX` is the expression (built only with the operators
  of the basis) and `X_expr` / `exprX_val` state that it computes X.
-/
import UPRF.Basic

namespace UPRF

def basis6 : Basis := ⟨{cst 1, funE}, {opPlusI, opBox}, {(· ∘ ·)}⟩

/-- clos 𝓕 -/
abbrev C6 (F : UFun) : Prop := Clos basis6 F

lemma C6_one : C6 (cst 1) := .init (by simp [basis6])
lemma C6_E : C6 funE := .init (by simp [basis6])
lemma C6_plusI {F} (h : C6 F) : C6 (opPlusI F) := .unop (u := opPlusI) (by simp [basis6]) h
lemma C6_box {F} (h : C6 F) : C6 (opBox F) := .unop (u := opBox) (by simp [basis6]) h
lemma C6_comp {F G} (hF : C6 F) (hG : C6 G) : C6 (F ∘ G) :=
  .binop (b := (· ∘ ·)) (by simp [basis6]) hF hG

/-! ## First functions in clos 𝓕 -/

def funMod3 : UFun := fun x => x % 3
def funM3 : UFun := fun x => 3 * x
/-- R(x) = x + 2Rt(x), as in Lemma 5.7 -/
def funR : UFun := fun x => x + 2 * funRt x

lemma funE_small : funE 0 = 0 ∧ funE 1 = 0 ∧ funE 2 = 1 ∧ funE 3 = 2 ∧ funE 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using funE_sq_add (m := 0) (k := 0) (by omega)
  · simpa using funE_sq_add (m := 1) (k := 0) (by omega)
  · simpa using funE_sq_add (m := 1) (k := 1) (by omega)
  · simpa using funE_sq_add (m := 1) (k := 2) (by omega)
  · simpa using funE_sq_add (m := 2) (k := 0) (by omega)

lemma S_expr : opPlusI (cst 1) = funS := by
  funext x; simp [opPlusI, cst, funS, Nat.add_comm]

lemma Sgn_expr : opBox (cst 1) = funSgn := by
  funext x; cases x <;> simp [cst, funSgn]

lemma zero_expr : funE ∘ cst 1 = cst 0 := by
  funext x; simp [cst, funE_small.2.1]

lemma D_expr : opPlusI (opPlusI (cst 0)) = funD := by
  funext x; simp [opPlusI, cst, funD]; omega

lemma M3_expr : opPlusI funD = funM3 := by
  funext x; simp [opPlusI, funD, funM3]; omega

lemma O_expr : funE ∘ funD ∘ funS ∘ funSgn = funO := by
  funext x; by_cases h : x = 0 <;> simp [funSgn, funS, funD, funO, h, funE_small]

lemma Q_expr : funO ∘ funE = funQ := by
  funext x; simp [funO, funQ_iff]

lemma Mod3_expr : opBox (funE ∘ funS ∘ funS) = funMod3 := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBox_succ, ih]
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h | h <;>
      simp [funMod3, funS, h, funE_small, Nat.add_mod]

/-- the step of R: R(n+1) = (D Q S S S)⁺ (S (R n)) -/
lemma R_step (n : ℕ) :
    opPlusI (funD ∘ funQ ∘ funS ∘ funS ∘ funS) (funS (funR n)) = funR (n + 1) := by
  set r := funRt n with hr
  have lo := funRt_sq_le n; have hi := funRt_lt n
  rw [← hr] at lo hi
  have v : opPlusI (funD ∘ funQ ∘ funS ∘ funS ∘ funS) (funS (funR n))
      = 2 * funQ (n + 2 * r + 4) + (n + 2 * r + 1) := by
    simp only [opPlusI, funD, funS, funR, Function.comp, ← hr]
  rw [v]
  by_cases hsq : (r + 1) * (r + 1) = n + 1
  · have rt : funRt (n + 1) = r + 1 := funRt_unique (by omega) (by nlinarith)
    have : n + 2 * r + 4 = (r + 2) * (r + 2) + 0 := by nlinarith
    have q : funQ (n + 2 * r + 4) = 1 := by
      rw [funQ_iff, this, funE_sq_add (by omega)]; rfl
    simp only [q, funR, rt]; omega
  · have h1 : n + 1 < (r + 1) * (r + 1) := by omega
    have rt : funRt (n + 1) = r := funRt_unique (by nlinarith) h1
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le lo
    have hk2 : k + 3 ≤ 2 * (r + 1) := by nlinarith
    have : n + 2 * r + 4 = (r + 1) * (r + 1) + (k + 3) := by rw [hk]; ring
    have q : funQ (n + 2 * r + 4) = 0 := by
      rw [funQ_iff, this, funE_sq_add hk2]; simp
    simp only [q, funR, rt]; omega

lemma R_expr : opBox (opPlusI (funD ∘ funQ ∘ funS ∘ funS ∘ funS) ∘ funS) = funR := by
  funext n
  induction n with
  | zero => simp [funR, funRt]
  | succ n ih => rw [opBox_succ, ih, Function.comp_apply, R_step]

lemma Sq_expr : opBox (funS ∘ funR) = funSq := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [opBox_succ, ih, Function.comp, funS, funR, funSq, funRt_sq]; ring

lemma S_in : C6 funS := S_expr ▸ C6_plusI C6_one
lemma Sgn_in : C6 funSgn := Sgn_expr ▸ C6_box C6_one
lemma zero_in : C6 (cst 0) := zero_expr ▸ C6_comp C6_E C6_one
lemma D_in : C6 funD := D_expr ▸ C6_plusI (C6_plusI zero_in)
lemma M3_in : C6 funM3 := M3_expr ▸ C6_plusI D_in
lemma O_in : C6 funO := O_expr ▸ C6_comp C6_E (C6_comp D_in (C6_comp S_in Sgn_in))
lemma Q_in : C6 funQ := Q_expr ▸ C6_comp O_in C6_E
lemma Mod3_in : C6 funMod3 := Mod3_expr ▸ C6_box (C6_comp C6_E (C6_comp S_in S_in))
lemma R_in : C6 funR :=
  R_expr ▸ C6_box (C6_comp (C6_plusI (C6_comp D_in (C6_comp Q_in (C6_comp S_in
    (C6_comp S_in S_in))))) S_in)
lemma Sq_in : C6 funSq := Sq_expr ▸ C6_box (C6_comp S_in R_in)

/-! ## Definition 6.1 (meaningful when F(x) ≥ x, G(x) ≥ x and, for ⊖, F(x) ≥ G(x)²) -/

def opMinusI (F : UFun) : UFun := fun x => F x - x
def opOplus (F G : UFun) : UFun := fun x => F x + G x * G x
def opOminus (F G : UFun) : UFun := fun x => F x - G x * G x
def opOtimes (F G : UFun) : UFun := fun x => F x * G x

/-! ## Lemma 6.2: F⁻ ≡ E S (M₃ F E)⁺ (Sq F⁺)⁺ -/

def exprMinusI (F : UFun) : UFun :=
  funE ∘ funS ∘ opPlusI (funM3 ∘ F ∘ funE) ∘ opPlusI (funSq ∘ opPlusI F)

lemma exprMinusI_in {F} (h : C6 F) : C6 (exprMinusI F) :=
  C6_comp C6_E (C6_comp S_in (C6_comp (C6_plusI (C6_comp M3_in (C6_comp h C6_E)))
    (C6_plusI (C6_comp Sq_in (C6_plusI h)))))

/-- pointwise correctness: only F(x) ≥ x at the point x is needed -/
lemma exprMinusI_val {F : UFun} {x : ℕ} (h : x ≤ F x) : exprMinusI F x = F x - x := by
  have ey : funE ((F x + x) * (F x + x) + x) = x := funE_sq_add (by omega)
  simp only [exprMinusI, Function.comp, opPlusI, funSq, funM3, funS, ey]
  rw [← robinson_diff_E h]; congr 1; ring

theorem Lemma_6_2 {F : UFun} (hF : C6 F) (h : ∀ x, x ≤ F x) : C6 (opMinusI F) := by
  have : exprMinusI F = opMinusI F := funext fun x => exprMinusI_val (h x)
  exact this ▸ exprMinusI_in hF

/-! ## Lemma 6.3: Hf ≡ ((S Mod₃⁺)^□)⁻ and Rt ≡ Hf R⁻ -/

lemma Hf_aux (n : ℕ) : opBox (funS ∘ opPlusI funMod3) n = n + n / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [opBox_succ, ih]; simp only [Function.comp, funS, opPlusI, funMod3]; omega

def exprHf : UFun := exprMinusI (opBox (funS ∘ opPlusI funMod3))
def exprRt : UFun := funHf ∘ exprMinusI funR

lemma Hf_expr : exprHf = funHf := by
  funext x; rw [exprHf, exprMinusI_val (by rw [Hf_aux]; omega), Hf_aux]
  simp [funHf]

lemma Rt_expr : exprRt = funRt := by
  funext x; simp only [exprRt, Function.comp]
  rw [exprMinusI_val (by simp [funR])]; simp [funR, funHf]

theorem Lemma_6_3 : C6 funHf ∧ C6 funRt := by
  have Hf : C6 funHf :=
    Hf_expr ▸ exprMinusI_in (C6_box (C6_comp S_in (C6_plusI Mod3_in)))
  exact ⟨Hf, Rt_expr ▸ C6_comp Hf (exprMinusI_in R_in)⟩

lemma Hf_in : C6 funHf := Lemma_6_3.1
lemma Rt_in : C6 funRt := Lemma_6_3.2

/-! ## Lemma 6.4: F ⊕ G ≡ (F⁻ E)⁺ (Sq G)⁺ and F ⊖ G ≡ (F⁺ E)⁻ (Sq G)⁺ -/

def exprOplus (F G : UFun) : UFun := opPlusI (exprMinusI F ∘ funE) ∘ opPlusI (funSq ∘ G)
def exprOminus (F G : UFun) : UFun := exprMinusI (opPlusI F ∘ funE) ∘ opPlusI (funSq ∘ G)

lemma exprOplus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (exprOplus F G) :=
  C6_comp (C6_plusI (C6_comp (exprMinusI_in hF) C6_E)) (C6_plusI (C6_comp Sq_in hG))

lemma exprOminus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (exprOminus F G) :=
  C6_comp (exprMinusI_in (C6_comp (C6_plusI hF) C6_E)) (C6_plusI (C6_comp Sq_in hG))

lemma E_SqG {G : UFun} {x : ℕ} (h : x ≤ G x) : funE (G x * G x + x) = x :=
  funE_sq_add (by omega)

lemma exprOplus_val {F G : UFun} {x : ℕ} (hF : x ≤ F x) (hG : x ≤ G x) :
    exprOplus F G x = F x + G x * G x := by
  simp only [exprOplus, Function.comp, opPlusI, funSq, E_SqG hG, exprMinusI_val hF]; omega

lemma exprOminus_val {F G : UFun} {x : ℕ} (hG : x ≤ G x) (h : G x * G x ≤ F x) :
    exprOminus F G x = F x - G x * G x := by
  simp only [exprOminus, Function.comp, opPlusI, funSq]
  rw [exprMinusI_val (by simp only [Function.comp, opPlusI, E_SqG hG]; omega)]
  simp only [Function.comp, opPlusI, E_SqG hG]; omega

theorem Lemma_6_4 {F G : UFun} (hF : C6 F) (hG : C6 G) (hFx : ∀ x, x ≤ F x)
    (hGx : ∀ x, x ≤ G x) :
    C6 (opOplus F G) ∧ ((∀ x, G x * G x ≤ F x) → C6 (opOminus F G)) := by
  refine ⟨?_, fun h => ?_⟩
  · have : exprOplus F G = opOplus F G := funext fun x => exprOplus_val (hFx x) (hGx x)
    exact this ▸ exprOplus_in hF hG
  · have : exprOminus F G = opOminus F G := funext fun x => exprOminus_val (hGx x) (h x)
    exact this ▸ exprOminus_in hF hG

/-! ## Lemma 6.5: P^ ≡ ((Sq⁺)⁺)⁺ ⊖ S, i.e. P^(x + 1) = x, and
  F ⊗ G ≡ Rt((Hf Hf (Sq P^((Sq S Sq F ⊕ G) ⊖ Sq F) ⊖ Sq G)) ⊖ Sq F) -/

def exprPhat : UFun := exprOminus (opPlusI (opPlusI (opPlusI funSq))) funS

lemma Phat_in : C6 exprPhat := exprOminus_in (C6_plusI (C6_plusI (C6_plusI Sq_in))) S_in

lemma Phat_succ (x : ℕ) : exprPhat (x + 1) = x := by
  rw [exprPhat, exprOminus_val (by simp [funS]) (by simp [opPlusI, funSq, funS]; nlinarith)]
  simp only [opPlusI, funSq, funS]
  have : (x + 1) * (x + 1) + (x + 1) + (x + 1) + (x + 1) = x + (x + 1 + 1) * (x + 1 + 1) := by
    ring
  omega

def exprOtimes (F G : UFun) : UFun :=
  funRt ∘ exprOminus
    (funHf ∘ funHf ∘ exprOminus (funSq ∘ exprPhat ∘
      exprOminus (exprOplus (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F)) (funSq ∘ G))
    (funSq ∘ F)

lemma exprOtimes_in {F G} (hF : C6 F) (hG : C6 G) : C6 (exprOtimes F G) :=
  C6_comp Rt_in (exprOminus_in (C6_comp Hf_in (C6_comp Hf_in (exprOminus_in
    (C6_comp Sq_in (C6_comp Phat_in (exprOminus_in (exprOplus_in
      (C6_comp Sq_in (C6_comp S_in (C6_comp Sq_in hF))) hG) (C6_comp Sq_in hF))))
    (C6_comp Sq_in hG)))) (C6_comp Sq_in hF))

lemma le_mul_self' (n : ℕ) : n ≤ n * n := Nat.le_mul_self n

lemma exprOtimes_val {F G : UFun} {x : ℕ} (hF : x ≤ F x) (hG : x ≤ G x) :
    exprOtimes F G x = F x * G x := by
  set a := F x with ha
  set b := G x with hb
  have xaa : x ≤ a * a := le_trans hF (le_mul_self' a)
  have xbb : x ≤ b * b := le_trans hG (le_mul_self' b)
  have SqF : (funSq ∘ F) x = a * a := rfl
  have SqG : (funSq ∘ G) x = b * b := rfl
  -- (Sq S Sq F ⊕ G)(x) = (a² + 1)² + b²
  have h1x : x ≤ (funSq ∘ funS ∘ funSq ∘ F) x := by
    simp only [Function.comp, funSq, funS, ← ha]; nlinarith
  have v1 : exprOplus (funSq ∘ funS ∘ funSq ∘ F) G x = (a * a + 1) * (a * a + 1) + b * b := by
    rw [exprOplus_val h1x hG]; rfl
  -- ⊖ Sq F gives 2a² + 1 + b²
  have v2 : exprOminus (exprOplus (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F) x
      = 2 * (a * a) + b * b + 1 := by
    rw [exprOminus_val (SqF ▸ xaa) (by rw [SqF, v1]; nlinarith), v1, SqF]
    have : (a * a + 1) * (a * a + 1) + b * b = 2 * (a * a) + b * b + 1 + a * a * (a * a) := by
      ring
    omega
  -- Sq P^ gives (2a² + b²)²
  set c := 2 * (a * a) + b * b
  have v3 : (funSq ∘ exprPhat ∘ exprOminus (exprOplus (funSq ∘ funS ∘ funSq ∘ F) G)
      (funSq ∘ F)) x = c * c := by
    simp only [Function.comp_apply] at v2 ⊢; rw [v2, Phat_succ]; rfl
  -- ⊖ Sq G gives 4a⁴ + 4a²b²; Hf Hf gives a⁴ + a²b²
  have v4 := exprOminus_val (F := funSq ∘ exprPhat ∘ exprOminus (exprOplus
      (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F)) (SqG ▸ xbb)
    (by rw [SqG, v3]; exact Nat.mul_le_mul (by omega) (by omega))
  rw [v3, SqG] at v4
  have e4 : c * c - b * b * (b * b) = 2 * (2 * (a * a * (a * a) + a * a * (b * b))) := by
    have : c * c = b * b * (b * b) + 2 * (2 * (a * a * (a * a) + a * a * (b * b))) := by ring
    omega
  set w := a * a * (a * a) + a * a * (b * b)
  have v5 : (funHf ∘ funHf ∘ exprOminus (funSq ∘ exprPhat ∘ exprOminus (exprOplus
      (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F)) (funSq ∘ G)) x = w := by
    simp only [Function.comp_apply] at v4 ⊢; rw [v4, e4]; simp [funHf]
  -- ⊖ Sq F gives a²b², and Rt gives ab
  have v6 := exprOminus_val (F := funHf ∘ funHf ∘ exprOminus (funSq ∘ exprPhat ∘
      exprOminus (exprOplus (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F)) (funSq ∘ G))
    (G := funSq ∘ F) (SqF ▸ xaa) (by rw [SqF, v5]; omega)
  rw [v5, SqF] at v6
  simp only [exprOtimes, Function.comp_apply] at v6 ⊢
  rw [v6]
  have : w - a * a * (a * a) = (a * b) * (a * b) := by
    have : w = a * a * (a * a) + (a * b) * (a * b) := by ring
    omega
  rw [this, funRt_sq]

theorem Lemma_6_5 {F G : UFun} (hF : C6 F) (hG : C6 G) (hFx : ∀ x, x ≤ F x)
    (hGx : ∀ x, x ≤ G x) : C6 (opOtimes F G) := by
  have : exprOtimes F G = opOtimes F G := funext fun x => exprOtimes_val (hFx x) (hGx x)
  exact this ▸ exprOtimes_in hF hG

/-! ## Lemma 6.6: F + G ≡ ((Rt((D(F⁺ ⊗ G⁺) ⊕ F⁺) ⊕ G⁺))⁻)⁻ and
  F - G ≡ E S (Sq(F + G) + M₃ F + G) -/

def exprPlus (F G : UFun) : UFun :=
  exprMinusI (exprMinusI (funRt ∘ exprOplus (exprOplus
    (funD ∘ exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F)) (opPlusI G)))

def exprMinus (F G : UFun) : UFun :=
  funE ∘ funS ∘ exprPlus (exprPlus (funSq ∘ exprPlus F G) (funM3 ∘ F)) G

lemma exprPlus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (exprPlus F G) :=
  exprMinusI_in (exprMinusI_in (C6_comp Rt_in (exprOplus_in (exprOplus_in
    (C6_comp D_in (exprOtimes_in (C6_plusI hF) (C6_plusI hG))) (C6_plusI hF)) (C6_plusI hG))))

lemma exprMinus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (exprMinus F G) :=
  C6_comp C6_E (C6_comp S_in (exprPlus_in (exprPlus_in (C6_comp Sq_in (exprPlus_in hF hG))
    (C6_comp M3_in hF)) hG))

lemma exprPlus_val (F G : UFun) (x : ℕ) : exprPlus F G x = F x + G x := by
  set a := F x + x with ha
  set b := G x + x with hb
  have pF : opPlusI F x = a := rfl
  have pG : opPlusI G x = b := rfl
  have t : exprOtimes (opPlusI F) (opPlusI G) x = a * b :=
    exprOtimes_val (by simp [opPlusI]) (by simp [opPlusI])
  have x2ab : x ≤ 2 * (a * b) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · omega
    · have : 1 ≤ b := by omega
      nlinarith
  have o1 : exprOplus (funD ∘ exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F) x
      = 2 * (a * b) + a * a := by
    rw [exprOplus_val (by simp only [Function.comp, funD, t]; omega) (by rw [pF]; omega)]
    simp only [Function.comp, funD, t, pF]
  have o2 : exprOplus (exprOplus (funD ∘ exprOtimes (opPlusI F) (opPlusI G)) (opPlusI F))
      (opPlusI G) x = (a + b) * (a + b) := by
    rw [exprOplus_val (by rw [o1]; omega) (by rw [pG]; omega), o1, pG]; ring
  have rH : (funRt ∘ exprOplus (exprOplus (funD ∘ exprOtimes (opPlusI F) (opPlusI G))
      (opPlusI F)) (opPlusI G)) x = a + b := by
    simp only [Function.comp_apply]; rw [o2, funRt_sq]
  rw [exprPlus, exprMinusI_val (by rw [exprMinusI_val (by omega), rH]; omega),
    exprMinusI_val (by omega), rH]
  omega

lemma exprPlus_eq (F G : UFun) : exprPlus F G = opPlus F G :=
  funext fun x => exprPlus_val F G x

/-- the difference function computed by F - G (footnote 8): it is F - G where F ≥ G,
  and some other value elsewhere -/
def dE (a b : ℕ) : ℕ := funE ((a + b) * (a + b) + 3 * a + b + 1)

lemma dE_diff {a b : ℕ} (h : b ≤ a) : dE a b = a - b := robinson_diff_E h

def opDiffE (F G : UFun) : UFun := fun x => dE (F x) (G x)

lemma exprMinus_eq (F G : UFun) : exprMinus F G = opDiffE F G := by
  funext x
  rw [exprMinus, Function.comp_apply, Function.comp_apply, exprPlus_val, exprPlus_val,
    Function.comp_apply, exprPlus_val]
  rfl

theorem Lemma_6_6 {F G : UFun} (hF : C6 F) (hG : C6 G) :
    C6 (opPlus F G) ∧ C6 (opDiffE F G) ∧ ((∀ x, G x ≤ F x) → C6 (opMinus F G)) := by
  refine ⟨exprPlus_eq F G ▸ exprPlus_in hF hG, exprMinus_eq F G ▸ exprMinus_in hF hG,
    fun h => ?_⟩
  have : opDiffE F G = opMinus F G := funext fun x => dE_diff (h x)
  exact this ▸ exprMinus_eq F G ▸ exprMinus_in hF hG

end UPRF
