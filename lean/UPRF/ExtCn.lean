/-
  Replacing the constant 1 by any constant n: for X ∈ {E, K, L} and a set U of unary operators
  containing F⁺, the bases ⟨n, X, U, FG⟩ and ⟨1, X, U, FG⟩ generate the same closure whenever
  n ≥ 1. For U = {F⁺, F^□} (Theorems 6.7, 6.8) this gives suitable bases, and for U = {F⁺, F⁻¹}
  (`ExtGR`) the unary general recursive functions. For n = 0 every generated function fixes 0,
  so 1 is missing.

  Only F⁺ and X are used. Since n⁺(x) = x + n, every constant c + kn is generated from c;
  X then steps down from c to c - 1:
  - E: c + kn = (nc + 1)² + (c - 1) for k = nc² + 2c;
  - K: c + kn = A(2nc + 1) + (c - 1) for k = 2nc² + 3c;
  - L: two steps, c ↦ nc - c ↦ c - 1, since
       c + n(2nc² + 2c) = A(2nc) + (nc + c)   and   (nc - c) + n(2nc²) = A(2nc - 1) + (2nc - c).
-/
import UPRF.ExtGRb

namespace UPRF

noncomputable section

/-! ## The bases ⟨n, X, U, FG⟩ -/

@[clos_defs] def basisC (X : UFun) (U : Set (UFun → UFun)) (n : ℕ) : Basis :=
  ⟨{cst n, X}, U, {(· ∘ ·)}⟩

lemma basis6_C : basis6 = basisC funE {opPlusI, opBox} 1 := rfl
lemma basis6K_C : basis6K = basisC funK {opPlusI, opBox} 1 := rfl
lemma basis6L_C : basis6L = basisC funL {opPlusI, opBox} 1 := rfl
lemma basisGR_C (X : UFun) : basisGR X = basisC X {opPlusI, opInv} 1 := rfl

/-! ## Shifting constants -/

lemma shift_cst (n k c : ℕ) : (opPlusI (cst n))^[k] ∘ cst c = cst (c + k * n) := by
  funext x
  simp only [Function.comp_apply, cst]
  exact shift_pow (fun y => by simp only [opPlusI, cst]; omega) k c

section shift

variable {X : UFun} {U : Set (UFun → UFun)} {n : ℕ} (P : opPlusI ∈ U)
include P

lemma cst_shift_in {c : ℕ} (hc : Clos (basisC X U n) (cst c)) (k : ℕ) :
    Clos (basisC X U n) (cst (c + k * n)) := by
  have nC : Clos (basisC X U n) (cst n) := Clos.init (by simp [basisC])
  have : Clos (basisC X U n) (opPlusI (cst n)) := Clos.unop P nC
  rw [← shift_cst]
  exact clos_powcomp (by simp [basisC]) this hc k

lemma X_cst_in {c : ℕ} (hc : Clos (basisC X U n) (cst c)) (k : ℕ) :
    Clos (basisC X U n) (cst (X (c + k * n))) := by
  have XC : Clos (basisC X U n) X := Clos.init (by simp [basisC])
  have : Clos (basisC X U n) (X ∘ cst (c + k * n)) :=
    Clos.binop (b := fun f g : UFun => f ∘ g) (by simp [basisC]) XC (cst_shift_in P hc k)
  exact this

omit P in
/-- if X steps down from every constant c ≥ 1, then 1 is generated from n ≥ 1 -/
lemma one_by_descent (hn : 1 ≤ n)
    (step : ∀ c, Clos (basisC X U n) (cst c) → 1 ≤ c → Clos (basisC X U n) (cst (c - 1))) :
    Clos (basisC X U n) (cst 1) := by
  have h : ∀ j, j < n → Clos (basisC X U n) (cst (n - j)) := by
    intro j
    induction j with
    | zero => intro _; exact Clos.init (by simp [basisC])
    | succ j ih =>
      intro hj
      have := step _ (ih (by omega)) (by omega)
      rwa [show n - j - 1 = n - (j + 1) by omega] at this
  have := h (n - 1) (by omega)
  rwa [show n - (n - 1) = 1 by omega] at this

/-- with 1 in the closure the two bases are equivalent -/
lemma C_eq_C1 (one : Clos (basisC X U n) (cst 1)) (hn : 1 ≤ n) (F : UFun) :
    Clos (basisC X U n) F ↔ Clos (basisC X U 1) F := by
  constructor
  · revert F
    have one1 : Clos (basisC X U 1) (cst 1) := Clos.init (by simp [basisC])
    have nC : Clos (basisC X U 1) (cst n) := by
      have := cst_shift_in (n := 1) P one1 (n - 1)
      rwa [show 1 + (n - 1) * 1 = n by omega] at this
    exact clos_subset
      (fun F hF => by
        simp only [basisC, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
        rcases hF with rfl | rfl
        · exact nC
        · exact Clos.init (by simp [basisC]))
      (fun u hu F hF => Clos.unop hu hF)
      (fun b hb F G hF hG => Clos.binop hb hF hG)
  · revert F
    exact clos_subset
      (fun F hF => by
        simp only [basisC, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
        rcases hF with rfl | rfl
        · exact one
        · exact Clos.init (by simp [basisC]))
      (fun u hu F hF => Clos.unop hu hF)
      (fun b hb F G hF hG => Clos.binop hb hF hG)

end shift

/-! ## The descent for E, K, L -/

lemma E_desc {n c : ℕ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    funE (c + (n * c * c + 2 * c) * n) = c - 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [show d + 1 + (n * (d + 1) * (d + 1) + 2 * (d + 1)) * n
      = (n * (d + 1) + 1) * (n * (d + 1) + 1) + d by ring, funE_sq_add (by nlinarith)]
  omega

lemma K_desc {n c : ℕ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    funK (c + (2 * n * c * c + 3 * c) * n) = c - 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have st : funA (2 * n * (d + 1) + 1) = 2 * n * n * (d + 1) * (d + 1) + 3 * n * (d + 1) + 1 := by
    have := two_funA (2 * n * (d + 1) + 1); nlinarith
  rw [show d + 1 + (2 * n * (d + 1) * (d + 1) + 3 * (d + 1)) * n
      = funA (2 * n * (d + 1) + 1) + d by rw [st]; ring, funK_diag (by nlinarith)]
  omega

/-- for L, two steps: c ↦ nc - c ↦ c - 1 (with N = nc) -/
lemma L_desc1 {n c : ℕ} (hn : 1 ≤ n) : funL (c + (2 * n * c * c + 2 * c) * n) = n * c - c := by
  have cN : c ≤ n * c := by nlinarith
  have s : funA (2 * (n * c)) = 2 * (n * c) * (n * c) + n * c := by
    have := two_funA (2 * (n * c)); nlinarith
  rw [show c + (2 * n * c * c + 2 * c) * n = funA (2 * (n * c)) + (n * c + c) by rw [s]; ring,
    funL_diag (by omega)]
  omega

lemma L_desc2 {n c : ℕ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    funL ((n * c - c) + (2 * n * c * c) * n) = c - 1 := by
  have cN : c ≤ n * c := by nlinarith
  obtain ⟨M, hM⟩ : ∃ M, n * c = M + 1 := ⟨n * c - 1, by omega⟩
  have s : funA (2 * M + 1) + (n * c) = 2 * (n * c) * (n * c) := by
    have := two_funA (2 * M + 1); rw [hM]; nlinarith
  have e : (n * c - c) + (2 * n * c * c) * n = funA (2 * M + 1) + (2 * (n * c) - c) := by
    have : (2 * n * c * c) * n = 2 * (n * c) * (n * c) := by ring
    rw [this]; omega
  rw [e, funL_diag (by omega)]; omega

section ELK

variable {U : Set (UFun → UFun)} {n : ℕ} (P : opPlusI ∈ U) (hn : 1 ≤ n)
include P hn

lemma one_in_E : Clos (basisC funE U n) (cst 1) :=
  one_by_descent hn fun c hc c1 => by
    have := X_cst_in P hc (n * c * c + 2 * c); rwa [E_desc hn c1] at this

lemma one_in_K : Clos (basisC funK U n) (cst 1) :=
  one_by_descent hn fun c hc c1 => by
    have := X_cst_in P hc (2 * n * c * c + 3 * c); rwa [K_desc hn c1] at this

lemma one_in_L : Clos (basisC funL U n) (cst 1) :=
  one_by_descent hn fun c hc c1 => by
    have w := X_cst_in P hc (2 * n * c * c + 2 * c); rw [L_desc1 hn] at w
    have := X_cst_in P w (2 * n * c * c); rwa [L_desc2 hn c1] at this

theorem C_eq_C1_ELK (F : UFun) :
    (Clos (basisC funE U n) F ↔ Clos (basisC funE U 1) F) ∧
      (Clos (basisC funK U n) F ↔ Clos (basisC funK U 1) F) ∧
      (Clos (basisC funL U n) F ↔ Clos (basisC funL U 1) F) :=
  ⟨C_eq_C1 P (one_in_E P hn) hn F, C_eq_C1 P (one_in_K P hn) hn F,
    C_eq_C1 P (one_in_L P hn) hn F⟩

end ELK

/-! ## The constant 0: every function of ⟨0, X, U, FG⟩ fixes 0 when X(0) = 0 and every operator
  of U preserves F(0) = 0 -/

lemma C0_fix0 {X : UFun} {U : Set (UFun → UFun)} (X0 : X 0 = 0)
    (hU : ∀ u ∈ U, ∀ F : UFun, F 0 = 0 → u F 0 = 0) {F : UFun} (h : Clos (basisC X U 0) F) :
    F 0 = 0 := by
  induction h with
  | init h =>
    simp only [basisC, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · rfl
    · exact X0
  | unop hu _ ih => exact hU _ hu _ ih
  | binop hb _ _ ih₁ ih₂ =>
    simp only [basisC, Set.mem_singleton_iff] at hb; subst hb
    simp [ih₁, ih₂]

lemma U_box_fix0 : ∀ u ∈ ({opPlusI, opBox} : Set (UFun → UFun)), ∀ F : UFun, F 0 = 0 → u F 0 = 0 := by
  intro u hu F h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · simp [opPlusI, h]
  · rfl

lemma U_inv_fix0 : ∀ u ∈ ({opPlusI, opInv} : Set (UFun → UFun)), ∀ F : UFun, F 0 = 0 → u F 0 = 0 := by
  intro u hu F h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · simp [opPlusI, h]
  · exact opInv_zero h

lemma one_notin_C0 {X : UFun} {U : Set (UFun → UFun)} (X0 : X 0 = 0)
    (hU : ∀ u ∈ U, ∀ F : UFun, F 0 = 0 → u F 0 = 0) : ¬ Clos (basisC X U 0) (cst 1) :=
  fun h => by simpa [cst] using C0_fix0 X0 hU h

/-! ## Primitive recursive functions -/

lemma Ext_Cn_aux {X : UFun} (X0 : X 0 = 0) (S1 : Suitable (basisC X {opPlusI, opBox} 1))
    (eq : ∀ n, 1 ≤ n → ∀ F, Clos (basisC X {opPlusI, opBox} n) F ↔
      Clos (basisC X {opPlusI, opBox} 1) F) (n : ℕ) :
    Suitable (basisC X {opPlusI, opBox} n) ↔ 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.le_zero, one_ne_zero, iff_false]
    exact fun S => one_notin_C0 X0 U_box_fix0 ((S _).2 (cst_PR 1))
  · exact iff_of_true (fun F => (eq n hn F).trans (S1 F)) hn

theorem Ext_Cn_suitable (n : ℕ) :
    (Suitable (basisC funE {opPlusI, opBox} n) ↔ 1 ≤ n) ∧
      (Suitable (basisC funK {opPlusI, opBox} n) ↔ 1 ≤ n) ∧
      (Suitable (basisC funL {opPlusI, opBox} n) ↔ 1 ≤ n) := by
  have P : opPlusI ∈ ({opPlusI, opBox} : Set (UFun → UFun)) := by simp
  exact ⟨Ext_Cn_aux funE_small.1 Theorem_6_7 (fun n hn F => (C_eq_C1_ELK P hn F).1) n,
    Ext_Cn_aux funK_zero' Theorem_6_8_K (fun n hn F => (C_eq_C1_ELK P hn F).2.1) n,
    Ext_Cn_aux funL_zero' Theorem_6_8_L (fun n hn F => (C_eq_C1_ELK P hn F).2.2) n⟩

/-! ## General recursive functions, assuming Robinson's theorem -/

section Robinson_1950

variable {GR : UFun → Prop} (Robinson_1950_sec4_thm3 : ∀ F, CJR F ↔ GR F)
include Robinson_1950_sec4_thm3

lemma Ext_GRCn_aux {X : UFun} (X0 : X 0 = 0) (S1 : ∀ F, Clos (basisC X {opPlusI, opInv} 1) F ↔ GR F)
    (eq : ∀ n, 1 ≤ n → ∀ F, Clos (basisC X {opPlusI, opInv} n) F ↔
      Clos (basisC X {opPlusI, opInv} 1) F) (n : ℕ) :
    (∀ F, Clos (basisC X {opPlusI, opInv} n) F ↔ GR F) ↔ 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.le_zero, one_ne_zero, iff_false]
    exact fun S => one_notin_C0 X0 U_inv_fix0
      ((S _).2 ((Robinson_1950_sec4_thm3 _).1 one_in_JR))
  · exact iff_of_true (fun F => (eq n hn F).trans (S1 F)) hn

theorem Ext_GRCn (n : ℕ) :
    ((∀ F, Clos (basisC funE {opPlusI, opInv} n) F ↔ GR F) ↔ 1 ≤ n) ∧
      ((∀ F, Clos (basisC funK {opPlusI, opInv} n) F ↔ GR F) ↔ 1 ≤ n) ∧
      ((∀ F, Clos (basisC funL {opPlusI, opInv} n) F ↔ GR F) ↔ 1 ≤ n) := by
  have P : opPlusI ∈ ({opPlusI, opInv} : Set (UFun → UFun)) := by simp
  obtain ⟨hE, hK, hL⟩ := Ext_GR Robinson_1950_sec4_thm3
  exact ⟨Ext_GRCn_aux Robinson_1950_sec4_thm3 funE_small.1 hE
      (fun n hn F => (C_eq_C1_ELK P hn F).1) n,
    Ext_GRCn_aux Robinson_1950_sec4_thm3 funK_zero' hK (fun n hn F => (C_eq_C1_ELK P hn F).2.1) n,
    Ext_GRCn_aux Robinson_1950_sec4_thm3 funL_zero' hL (fun n hn F => (C_eq_C1_ELK P hn F).2.2) n⟩

end Robinson_1950

end

end UPRF
