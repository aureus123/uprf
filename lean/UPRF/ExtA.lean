/-
  Extension of Remark 6.9 to iteration from any fixed a ≥ 2, answering the question left open
  at the end of Section 6:
    ⟨X, F⁺, FG, F^□⁽ᵃ⁾⟩ is suitable for every a ≥ 2 and X ∈ {E, K, L}.
  Together with Remark 6.9 (a = 1) this covers every a ≥ 1.
-/
import UPRF.Rem69

namespace UPRF

/-! ## General facts -/

macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opBoxA _))

/-- the basis ⟨X, F⁺, FG, F^□⁽ᵃ⁾⟩ -/
@[clos_defs] def basisA (X : UFun) (a : ℕ) : Basis := ⟨{X}, {opPlusI, opBoxA a}, {(· ∘ ·)}⟩

lemma basis69_eq (X : UFun) : basis69 X = basisA X 1 := rfl

/-- finite powers F^k G (composition) stay in any closure containing (∘) -/
lemma clos_powcomp {B : Basis} (hc : (fun f g : UFun => f ∘ g) ∈ B.binops) {F G : UFun}
    (hF : Clos B F) (hG : Clos B G) (k : ℕ) : Clos B (F^[k] ∘ G) := by
  induction k with
  | zero => exact hG
  | succ k ih => rw [Function.iterate_succ', Function.comp_assoc]; exact Clos.binop hc hF ih

/-- F^k, when the identity is in the closure -/
lemma clos_iter {B : Basis} (hc : (fun f g : UFun => f ∘ g) ∈ B.binops) {F : UFun}
    (hI : Clos B funI) (hF : Clos B F) (k : ℕ) : Clos B F^[k] :=
  clos_powcomp hc hF hI k

macro_rules | `(tactic| clos_hint) => `(tactic| with_reducible apply clos_powcomp)
macro_rules | `(tactic| clos_hint) => `(tactic| with_reducible apply clos_iter)

lemma funS_pow (k x : ℕ) : funS^[k] x = x + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma shift_pow {F : UFun} {c : ℕ} (h : ∀ y, F y = y + c) (k x : ℕ) : F^[k] x = x + k * c := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, h]; ring

/-- a predecessor (P(x + 1) = x) undoes k successors -/
lemma pred_pow {P : UFun} (h : ∀ x, P (x + 1) = x) (k x : ℕ) : P^[k] (x + k) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ← Nat.add_assoc, h, ih]

/-- recovering iteration from 0 out of iteration from a (as in Remark 5.10 of the paper):
  F^□ ≡ P^a (S^a F P^a)^□⁽ᵃ⁾ -/
lemma box_from_boxA {P : UFun} (hP : ∀ x, P (x + 1) = x) (a : ℕ) (F : UFun) :
    P^[a] ∘ opBoxA a (funS^[a] ∘ F ∘ P^[a]) = opBox F := by
  have aux : ∀ n, opBoxA a (funS^[a] ∘ F ∘ P^[a]) n = opBox F n + a := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [opBoxA_succ, ih, opBox_succ]; simp [funS_pow, pred_pow hP]
  funext n; simp [aux, pred_pow hP]

/-- M_r ≡ (…(0̄⁺)⁺…)⁺ (r times), i.e. M_r(x) = rx -/
def funM (r : ℕ) : UFun := opPlusI^[r] (cst 0)

lemma funM_apply (r x : ℕ) : funM r x = r * x := by
  induction r with
  | zero => simp [funM, cst]
  | succ r ih =>
    simp only [funM, Function.iterate_succ_apply'] at ih ⊢
    simp only [opPlusI, ih]; ring

/-- the chain N = T₂ T₃ ⋯ T_{k+1} -/
def Nchain (T : ℕ → UFun) : ℕ → UFun
  | 0 => funI
  | k + 1 => Nchain T k ∘ T (k + 2)

lemma Nchain_val {T : ℕ → UFun} (h1 : ∀ j, 2 ≤ j → T j j = j - 1) (h0 : ∀ j, T j 0 = 0)
    (k : ℕ) : Nchain T k (k + 1) = 1 ∧ Nchain T k 0 = 0 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · simp only [Nchain, Function.comp_apply]
      rw [h1 _ (by omega), show k + 1 + 1 - 1 = k + 1 by omega]; exact ih.1
    · simp only [Nchain, Function.comp_apply, h0]; exact ih.2

/-! ## The common part of the three cases

  Data: the initial function X, the starting value a ≥ 2, and multipliers m with
  X(m(j) j) = j - 1, so that T_j ≡ X M_{m(j)} maps j to j - 1. -/

structure ExtA (X : UFun) (a : ℕ) (m : ℕ → ℕ) : Prop where
  two_le : 2 ≤ a
  zero_in : Clos (basisA X a) (cst 0)
  X0 : X 0 = 0
  Xm : ∀ j, 2 ≤ j → X (m j * j) = j - 1

def funT (X : UFun) (m : ℕ → ℕ) (j : ℕ) : UFun := X ∘ funM (m j)

namespace ExtA

variable {X : UFun} {a : ℕ} {m : ℕ → ℕ} (h : ExtA X a m)
include h

lemma M_in (r : ℕ) : Clos (basisA X a) (funM r) := by
  induction r with
  | zero => exact h.zero_in
  | succ r ih =>
    rw [funM, Function.iterate_succ_apply']; exact Clos.unop (by clos_mem) ih

lemma I_in : Clos (basisA X a) funI := by
  have := h.M_in 1
  rwa [show funM 1 = funI from funext fun x => by simp [funM_apply, funI]] at this

lemma D_in : Clos (basisA X a) funD := by
  have := h.M_in 2
  rwa [show funM 2 = funD from funext fun x => by simp [funM_apply, funD]] at this

lemma T_in (j : ℕ) : Clos (basisA X a) (funT X m j) := by
  have := h.M_in (m j); unfold funT; clos_solve

lemma N_val (k : ℕ) : Nchain (funT X m) k (k + 1) = 1 ∧ Nchain (funT X m) k 0 = 0 :=
  Nchain_val (fun j hj => by simp [funT, funM_apply, h.Xm j hj])
    (fun j => by simp [funT, funM_apply, h.X0]) k

lemma N_in (k : ℕ) : Clos (basisA X a) (Nchain (funT X m) k) := by
  induction k with
  | zero => exact h.I_in
  | succ k ih => have := h.T_in (k + 2); simp only [Nchain]; clos_solve

/-- the constant a is I^□⁽ᵃ⁾, and 1̄ ≡ N ā with N = T₂ ⋯ T_a -/
lemma one_expr : Nchain (funT X m) (a - 1) ∘ opBoxA a funI = cst 1 := by
  have e : ∀ n, opBoxA a funI n = a := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [opBoxA_succ, ih]; rfl
  funext x
  have := (h.N_val (a - 1)).1
  rw [show a - 1 + 1 = a by have := h.two_le; omega] at this
  simp [e, this, cst]

/-- cosignum: O ≡ N 0̄^□⁽ᵃ⁾ (the iteration of 0̄ from a has values a, 0, 0, …) -/
lemma O_expr : Nchain (funT X m) (a - 1) ∘ opBoxA a (cst 0) = funO := by
  funext n
  cases n with
  | zero =>
    have := (h.N_val (a - 1)).1
    rw [show a - 1 + 1 = a by have := h.two_le; omega] at this
    simp [this, funO]
  | succ n => simp [cst, (h.N_val (a - 1)).2, funO]

lemma one_in : Clos (basisA X a) (cst 1) := by
  have := h.N_in (a - 1); have := h.I_in
  rw [← h.one_expr]; clos_solve

lemma S_in : Clos (basisA X a) funS := by
  have := h.one_in; rw [← S_expr]; clos_solve

lemma O_in : Clos (basisA X a) funO := by
  have := h.N_in (a - 1); have := h.zero_in
  rw [← h.O_expr]; clos_solve

/-- with any predecessor in the closure, iteration from 0 is available -/
lemma box_in {P : UFun} (hPin : Clos (basisA X a) P) (hP : ∀ x, P (x + 1) = x)
    {F : UFun} (hF : Clos (basisA X a) F) : Clos (basisA X a) (opBox F) := by
  have := h.I_in; have := h.S_in
  rw [← box_from_boxA hP a]; clos_solve

end ExtA

/-- for X with X(0) = 0 and X(y) < y for y > 0: 0̄ ≡ X^a X^□⁽ᵃ⁾ -/
lemma decreasing_zero {X : UFun} (X0 : X 0 = 0) (Xlt : ∀ y, 0 < y → X y < y) (a : ℕ) :
    X^[a] ∘ opBoxA a X = cst 0 := by
  have le : ∀ n, opBoxA a X n ≤ a := by
    intro n; induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [opBoxA_succ]
      rcases Nat.eq_zero_or_pos (opBoxA a X n) with h | h
      · rw [h, X0]; exact Nat.zero_le _
      · exact le_trans (Xlt _ h).le ih
  have pow : ∀ k y, y ≤ k → X^[k] y = 0 := by
    intro k; induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy; rw [Function.iterate_succ_apply]; apply ih
      rcases Nat.eq_zero_or_pos y with h | h
      · rw [h, X0]; exact Nat.zero_le _
      · have := Xlt y h; omega
  funext n; exact pow a _ (le n)

/-! ## The case X = E -/

lemma funE_lt {y : ℕ} (hy : 0 < y) : funE y < y := by
  have hr : 1 ≤ funRt y := Nat.sqrt_pos.2 hy
  have := funRt_sq_le y
  have : 1 * 1 ≤ funRt y * funRt y := Nat.mul_le_mul hr hr
  simp only [funE]; omega

lemma zero_in_E (a : ℕ) : Clos (basisA funE a) (cst 0) := by
  rw [← decreasing_zero funE_small.1 (fun y => funE_lt) a]; clos_solve

lemma Xm_E {j : ℕ} (hj : 2 ≤ j) : funE ((j - 1) * j) = j - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, show i * (i + 1) = i * i + i by ring, funE_sq_add (by omega)]

lemma locE {a : ℕ} (ha : 2 ≤ a) : ExtA funE a (fun j => j - 1) :=
  ⟨ha, zero_in_E a, funE_small.1, fun _ hj => Xm_E hj⟩

/-- the construction for E: with c = a² + a + 4,
  B ≡ (S (D Q S^c)⁺)^□⁽ᵃ⁾ satisfies B(n) + a² + a = R(n + a²), i.e. B(n) = n + 2⌊√(n + a²)⌋ - a;
  G ≡ (S^{a+1} B)^□⁽ᵃ⁾ satisfies G(n) = n² + 2an + a; and P^ ≡ E S^d G⁺, d = a² - a - 1,
  is a predecessor. -/
noncomputable def funHE (a : ℕ) : UFun := funS ∘ opPlusI (funD ∘ funQ ∘ funS^[a * a + a + 4])
noncomputable def funBE (a : ℕ) : UFun := opBoxA a (funHE a)
noncomputable def funGE (a : ℕ) : UFun := opBoxA a (funS^[a + 1] ∘ funBE a)
noncomputable def exprPE (a : ℕ) : UFun := funE ∘ funS^[a * a - a - 1] ∘ opPlusI (funGE a)

lemma R_rec (t : ℕ) : funR (t + 1) = 2 * funQ (funR t + 4) + funR t + 1 := by
  rw [← R_step]; simp only [opPlusI, funD, funS, Function.comp]; ring_nf

lemma HE_val (a y : ℕ) : funHE a y = 2 * funQ (y + (a * a + a + 4)) + y + 1 := by
  simp only [funHE, Function.comp, opPlusI, funD, funS_pow, funS]

lemma BE_val (a n : ℕ) : funBE a n + a * a + a = funR (n + a * a) := by
  induction n with
  | zero => simp only [funBE, opBoxA_zero, Nat.zero_add, funR, funRt_sq]; ring
  | succ n ih =>
    have arg : funBE a n + (a * a + a + 4) = funR (n + a * a) + 4 := by rw [← ih]; ring
    rw [funBE, opBoxA_succ, ← funBE, HE_val, arg, show n + 1 + a * a = n + a * a + 1 by ring,
      R_rec, ← ih]
    ring

lemma GE_val (a n : ℕ) : funGE a n = n * n + 2 * a * n + a := by
  induction n with
  | zero => simp [funGE]
  | succ n ih =>
    have rt : funRt (n * n + 2 * a * n + a + a * a) = n + a := by
      rw [show n * n + 2 * a * n + a + a * a = (n + a) * (n + a) + a by ring]
      exact funRt_sq_add (by omega)
    have b := BE_val a (n * n + 2 * a * n + a)
    simp only [funR, rt] at b
    rw [funGE, opBoxA_succ, ← funGE, ih, Function.comp_apply, funS_pow]
    linarith

lemma PE_succ {a : ℕ} (ha : 2 ≤ a) (k : ℕ) : exprPE a (k + 1) = k := by
  have h2 : 2 * a ≤ a * a := Nat.mul_le_mul_right a ha
  obtain ⟨d, hd⟩ : ∃ d, a * a = d + a + 1 :=
    ⟨a * a - a - 1, by generalize a * a = s at h2 ⊢; omega⟩
  have e : a * a - a - 1 = d := by rw [hd]; omega
  simp only [exprPE, Function.comp, opPlusI, funS_pow, GE_val, e]
  rw [show (k + 1) * (k + 1) + 2 * a * (k + 1) + a + (k + 1) + d = (k + 1 + a) * (k + 1 + a) + k
    by linarith, funE_sq_add (by omega)]

lemma PE_in {a : ℕ} (ha : 2 ≤ a) : Clos (basisA funE a) (exprPE a) := by
  have L := locE ha
  have := L.S_in; have := L.D_in; have := L.I_in
  have : Clos (basisA funE a) funQ := by have := L.O_in; rw [← Q_expr]; clos_solve
  unfold exprPE funGE funBE funHE; clos_solve

theorem Ext_a_E {a : ℕ} (ha : 2 ≤ a) : Suitable (basisA funE a) := by
  have L := locE ha
  have one := L.one_in
  have box : ∀ F, Clos (basisA funE a) F → Clos (basisA funE a) (opBox F) :=
    fun _ hF => L.box_in (PE_in ha) (PE_succ ha) hF
  simulate Theorem_6_7

/-! ## The case X = K -/

lemma funK_lt {y : ℕ} (hy : 0 < y) : funK y < y := by
  obtain ⟨hx, hk⟩ := decomp y
  rcases Nat.eq_zero_or_pos (funV y) with h | h
  · omega
  · have : funA 1 ≤ funA (funV y) := funA_mono h
    rw [funA_one] at this; omega

lemma zero_in_K (a : ℕ) : Clos (basisA funK a) (cst 0) := by
  rw [← decreasing_zero funK_zero (fun y => funK_lt) a]; clos_solve

lemma Xm_K {j : ℕ} (hj : 2 ≤ j) : funK ((2 * j - 2) * j) = j - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := two_funA (2 * i)
  rw [show 2 * (i + 1) - 2 = 2 * i by omega,
    show 2 * i * (i + 1) = funA (2 * i) + i by nlinarith, funK_diag (by omega)]
  omega

lemma locK {a : ℕ} (ha : 2 ≤ a) : ExtA funK a (fun j => 2 * j - 2) :=
  ⟨ha, zero_in_K a, funK_zero, fun _ hj => Xm_K hj⟩

/-- the construction for K: with c = A(a), B ≡ (S² (K S^c)⁺)^□⁽ᵃ⁾ satisfies
  B(n) + A(a) + 1 = A(n + a + 1), and P^ ≡ K S^c B⁺ is a predecessor. -/
def funBK (a : ℕ) : UFun := opBoxA a (funS^[2] ∘ opPlusI (funK ∘ funS^[funA a]))
def exprPK (a : ℕ) : UFun := funK ∘ funS^[funA a] ∘ opPlusI (funBK a)

lemma BK_val (a n : ℕ) : funBK a n + funA a + 1 = funA (n + a + 1) := by
  induction n with
  | zero => simp only [funBK, opBoxA_zero, funA_succ, Nat.zero_add]; ring
  | succ n ih =>
    have arg : funBK a n + funA a = funA (n + a) + (n + a) := by
      have := funA_succ (n + a); omega
    have k : funK (funBK a n + funA a) = n + a := by rw [arg]; exact funK_diag le_rfl
    rw [funBK, opBoxA_succ, ← funBK]
    simp only [Function.comp, opPlusI, funS_pow, k]
    rw [show n + 1 + a + 1 = (n + a + 1) + 1 by ring, funA_succ (n + a + 1), ← ih]; ring

lemma PK_succ (a k : ℕ) : exprPK a (k + 1) = k := by
  have := BK_val a (k + 1)
  simp only [exprPK, Function.comp, opPlusI, funS_pow]
  rw [show funBK a (k + 1) + (k + 1) + funA a = funA (k + 1 + a + 1) + k by omega,
    funK_diag (by omega)]

lemma PK_in {a : ℕ} (ha : 2 ≤ a) : Clos (basisA funK a) (exprPK a) := by
  have L := locK ha
  have := L.S_in; have := L.I_in
  unfold exprPK funBK; clos_solve

theorem Ext_a_K {a : ℕ} (ha : 2 ≤ a) : Suitable (basisA funK a) := by
  have L := locK ha
  have one := L.one_in
  have box : ∀ F, Clos (basisA funK a) F → Clos (basisA funK a) (opBox F) :=
    fun _ hF => L.box_in (PK_in ha) (PK_succ a) hF
  simulate Theorem_6_8_K

/-! ## The case X = L -/

/-- 0̄ ≡ L L⁺, because L(x + L(x)) = 0 -/
lemma zero_expr_L : funL ∘ opPlusI funL = cst 0 := by
  funext x
  obtain ⟨hx, hk⟩ := decomp x
  have Lx : funL x = funV x - funK x := funL_eq x
  simp only [Function.comp, opPlusI, cst]
  rw [show funL x + x = funA (funV x) + funV x by omega, funL_diag le_rfl, Nat.sub_self]

lemma zero_in_L (a : ℕ) : Clos (basisA funL a) (cst 0) := by
  rw [← zero_expr_L]; clos_solve

lemma Xm_L {j : ℕ} (hj : 2 ≤ j) : funL (2 * j * j) = j - 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := two_funA (2 * i + 1)
  rw [show 2 * (i + 1) * (i + 1) = funA (2 * i + 1) + (i + 1) by nlinarith,
    funL_diag (by omega)]
  omega

lemma locL {a : ℕ} (ha : 2 ≤ a) : ExtA funL a (fun j => 2 * j) :=
  ⟨ha, zero_in_L a, funL_zero, fun _ hj => Xm_L hj⟩

/-- K ≡ L 1̄⁺ ((1̄⁺)⁺ L)⁺ as in Theorem 6.8, so the case of L reduces to that of K -/
lemma K_in_La {a : ℕ} (ha : 2 ≤ a) : Clos (basisA funL a) funK := by
  have := (locL ha).one_in
  rw [← K_expr_L]; clos_solve

theorem Ext_a_L {a : ℕ} (ha : 2 ≤ a) : Suitable (basisA funL a) := by
  have K := K_in_La ha
  simulate Ext_a_K ha

/-! ## Every starting value a ≥ 1 -/

theorem Ext_a_all {a : ℕ} (ha : 1 ≤ a) {X : UFun} (hX : X = funE ∨ X = funK ∨ X = funL) :
    Suitable (basisA X a) := by
  rcases Nat.eq_or_lt_of_le ha with rfl | h
  · rcases hX with rfl | rfl | rfl
    · exact Remark_6_9_I
    · exact Remark_6_9_II
    · exact Remark_6_9_III
  · rcases hX with rfl | rfl | rfl
    · exact Ext_a_E h
    · exact Ext_a_K h
    · exact Ext_a_L h

end UPRF
