/-
  The general recursive analogue of the shifted operator of `ExtVb`: for X ∈ {E, K, L},

    clos ⟨X, F⁺ᵇ, FG, F⁻¹⟩ = clos ⟨S, E, F + G, FG, F⁻¹⟩   iff   b ≥ 1,

  where F⁺ᵇ(x) = F(x) + x + b. So, assuming J. Robinson's theorem, these bases generate exactly
  the unary general recursive functions when b ≥ 1, and not when b = 0 (then every generated
  function fixes 0, `ExtGR`).

  In each case a successor S is generated first; then a predecessor P (P(x + 1) = x) gives
  F⁺ ≡ P^b F⁺ᵇ and the constant 1, so the closure contains the basis ⟨1, X, F⁺, FG, F⁻¹⟩ of
  `ExtGR`. With T ≡ I⁺ᵇ (T(x) = 2x + b):
  - E, b ≥ 2: E (E⁻¹ T)⁺ᵇ and E (E⁻¹ (E (E⁻¹ T)⁺ᵇ) T)⁺ᵇ are the shifts x + b - 1 and x + b - 2
    (in an order that depends on the parity of b); if V(x) = x + c then E (E V)⁻¹ subtracts c,
    and S ≡ E (E U₂)⁻¹ U₁.
  - E, b = 1: P ≡ E (E⁻¹ T)⁺¹ is a predecessor and S ≡ E P⁻¹ (E⁻¹ P T)⁺¹.
  - K, b ≥ 2: U ≡ K (Z T)⁺ᵇ is x + b - 1 (Z = K⁻¹), the constant 2b - 4 is
    K (Z K (K U)⁻¹)⁺ᵇ U U U, and S ≡ K (K V)⁻¹ U U U with V ≡ (2b - 4)⁺ᵇ.
  - K, b = 1: P ≡ K (Z⁺¹)⁺¹ is a predecessor and S ≡ K P⁻¹ (Z T)⁺¹.
  - L: L⁻¹ = A, L ((…(A⁺ᵇ)…)⁺ᵇ) (2b - 2 times) is x + b - 1, L A⁺ᵇ subtracts b - 2, and S is
    their composition.
-/
import UPRF.ExtGR

namespace UPRF

noncomputable section

/-! ## The bases ⟨X, F⁺ᵇ, FG, F⁻¹⟩ -/

@[clos_defs] def basisGRb (X : UFun) (b : ℕ) : Basis := ⟨{X}, {opPlusIb b, opInv}, {(· ∘ ·)}⟩

abbrev CbE (b : ℕ) (F : UFun) : Prop := Clos (basisGRb funE b) F
abbrev CbK (b : ℕ) (F : UFun) : Prop := Clos (basisGRb funK b) F
abbrev CbL (b : ℕ) (F : UFun) : Prop := Clos (basisGRb funL b) F

/-- for b = 0 this is the basis ⟨X, F⁺, FG, F⁻¹⟩ of `ExtGR` -/
lemma basisGRb_zero (X : UFun) : basisGRb X 0 = basisGR0 X := rfl

/-! ## General facts -/

lemma clos_iter_unop {B : Basis} {u : UFun → UFun} (hu : u ∈ B.unops) {F : UFun}
    (hF : Clos B F) (n : ℕ) : Clos B (u^[n] F) := by
  induction n with
  | zero => exact hF
  | succ n ih => rw [Function.iterate_succ_apply']; exact Clos.unop hu ih

lemma T_val (b x : ℕ) : opPlusIb b funI x = 2 * x + b := by
  simp only [opPlusIb, funI]; ring

/-- a predecessor recovers F⁺: F⁺ = P^b F⁺ᵇ -/
lemma plusI_from_pred {P : UFun} (hP : ∀ y, P (y + 1) = y) (b : ℕ) (F : UFun) :
    P^[b] ∘ opPlusIb b F = opPlusI F := by
  funext x
  simp only [Function.comp_apply, opPlusIb, opPlusI]
  exact pred_pow hP b (F x + x)

lemma plusI_in_b {X : UFun} {b : ℕ} {P : UFun} (hPin : Clos (basisGRb X b) P)
    (hP : ∀ y, P (y + 1) = y) {F : UFun} (hF : Clos (basisGRb X b) F) :
    Clos (basisGRb X b) (opPlusI F) := by
  rw [← plusI_from_pred hP b F]
  exact clos_powcomp (by clos_mem) hPin (by cs) b

/-- with 1 and a predecessor, the closure contains the basis ⟨1, X, F⁺, FG, F⁻¹⟩ -/
lemma GR_sub_GRb {X : UFun} {b : ℕ} (one : Clos (basisGRb X b) (cst 1)) {P : UFun}
    (hPin : Clos (basisGRb X b) P) (hP : ∀ y, P (y + 1) = y) :
    ∀ F, Clos (basisGR X) F → Clos (basisGRb X b) F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> cs)
    (fun u hu F hF => by
      basis_cases hu
      · exact plusI_in_b hPin hP hF
      · cs)
    (fun c hc F G hF hG => by basis_cases hc; cs)

/-- conversely, F⁺ᵇ = F⁺ + b, so the closure lies in Robinson's -/
lemma cst_in_GE (n : ℕ) : CGE (cst n) := by
  induction n with
  | zero => exact zero_in_GE
  | succ n ih => have := S_in_GE; show CGE (funS ∘ cst n); cs

lemma opPlusIb_eq (b : ℕ) (F : UFun) : opPlusIb b F = opPlus (opPlusI F) (cst b) := rfl

lemma GRb_sub_GE {X : UFun} (hX : CGE X) (b : ℕ) : ∀ F, Clos (basisGRb X b) F → CGE F :=
  clos_subset
    (fun F hF => by basis_cases hF; exact hX)
    (fun u hu F hF => by
      basis_cases hu
      · rw [opPlusIb_eq]; exact plus_in_GE (by cs) (cst_in_GE b)
      · cs)
    (fun c hc F G hF hG => by basis_cases hc; cs)

/-! ## The basis with E -/

lemma Einv_even (m : ℕ) : opInv funE (2 * m) = m * m + 2 * m := Einv_D m

lemma Einv_odd (m : ℕ) : opInv funE (2 * m + 1) = (m + 1) * (m + 1) + (2 * m + 1) := by
  rw [Einv_val]; congr 2 <;> omega

lemma E_shift_even {b x m : ℕ} (hb : 1 ≤ b) (h : x + b ≤ 2 * m + 3) :
    funE (opInv funE (2 * m) + x + b) = x + b - 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Einv_even, show m * m + 2 * m + x + (c + 1) = (m + 1) * (m + 1) + (x + c) by ring,
    funE_sq_add (by omega)]; omega

lemma E_shift_odd {b x m : ℕ} (hb : 2 ≤ b) (h : x + b ≤ 2 * m + 6) :
    funE (opInv funE (2 * m + 1) + x + b) = x + b - 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  rw [Einv_odd, show (m + 1) * (m + 1) + (2 * m + 1) + x + (c + 2)
      = (m + 2) * (m + 2) + (x + c) by ring, funE_sq_add (by omega)]; omega

/-- subtraction by inversion with E: an instance of `sub_inv_val` with base(t) = t² and
  bound(t) = 2t -/
lemma E_dec (y : ℕ) : ∃ t, y = t * t + funE y ∧ funE y ≤ 2 * t :=
  ⟨funRt y, by have := funE_add y; omega, funE_bound y⟩

lemma E_diag (t k : ℕ) (h : k ≤ 2 * t) : funE (t * t + k) = k := funE_sq_add h

lemma E_big (c z : ℕ) : ∃ t, z ≤ 2 * t ∧ c ≤ t * t := ⟨z + c, by omega, by nlinarith⟩

lemma surj_E_shift {V : UFun} {c : ℕ} (hV : ∀ y, V y = y + c) : Function.Surjective (funE ∘ V) :=
  sub_inv_surj (base := fun t => t * t) (bound := fun t => 2 * t) E_diag (E_big c) hV

lemma E_sub_inv {V : UFun} {c x : ℕ} (hV : ∀ y, V y = y + c) (hc : c ≤ x) :
    funE (opInv (funE ∘ V) x) = x - c :=
  sub_inv_val (base := fun t => t * t) (bound := fun t => 2 * t) E_dec E_diag (E_big c) hV hc

/-! ### The successor, b ≥ 2 -/

/-- W₁ ≡ E (E⁻¹ T)⁺ᵇ and W₂ ≡ E (E⁻¹ W₁ T)⁺ᵇ, with T = I⁺ᵇ: the shifts x + b - 1 and x + b - 2,
  in an order that depends on the parity of b -/
def expW1 (b : ℕ) : UFun := funE ∘ opPlusIb b (opInv funE ∘ opPlusIb b funI)
def expW2 (b : ℕ) : UFun := funE ∘ opPlusIb b (opInv funE ∘ expW1 b ∘ opPlusIb b funI)

lemma I_in_bE (b : ℕ) : CbE b funI := by rw [← I_expr_inv]; cs
lemma expW1_in (b : ℕ) : CbE b (expW1 b) := by unfold expW1; have := I_in_bE b; cs
lemma expW2_in (b : ℕ) : CbE b (expW2 b) := by
  unfold expW2; have := I_in_bE b; have := expW1_in b; cs

lemma expW1_val {b : ℕ} (hb : 2 ≤ b) (x : ℕ) :
    expW1 b x = x + (if b % 2 = 0 then b - 1 else b - 2) := by
  have e : expW1 b x = funE (opInv funE (2 * x + b) + x + b) := by
    simp only [expW1, Function.comp_apply, opPlusIb, funI, ← two_mul]
  split_ifs with h
  · obtain ⟨c, hc⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
    rw [e, show 2 * x + b = 2 * (x + c) by omega, E_shift_even (by omega) (by omega)]; omega
  · obtain ⟨c, hc⟩ : ∃ c, b = 2 * c + 1 := ⟨b / 2, by omega⟩
    rw [e, show 2 * x + b = 2 * (x + c) + 1 by omega, E_shift_odd hb (by omega)]; omega

lemma expW2_val {b : ℕ} (hb : 2 ≤ b) (x : ℕ) :
    expW2 b x = x + (if b % 2 = 0 then b - 2 else b - 1) := by
  have e : expW2 b x = funE (opInv funE (expW1 b (2 * x + b)) + x + b) := by
    simp only [expW2, Function.comp_apply, opPlusIb, funI, ← two_mul]
  rw [e, expW1_val hb]
  split_ifs with h
  · rw [show 2 * x + b + (b - 1) = 2 * (x + b - 1) + 1 by omega, E_shift_odd hb (by omega)]
    omega
  · rw [show 2 * x + b + (b - 2) = 2 * (x + b - 1) by omega, E_shift_even (by omega) (by omega)]
    omega

/-- U₁(x) = x + b - 1 and U₂(x) = x + b - 2 -/
def expU1 (b : ℕ) : UFun := if b % 2 = 0 then expW1 b else expW2 b
def expU2 (b : ℕ) : UFun := if b % 2 = 0 then expW2 b else expW1 b

lemma expU1_val {b : ℕ} (hb : 2 ≤ b) (x : ℕ) : expU1 b x = x + (b - 1) := by
  unfold expU1; split_ifs with h <;> simp [expW1_val hb, expW2_val hb, h]
lemma expU2_val {b : ℕ} (hb : 2 ≤ b) (x : ℕ) : expU2 b x = x + (b - 2) := by
  unfold expU2; split_ifs with h <;> simp [expW1_val hb, expW2_val hb, h]

lemma expU1_in (b : ℕ) : CbE b (expU1 b) := by
  unfold expU1; split_ifs; exacts [expW1_in b, expW2_in b]
lemma expU2_in (b : ℕ) : CbE b (expU2 b) := by
  unfold expU2; split_ifs; exacts [expW2_in b, expW1_in b]

def expSE2 (b : ℕ) : UFun := funE ∘ opInv (funE ∘ expU2 b) ∘ expU1 b

lemma expSE2_val {b : ℕ} (hb : 2 ≤ b) : expSE2 b = funS := by
  funext x
  simp only [expSE2, Function.comp_apply, expU1_val hb]
  rw [E_sub_inv (expU2_val hb) (by omega)]; simp only [funS]; omega

lemma expSE2_in (b : ℕ) : CbE b (expSE2 b) := by
  unfold expSE2; have := expU1_in b; have := expU2_in b; cs

/-! ### The successor, b = 1 -/

def expPE1 : UFun := funE ∘ opPlusIb 1 (opInv funE ∘ opPlusIb 1 funI)

lemma expPE1_val (x : ℕ) : expPE1 x = funE (opInv funE (2 * x + 1) + x + 1) := by
  simp only [expPE1, Function.comp_apply, opPlusIb, funI, ← two_mul]

lemma expPE1_succ (y : ℕ) : expPE1 (y + 1) = y := by
  rw [expPE1_val, Einv_odd, show (y + 1 + 1) * (y + 1 + 1) + (2 * (y + 1) + 1) + (y + 1) + 1
      = (y + 3) * (y + 3) + y by ring, funE_sq_add (by omega)]

lemma expPE1_zero : expPE1 0 = 2 := by
  rw [expPE1_val, Einv_odd]; exact funE_small.2.2.2.1

lemma surj_expPE1 : Function.Surjective expPE1 := fun y => ⟨y + 1, expPE1_succ y⟩

lemma expPE1_inv {v : ℕ} (hv : v ≠ 2) : opInv expPE1 v = v + 1 := by
  have e := opInv_right surj_expPE1 v
  rcases h : opInv expPE1 v with _ | y
  · rw [h, expPE1_zero] at e; omega
  · rw [h, expPE1_succ] at e; omega

def expSE1 : UFun := funE ∘ opInv expPE1 ∘ opPlusIb 1 (opInv funE ∘ expPE1 ∘ opPlusIb 1 funI)

lemma expSE1_val : expSE1 = funS := by
  funext x
  have d : expPE1 (2 * x + 1) = 2 * x := expPE1_succ _
  have v : opPlusIb 1 (opInv funE ∘ expPE1 ∘ opPlusIb 1 funI) x = x * x + 3 * x + 1 := by
    simp only [opPlusIb, Function.comp_apply, funI, ← two_mul, d, Einv_even]; ring
  have v2 : x * x + 3 * x + 1 ≠ 2 := by
    rcases x with _ | x
    · omega
    · nlinarith
  simp only [expSE1, Function.comp_apply, v, expPE1_inv v2, funS]
  rw [show x * x + 3 * x + 1 + 1 = (x + 1) * (x + 1) + (x + 1) by ring, funE_sq_add (by omega)]

lemma expSE1_in : CbE 1 expSE1 := by
  have := I_in_bE 1
  have : CbE 1 expPE1 := by unfold expPE1; cs
  unfold expSE1; cs

/-! ### The basis with E generates Robinson's closure -/

lemma S_in_bE {b : ℕ} (hb : 1 ≤ b) : CbE b funS := by
  rcases Nat.lt_or_ge b 2 with h | h
  · obtain rfl : b = 1 := by omega
    exact expSE1_val ▸ expSE1_in
  · exact expSE2_val h ▸ expSE2_in b

/-- the predecessor E (E S)⁻¹ -/
lemma predE_succ (y : ℕ) : (funE ∘ opInv (funE ∘ funS)) (y + 1) = y := by
  simp only [Function.comp_apply]
  rw [E_sub_inv (V := funS) (c := 1) (fun _ => rfl) (by omega)]; omega

lemma zeroE_b : funE ∘ funS ∘ opInv funE ∘ opPlusI funI = cst 0 := by
  funext x
  have o : opPlusI funI x = 2 * x := by simp only [opPlusI, funI]; ring
  simp only [Function.comp_apply, o, Einv_even, funS, cst]
  rw [show x * x + 2 * x + 1 = (x + 1) * (x + 1) + 0 by ring, funE_sq_add (by omega)]

lemma GE_sub_bE {b : ℕ} (hb : 1 ≤ b) : ∀ F, CGE F → CbE b F := by
  have S := S_in_bE hb
  have P : CbE b (funE ∘ opInv (funE ∘ funS)) := by cs
  have D : CbE b (opPlusI funI) := plusI_in_b P predE_succ (I_in_bE b)
  have z : CbE b (cst 0) := by rw [← zeroE_b]; cs
  have one : CbE b (cst 1) := by rw [← one_expr]; cs
  exact GR_sub_GRb one P predE_succ

theorem GRb_E_eq_JR {b : ℕ} (hb : 1 ≤ b) (F : UFun) : CbE b F ↔ CJR F :=
  ⟨fun h => GE_sub_JR F (GRb_sub_GE (by cs) b F h), fun h => GE_sub_bE hb F (JR_sub_GE F h)⟩

/-! ## The basis with K -/

lemma Z_in_bK (b : ℕ) : CbK b funZ := by rw [← Kinv_eq_Z]; cs

lemma KZ_I : funK ∘ funZ = funI := funext KZ

lemma I_in_bK (b : ℕ) : CbK b funI := by rw [← KZ_I]; have := Z_in_bK b; cs

lemma le_funA (n : ℕ) : n ≤ funA n := by have := two_funA n; nlinarith

/-- subtraction by inversion with K: an instance of `sub_inv_val` with base = A and
  bound(t) = t -/
lemma K_dec (y : ℕ) : ∃ t, y = funA t + funK y ∧ funK y ≤ t :=
  ⟨funV y, (decomp y).1, (decomp y).2⟩

lemma K_big (c z : ℕ) : ∃ t, z ≤ t ∧ c ≤ funA t :=
  ⟨z + c, by omega, by have := le_funA (z + c); omega⟩

lemma surj_K_shift {V : UFun} {c : ℕ} (hV : ∀ y, V y = y + c) : Function.Surjective (funK ∘ V) :=
  sub_inv_surj (base := funA) (bound := id) (fun _ _ h => funK_diag h) (K_big c) hV

lemma K_sub_inv {V : UFun} {c x : ℕ} (hV : ∀ y, V y = y + c) (hc : c ≤ x) :
    funK (opInv (funK ∘ V) x) = x - c :=
  sub_inv_val (base := funA) (bound := id) K_dec (fun _ _ h => funK_diag h) (K_big c) hV hc

/-- U ≡ K (Z T)⁺ᵇ, U(x) = x + b - 1 -/
def expUK (b : ℕ) : UFun := funK ∘ opPlusIb b (funZ ∘ opPlusIb b funI)

lemma expUK_val {b : ℕ} (hb : 1 ≤ b) (x : ℕ) : expUK b x = x + (b - 1) := by
  have e : expUK b x = funK (funZ (2 * x + b) + x + b) := by
    simp only [expUK, Function.comp_apply, opPlusIb, funI, ← two_mul]
  have ar : funZ (2 * x + b) + x + b = funA (2 * x + b + 1) + (x + (b - 1)) := by
    simp only [funZ, funA_succ]; omega
  rw [e, ar, funK_diag (by omega)]

lemma expUK_in (b : ℕ) : CbK b (expUK b) := by
  unfold expUK; have := Z_in_bK b; have := I_in_bK b; cs

/-! ### The successor, b ≥ 2 -/

def expP1K (b : ℕ) : UFun := funK ∘ opInv (funK ∘ expUK b)
def expCK (b : ℕ) : UFun := funK ∘ opPlusIb b (funZ ∘ expP1K b) ∘ expUK b ∘ expUK b ∘ expUK b
def expSK2 (b : ℕ) : UFun := funK ∘ opInv (funK ∘ opPlusIb b (expCK b)) ∘ expUK b ∘ expUK b ∘ expUK b

lemma expP1K_val {b x : ℕ} (hb : 1 ≤ b) (hx : b - 1 ≤ x) : expP1K b x = x - (b - 1) :=
  K_sub_inv (expUK_val hb) hx

/-- the constant 2b - 4 -/
lemma expCK_val {b : ℕ} (hb : 2 ≤ b) (x : ℕ) : expCK b x = 2 * b - 4 := by
  have u3 : expUK b (expUK b (expUK b x)) = x + 3 * (b - 1) := by
    simp only [expUK_val (show 1 ≤ b by omega)]; omega
  set g := x + 2 * (b - 1)
  have p : expP1K b (x + 3 * (b - 1)) = g := by rw [expP1K_val (by omega) (by omega)]; omega
  have ar : funZ g + (x + 3 * (b - 1)) + b = funA (g + 1 + 1) + (2 * b - 4) := by
    have := funA_succ g; have := funA_succ (g + 1); simp only [funZ]; omega
  simp only [expCK, Function.comp_apply, u3, opPlusIb, p]
  rw [ar, funK_diag (by omega)]

lemma expSK2_val {b : ℕ} (hb : 2 ≤ b) : expSK2 b = funS := by
  funext x
  have V (y : ℕ) : opPlusIb b (expCK b) y = y + (3 * b - 4) := by
    simp only [opPlusIb, expCK_val hb]; omega
  have u3 : expUK b (expUK b (expUK b x)) = x + 3 * (b - 1) := by
    simp only [expUK_val (show 1 ≤ b by omega)]; omega
  simp only [expSK2, Function.comp_apply, u3]
  rw [K_sub_inv V (by omega)]; simp only [funS]; omega

lemma expSK2_in (b : ℕ) : CbK b (expSK2 b) := by
  have := expUK_in b; have := Z_in_bK b
  have : CbK b (expP1K b) := by unfold expP1K; cs
  have : CbK b (expCK b) := by unfold expCK; cs
  unfold expSK2; cs

/-! ### The successor, b = 1 -/

def expPK1 : UFun := funK ∘ opPlusIb 1 (opPlusIb 1 funZ)

lemma expPK1_succ (y : ℕ) : expPK1 (y + 1) = y := by
  have ar : funZ (y + 1) + (y + 1) + 1 + (y + 1) + 1 = funA (y + 1 + 1 + 1) + y := by
    have := funA_succ (y + 1); have := funA_succ (y + 1 + 1); simp only [funZ]; omega
  simp only [expPK1, Function.comp_apply, opPlusIb]
  rw [ar, funK_diag (by omega)]

lemma expPK1_zero : expPK1 0 = 1 := by
  simp only [expPK1, Function.comp_apply, opPlusIb, funZ, funA_zero]
  simpa [funA_one] using funK_diag (k := 1) (t := 1) le_rfl

lemma surj_expPK1 : Function.Surjective expPK1 := fun y => ⟨y + 1, expPK1_succ y⟩

lemma expPK1_inv {v : ℕ} (hv : v ≠ 1) : opInv expPK1 v = v + 1 := by
  have e := opInv_right surj_expPK1 v
  rcases h : opInv expPK1 v with _ | y
  · rw [h, expPK1_zero] at e; omega
  · rw [h, expPK1_succ] at e; omega

def expSK1 : UFun := funK ∘ opInv expPK1 ∘ opPlusIb 1 (funZ ∘ opPlusIb 1 funI)

lemma expSK1_val : expSK1 = funS := by
  funext x
  have v : opPlusIb 1 (funZ ∘ opPlusIb 1 funI) x = funA (2 * x + 1 + 1) + x := by
    simp only [opPlusIb, Function.comp_apply, funI, ← two_mul, funZ, funA_succ]; omega
  have v1 : funA (2 * x + 1 + 1) + x ≠ 1 := by
    have := funA_mono (show 2 ≤ 2 * x + 1 + 1 by omega)
    have : funA 2 = 3 := rfl
    omega
  simp only [expSK1, Function.comp_apply, v, expPK1_inv v1, funS]
  rw [show funA (2 * x + 1 + 1) + x + 1 = funA (2 * x + 1 + 1) + (x + 1) by ring,
    funK_diag (by omega)]

lemma expSK1_in : CbK 1 expSK1 := by
  have := Z_in_bK 1; have := I_in_bK 1
  have : CbK 1 expPK1 := by unfold expPK1; cs
  unfold expSK1; cs

/-! ### The basis with K generates Robinson's closure -/

lemma S_in_bK {b : ℕ} (hb : 1 ≤ b) : CbK b funS := by
  rcases Nat.lt_or_ge b 2 with h | h
  · obtain rfl : b = 1 := by omega
    exact expSK1_val ▸ expSK1_in
  · exact expSK2_val h ▸ expSK2_in b

lemma A0_K : funK ∘ funA = cst 0 := by
  funext x; simpa [cst] using funK_diag (k := 0) (t := x) (Nat.zero_le _)

lemma GK_sub_bK {b : ℕ} (hb : 1 ≤ b) : ∀ F, CGK F → CbK b F := by
  have S := S_in_bK hb
  have P : CbK b funPred := by rw [← P_expr_K]; cs
  have pI := fun {F : UFun} (h : CbK b F) => plusI_in_b P P_succ h
  have Z := Z_in_bK b
  have A : CbK b funA := by
    rw [← A_expr_K]; unfold exprAK
    have h1 : CbK b (opPlusI funZ) := pI Z
    have h2 : CbK b (opPlusI (funZ ∘ opPlusI funZ ∘ funK)) := pI (by cs)
    have h3 : CbK b (opPlusI (opPlusI (funZ ∘ opPlusI funZ ∘ funK) ∘ funZ ∘ funK)) := pI (by cs)
    cs
  have z : CbK b (cst 0) := by rw [← A0_K]; cs
  have one : CbK b (cst 1) := by rw [← one_expr]; cs
  exact GR_sub_GRb one P P_succ

theorem GRb_K_eq_JR {b : ℕ} (hb : 1 ≤ b) (F : UFun) : CbK b F ↔ CJR F :=
  ⟨fun h => GE_sub_JR F (GRb_sub_GE K_in_GE b F h),
   fun h => GK_sub_bK hb F (GE_sub_GK F (JR_sub_GE F h))⟩

/-! ## The basis with L -/

lemma surj_funL : Function.Surjective funL := fun x =>
  ⟨funA x, by simpa using funL_diag (k := 0) (t := x) (Nat.zero_le _)⟩

/-- L⁻¹ = A -/
lemma Linv_eq_A : opInv funL = funA := by
  funext x
  inv_eq surj_funL
  · simpa using funL_diag (k := 0) (t := x) (Nat.zero_le _)
  · intro y hy
    obtain ⟨d1, d2⟩ := decomp y
    have hl := funL_eq y
    rw [hy] at hl
    have := funA_mono (show x ≤ funV y by omega)
    omega

lemma A_in_bL (b : ℕ) : CbL b funA := by rw [← Linv_eq_A]; cs

lemma iter_A (b n x : ℕ) : ((opPlusIb b)^[n] funA) x = funA x + n * (x + b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', opPlusIb, ih]; ring

lemma funA_add (x n : ℕ) : funA (x + n) = funA x + n * x + funA n := by
  have h1 := two_funA (x + n); have h2 := two_funA x; have h3 := two_funA n; nlinarith

/-- U ≡ L (…(A⁺ᵇ)…)⁺ᵇ (2b - 2 times), U(x) = x + b - 1 -/
def expUL (b : ℕ) : UFun := funL ∘ (opPlusIb b)^[2 * b - 2] funA

lemma expUL_val {b : ℕ} (hb : 1 ≤ b) (x : ℕ) : expUL b x = x + (b - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have n : 2 * (c + 1) - 2 = 2 * c := by omega
  have sfc : funA (2 * c) = 2 * c * c + c := by have := two_funA (2 * c); nlinarith
  have ar : funA x + 2 * c * (x + (c + 1)) = funA (x + 2 * c) + c := by
    rw [funA_add, sfc]; ring
  simp only [expUL, Function.comp_apply, iter_A, n, ar]
  rw [funL_diag (by omega)]; omega

/-- L A⁺ᵇ subtracts b - 2: A(y) + y + b = A(y + 1) + (b - 1) -/
lemma sigmaL_val {b y : ℕ} (hb : 1 ≤ b) (h : b - 1 ≤ y + 1) :
    (funL ∘ opPlusIb b funA) y = y + 1 - (b - 1) := by
  simp only [Function.comp_apply, opPlusIb]
  rw [show funA y + y + b = funA (y + 1) + (b - 1) by rw [funA_succ]; omega, funL_diag h]

def expSL (b : ℕ) : UFun := funL ∘ opPlusIb b funA ∘ expUL b

lemma expSL_val {b : ℕ} (hb : 1 ≤ b) : expSL b = funS := by
  funext x
  have := sigmaL_val (y := x + (b - 1)) hb (by omega)
  simp only [Function.comp_apply] at this
  simp only [expSL, Function.comp_apply, expUL_val hb, this, funS]; omega

lemma expSL_in (b : ℕ) : CbL b (expSL b) := by
  have A := A_in_bL b
  have it : CbL b ((opPlusIb b)^[2 * b - 2] funA) := clos_iter_unop (by clos_mem) A _
  unfold expSL expUL; cs

/-- the predecessor L S A and the constant 0 ≡ L A⁺ -/
lemma predL_succ (y : ℕ) : (funL ∘ funS ∘ funA) (y + 1) = y := by
  simp only [Function.comp_apply, funS]
  rw [funL_diag (show 1 ≤ y + 1 by omega)]; omega

lemma zeroL : funL ∘ opPlusI funA = cst 0 := by
  funext x; simp only [Function.comp_apply, opPlusI, cst]; rw [funL_diag le_rfl]; omega

lemma GL_sub_bL {b : ℕ} (hb : 1 ≤ b) : ∀ F, CGL F → CbL b F := by
  have S : CbL b funS := expSL_val hb ▸ expSL_in b
  have A := A_in_bL b
  have P : CbL b (funL ∘ funS ∘ funA) := by cs
  have pA : CbL b (opPlusI funA) := plusI_in_b P predL_succ A
  have z : CbL b (cst 0) := by rw [← zeroL]; cs
  have one : CbL b (cst 1) := by rw [← one_expr]; cs
  exact GR_sub_GRb one P predL_succ

theorem GRb_L_eq_JR {b : ℕ} (hb : 1 ≤ b) (F : UFun) : CbL b F ↔ CJR F :=
  ⟨fun h => GE_sub_JR F (GRb_sub_GE L_in_GE b F h),
   fun h => GL_sub_bL hb F (GK_sub_GL F (GE_sub_GK F (JR_sub_GE F h)))⟩

/-! ## Assuming Robinson's theorem -/

theorem Ext_GRb_iff {GR : UFun → Prop} (Robinson_1950_sec4_thm3 : ∀ F, CJR F ↔ GR F) (b : ℕ) :
    ((∀ F, CbE b F ↔ GR F) ↔ 1 ≤ b) ∧ ((∀ F, CbK b F ↔ GR F) ↔ 1 ≤ b) ∧
      ((∀ F, CbL b F ↔ GR F) ↔ 1 ≤ b) := by
  obtain ⟨nE, nK, nL⟩ := Ext_GR0 Robinson_1950_sec4_thm3
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.le_zero, one_ne_zero, iff_false]
    exact ⟨nE, nK, nL⟩
  · exact ⟨iff_of_true (fun F => (GRb_E_eq_JR hb F).trans (Robinson_1950_sec4_thm3 F)) hb,
      iff_of_true (fun F => (GRb_K_eq_JR hb F).trans (Robinson_1950_sec4_thm3 F)) hb,
      iff_of_true (fun F => (GRb_L_eq_JR hb F).trans (Robinson_1950_sec4_thm3 F)) hb⟩

end

end UPRF
