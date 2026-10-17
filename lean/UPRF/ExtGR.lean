/-
  The general recursive analogue of Section 6 (README §2.3).

  J. Robinson (General recursive functions, Proc. AMS 1 (1950), §4, Thm. 3) proved that the
  unary general recursive functions are the closure of ⟨S, E, F + G, FG, F⁻¹⟩, where
  F⁻¹(x) = μy [F(y) = x] (F onto). Here F + G is replaced by F⁺(x) = F(x) + x: for
  X ∈ {E, K, L},
    clos ⟨1, X, F⁺, FG, F⁻¹⟩ = clos ⟨S, E, F + G, FG, F⁻¹⟩,
  so, assuming Robinson's theorem, these bases generate the unary general recursive functions.
  Without 1 every generated function fixes 0. The constant 1 can be replaced by S (Remark).

  The functions E, S, D, M₃, Sq, Hf, Rt used by Lemmas 6.2–6.6 are generated with inversion
  in place of iteration; Lemma 6.6 then gives F + G.
  With E:  E⁻¹(x) = ⌈x/2⌉² + x,  F⁻ ≡ E (S S S M₃ F E)⁺ S (E⁻¹ D F⁺)⁺,  Sq ≡ ((E⁻¹ D)⁻)⁻,
           I - F ≡ E (S (F⁺)⁺ E)⁺ (Sq F⁺)⁺,  W ≡ E (S S D E E)⁺ E⁻¹ (W(y) = 2E(y) + [y even]),
           Hf ≡ E W⁻¹,  Rt ≡ Hf Hf S S E (I - 1) (I - E) S M₄.
  With K:  Z ≡ K⁻¹,  A ≡ Z - I,  F⁻ ≡ K (S S S M₃ F K)⁺ (A F⁺)⁺,  Sq ≡ (((D Z)⁻)⁻)⁻,
           P ≡ K (K S)⁻¹,  U ≡ I - A K P (I - K) (U = V + K),  Hf ≡ K U⁻¹,
           B ≡ I - (I - Sq (I - Hf) U) (I - K) (B = K + ⌈V/2⌉²),  E ≡ K B⁻¹.
  With L:  K ≡ L 1⁺ ((1⁺)⁺ L)⁺ (as in Theorem 6.8).
-/
import UPRF.ExtVb

namespace UPRF

noncomputable section

/-! ## Inversion -/

open Classical in
/-- F⁻¹(x) = μy [F(y) = x]. Robinson applies inversion only to onto functions; as an operator
  on all functions, `opInv` leaves a function that is not onto unchanged, so a closure under
  `opInv` is exactly a closure under the restricted inversion. -/
noncomputable def opInv (F : UFun) : UFun :=
  if h : Function.Surjective F then fun x => Nat.find (h x) else F

lemma opInv_right {F : UFun} (h : Function.Surjective F) (x : ℕ) : F (opInv F x) = x := by
  unfold opInv; simp only [h, ↓reduceDIte]; exact Nat.find_spec (h x)

lemma opInv_least {F : UFun} (h : Function.Surjective F) {x y : ℕ} (hy : F y = x) :
    opInv F x ≤ y := by
  unfold opInv; simp only [h, ↓reduceDIte]; exact Nat.find_min' (h x) hy

lemma opInv_not {F : UFun} (h : ¬ Function.Surjective F) : opInv F = F := by
  unfold opInv; simp only [h, ↓reduceDIte]

/-- F⁻¹(x) = v as soon as F is onto, v is a preimage of x and every preimage is at least v -/
lemma opInv_eqI {F : UFun} {x v : ℕ} (h : Function.Surjective F) (hv : F v = x)
    (hmin : ∀ y, F y = x → v ≤ y) : opInv F x = v :=
  le_antisymm (opInv_least h hv) (hmin _ (opInv_right h x))

/-- `inv_eq h` proves `opInv F x = v` from `h : Function.Surjective F` with `opInv_eqI`; the
  goals `F v = x` and `∀ y, F y = x → v ≤ y` are tried with `rfl`, `omega` and `simp_all`, and
  left to the user otherwise.  For `opInv F = G`, use `funext x` first. -/
macro "inv_eq " h:term : tactic =>
  `(tactic| (refine opInv_eqI $h ?_ ?_ <;>
      try (first | rfl | omega | (simp_all; done))))

/-- `eval` computes the value of an expression at a point: the operators and the basic
  functions are unfolded (with the extra lemmas given in brackets), then the arithmetic goal is
  tried with `omega`, `ring1` and `nlinarith`, and left to the user otherwise. -/
syntax "eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eval) => `(tactic| eval [])
  | `(tactic| eval [$ts,*]) => `(tactic| ((simp only [Function.comp_apply, opPlusI, opPlus,
      opPlusIb, funI, cst, funS, funD, funSq, funM3, $ts,*]) <;>
      try (first | omega | ring1 | nlinarith)))

/-- subtraction by inversion.  Let every y decompose as y = base(t) + X(y) with
  X(y) ≤ bound(t), where X(base(t) + k) = k for k ≤ bound(t) (for E: base(t) = t², bound(t) = 2t;
  for K: base = A, bound(t) = t).  If V(y) = y + c, then X (X V)⁻¹ subtracts c. -/
theorem sub_inv_surj {X V : UFun} {base bound : ℕ → ℕ} {c : ℕ}
    (diag : ∀ t k, k ≤ bound t → X (base t + k) = k)
    (big : ∀ z, ∃ t, z ≤ bound t ∧ c ≤ base t) (hV : ∀ y, V y = y + c) :
    Function.Surjective (X ∘ V) := fun z => by
  obtain ⟨t, h1, h2⟩ := big z
  exact ⟨base t + z - c, by
    simp only [Function.comp_apply, hV, Nat.sub_add_cancel (by omega : c ≤ base t + z)]
    exact diag t z h1⟩

theorem sub_inv_val {X V : UFun} {base bound : ℕ → ℕ} {c x : ℕ}
    (dec : ∀ y, ∃ t, y = base t + X y ∧ X y ≤ bound t)
    (diag : ∀ t k, k ≤ bound t → X (base t + k) = k)
    (big : ∀ z, ∃ t, z ≤ bound t ∧ c ≤ base t) (hV : ∀ y, V y = y + c) (hc : c ≤ x) :
    X (opInv (X ∘ V) x) = x - c := by
  have e := opInv_right (sub_inv_surj diag big hV) x
  simp only [Function.comp_apply, hV] at e
  obtain ⟨t, h1, h2⟩ := dec (opInv (X ∘ V) x + c)
  rw [e] at h1 h2
  have y : opInv (X ∘ V) x = base t + (x - c) := by omega
  rw [y, diag t _ (by omega)]

macro_rules | `(tactic| clos_rule) => `(tactic| with_reducible apply Clos.unop (u := opInv))

/-- a lighter `clos_solve` for the large expressions of Lemmas 6.2–6.6: decomposition by
  composition, F⁺, F⁻¹ and F⁺ᵇ, then hypotheses and initial functions -/
macro "cs" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | (apply Clos.init; clos_mem)
  | (with_reducible apply Clos.binop (b := fun f g : UFun => f ∘ g) (by clos_mem))
  | (with_reducible apply Clos.unop (u := opPlusI) (by clos_mem))
  | (with_reducible apply Clos.unop (u := opInv) (by clos_mem))
  | (with_reducible apply Clos.unop (u := opPlusIb _) (by clos_mem))))

/-! ## The bases -/

/-- J. Robinson's basis ⟨S, E, F + G, FG, F⁻¹⟩ -/
@[clos_defs] def basisJR : Basis := ⟨{funS, funE}, {opInv}, {opPlus, (· ∘ ·)}⟩
/-- ⟨1, X, F⁺, FG, F⁻¹⟩ -/
@[clos_defs] def basisGR (X : UFun) : Basis := ⟨{cst 1, X}, {opPlusI, opInv}, {(· ∘ ·)}⟩
/-- ⟨X, F⁺, FG, F⁻¹⟩ -/
@[clos_defs] def basisGR0 (X : UFun) : Basis := ⟨{X}, {opPlusI, opInv}, {(· ∘ ·)}⟩

abbrev CJR (F : UFun) : Prop := Clos basisJR F
abbrev CGE (F : UFun) : Prop := Clos (basisGR funE) F
abbrev CGK (F : UFun) : Prop := Clos (basisGR funK) F
abbrev CGL (F : UFun) : Prop := Clos (basisGR funL) F

/-! ## Arithmetic facts -/

lemma funE_bound (y : ℕ) : funE y ≤ 2 * funRt y := by
  have h1 := funRt_sq_le y; have h2 := funRt_lt y
  have : (funRt y + 1) * (funRt y + 1) = funRt y * funRt y + 2 * funRt y + 1 := by ring
  simp only [funE]; generalize funRt y * funRt y = q at *; omega

lemma two_le_sq_succ (r : ℕ) : 2 * r ≤ r * r + 1 := by
  rcases r with _ | r
  · omega
  · nlinarith

/-- 2E(y) ≤ y + 1 -/
lemma two_funE_le (y : ℕ) : 2 * funE y ≤ y + 1 := by
  have h1 := funE_bound y; have h2 := two_le_sq_succ (funRt y); have h3 := funE_add y
  generalize funRt y * funRt y = q at *; omega

/-- ⌊√(4x+1)⌋ / 2 = ⌊√x⌋ -/
lemma funRt_4x1 (x : ℕ) : funRt (4 * x + 1) / 2 = funRt x := by
  have a := funRt_sq_le x; have b := funRt_lt x
  have c := funRt_sq_le (4 * x + 1); have d := funRt_lt (4 * x + 1)
  have lo : 2 * funRt x ≤ funRt (4 * x + 1) := by
    by_contra h; push Not at h
    have : funRt (4 * x + 1) + 1 ≤ 2 * funRt x := h
    nlinarith
  have hi : funRt (4 * x + 1) < 2 * funRt x + 2 := by
    by_contra h; push Not at h
    nlinarith
  omega

/-! ## clos ⟨1, E, F⁺, FG, F⁻¹⟩ ⊆ clos ⟨S, E, F + G, FG, F⁻¹⟩ -/

lemma surj_funE : Function.Surjective funE := fun x => ⟨x * x + x, funE_sq_add (by omega)⟩

/-- E⁻¹(x) = ⌈x/2⌉² + x -/
lemma Einv_val (x : ℕ) : opInv funE x = ((x + 1) / 2) * ((x + 1) / 2) + x := by
  apply le_antisymm
  · exact opInv_least surj_funE (funE_sq_add (by omega))
  · have e := opInv_right surj_funE x
    have b := funE_bound (opInv funE x); have d := funE_add (opInv funE x)
    rw [e] at b d
    have : (x + 1) / 2 ≤ funRt (opInv funE x) := by omega
    have := Nat.mul_le_mul this this
    omega

lemma Einv_D (z : ℕ) : opInv funE (funD z) = z * z + 2 * z := by
  rw [Einv_val]; simp only [funD]
  have : (2 * z + 1) / 2 = z := by omega
  rw [this]

lemma I_expr_inv : funE ∘ opInv funE = funI := by
  funext x; exact opInv_right surj_funE x

lemma zero_expr_JR : funE ∘ funS ∘ opInv funE ∘ opPlus funI funI = cst 0 := by
  funext x
  have : opPlus funI funI x = funD x := by simp only [opPlus, funI, funD]; ring
  simp only [Function.comp_apply, this, Einv_D, funS, cst]
  have : x * x + 2 * x + 1 = (x + 1) * (x + 1) + 0 := by ring
  rw [this, funE_sq_add (by omega)]

lemma one_expr : funS ∘ cst 0 = cst 1 := rfl

lemma plusI_expr (F : UFun) : opPlus F funI = opPlusI F := rfl

lemma I_in_JR : CJR funI := by rw [← I_expr_inv]; clos_solve
lemma zero_in_JR : CJR (cst 0) := by rw [← zero_expr_JR]; have := I_in_JR; clos_solve
lemma one_in_JR : CJR (cst 1) := by rw [← one_expr]; have := zero_in_JR; clos_solve
lemma plusI_in_JR {F : UFun} (h : CJR F) : CJR (opPlusI F) := by
  rw [← plusI_expr]; have := I_in_JR; clos_solve

theorem GE_sub_JR : ∀ F, CGE F → CJR F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact one_in_JR | clos_solve)
    (fun u hu F hF => by basis_cases hu <;> first | exact plusI_in_JR hF | clos_solve)
    (fun b hb F G hF hG => by basis_cases hb; clos_solve)

/-! ## Generating Sq, Hf, Rt in clos ⟨1, E, F⁺, FG, F⁻¹⟩ -/

lemma I_expr : opPlusI (cst 0) = funI := by funext x; eval

lemma one_in_GE : CGE (cst 1) := by clos_solve
lemma S_in_GE : CGE funS := by rw [← S_expr]; clos_solve
lemma zero_in_GE : CGE (cst 0) := by rw [← zero_expr]; clos_solve
lemma I_in_GE : CGE funI := by rw [← I_expr]; have := zero_in_GE; clos_solve
lemma D_in_GE : CGE funD := by rw [← D_expr]; have := zero_in_GE; clos_solve
lemma M3_in_GE : CGE funM3 := by rw [← M3_expr]; have := D_in_GE; clos_solve
lemma Einv_in_GE : CGE (opInv funE) := by clos_solve

/-- F⁻ without Sq: F⁻ ≡ E (S S S M₃ F E)⁺ S (E⁻¹ D F⁺)⁺ -/
def exprMinusIE (F : UFun) : UFun :=
  funE ∘ opPlusI (funS ∘ funS ∘ funS ∘ funM3 ∘ F ∘ funE) ∘ funS ∘
    opPlusI (opInv funE ∘ funD ∘ opPlusI F)

lemma exprMinusIE_in {F : UFun} (h : CGE F) : CGE (exprMinusIE F) := by
  unfold exprMinusIE; have := M3_in_GE; have := D_in_GE; have := S_in_GE; clos_solve

lemma exprMinusIE_val {F : UFun} {x : ℕ} (h : x ≤ F x) : exprMinusIE F x = F x - x := by
  obtain ⟨d, hd⟩ : ∃ d, F x = x + d := ⟨F x - x, by omega⟩
  have v : funS (opPlusI (opInv funE ∘ funD ∘ opPlusI F) x)
      = (F x + x + 1) * (F x + x + 1) + x := by
    simp only [funS, opPlusI, Function.comp_apply, Einv_D]; ring
  have ev : funE ((F x + x + 1) * (F x + x + 1) + x) = x := funE_sq_add (by omega)
  have e : exprMinusIE F x = funE (opPlusI (funS ∘ funS ∘ funS ∘ funM3 ∘ F ∘ funE)
      (funS (opPlusI (opInv funE ∘ funD ∘ opPlusI F) x))) := rfl
  rw [e, v]
  simp only [opPlusI, Function.comp_apply, ev, funS, funM3]
  rw [hd]
  have : 3 * (x + d) + 1 + 1 + 1 + ((x + d + x + 1) * (x + d + x + 1) + x)
      = (2 * x + d + 2) * (2 * x + d + 2) + d := by ring
  rw [this, funE_sq_add (by omega)]; omega

lemma Sq_expr_GE : exprMinusIE (exprMinusIE (opInv funE ∘ funD)) = funSq := by
  funext x
  have a : (opInv funE ∘ funD) x = x * x + 2 * x := Einv_D x
  have b : exprMinusIE (opInv funE ∘ funD) x = x * x + x := by
    rw [exprMinusIE_val (by rw [a]; omega), a]; omega
  rw [exprMinusIE_val (by rw [b]; omega), b]; simp only [funSq]; omega

lemma Sq_in_GE : CGE funSq := by
  rw [← Sq_expr_GE]; have := D_in_GE
  exact exprMinusIE_in (exprMinusIE_in (by clos_solve))

/-- I - F ≡ E (S (F⁺)⁺ E)⁺ (Sq F⁺)⁺ (if F(x) ≤ x) -/
def exprIminusE (F : UFun) : UFun :=
  funE ∘ opPlusI (funS ∘ opPlusI (opPlusI F) ∘ funE) ∘ opPlusI (funSq ∘ opPlusI F)

lemma exprIminusE_in {F : UFun} (h : CGE F) : CGE (exprIminusE F) := by
  unfold exprIminusE; have := Sq_in_GE; have := S_in_GE; clos_solve

lemma exprIminusE_val {F : UFun} {x : ℕ} (h : F x ≤ x) : exprIminusE F x = x - F x := by
  have e : funE ((F x + x) * (F x + x) + x) = x := funE_sq_add (by omega)
  have : exprIminusE F x = funE ((x + F x) * (x + F x) + 3 * x + F x + 1) := by
    simp only [exprIminusE, Function.comp_apply, opPlusI, funSq, e, funS]; congr 1; ring
  rw [this, robinson_diff_E h]

/-- W ≡ E (S S D E E)⁺ E⁻¹, W(y) = 2E(y) + [y even] (Robinson's W, 1950, §3) -/
def exprW : UFun := funE ∘ opPlusI (funS ∘ funS ∘ funD ∘ funE ∘ funE) ∘ opInv funE

lemma exprW_in : CGE exprW := by unfold exprW; have := S_in_GE; have := D_in_GE; clos_solve

lemma exprW_val (y : ℕ) : exprW y = 2 * funE y + (1 - y % 2) := by
  have inv := Einv_val y
  have ei : funE ((y + 1) / 2 * ((y + 1) / 2) + y) = y := funE_sq_add (by omega)
  have e2 := two_funE_le y
  have h : exprW y = funE (2 * funE y + 2 + ((y + 1) / 2 * ((y + 1) / 2) + y)) := by
    simp only [exprW, Function.comp_apply, opPlusI, inv, ei, funS, funD]
  rw [h]
  have key : 2 * funE y + 2 + ((y + 1) / 2 * ((y + 1) / 2) + y)
      = ((y + 1) / 2 + 1) * ((y + 1) / 2 + 1) + (2 * funE y + (1 - y % 2)) := by
    have : ((y + 1) / 2 + 1) * ((y + 1) / 2 + 1) = (y + 1) / 2 * ((y + 1) / 2) + 2 * ((y + 1) / 2) + 1 := by ring
    rw [this]; omega
  rw [key, funE_sq_add (by omega)]

lemma sq_add_mod2 (m k : ℕ) : (m * m + k) % 2 = (m + k) % 2 := by
  rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have : (t + t) * (t + t) + k = 2 * (2 * t * t) + k := by ring
    rw [this]; omega
  · have : (2 * t + 1) * (2 * t + 1) + k = 2 * (2 * t * t + 2 * t) + 1 + k := by ring
    rw [this]; omega

lemma surj_exprW : Function.Surjective exprW := by
  intro x
  refine ⟨(x / 2 + 1 + x % 2) * (x / 2 + 1 + x % 2) + x / 2, ?_⟩
  rw [exprW_val, funE_sq_add (by omega), sq_add_mod2]; omega

lemma Hf_expr_GE : funE ∘ opInv exprW = funHf := by
  funext x
  have h := opInv_right surj_exprW x
  rw [exprW_val] at h
  simp only [Function.comp_apply, funHf]; omega

lemma Hf_in_GE : CGE funHf := by rw [← Hf_expr_GE]; have := exprW_in; clos_solve

/-- Rt ≡ Hf Hf S S E (I - 1) (I - E) S M₄, with M₄(x) = 4x -/
def exprRtGE : UFun :=
  funHf ∘ funHf ∘ funS ∘ funS ∘ funE ∘ exprIminusE (cst 1) ∘ exprIminusE funE ∘ funS ∘
    opPlusI funM3

lemma exprRtGE_in : CGE exprRtGE := by
  unfold exprRtGE
  have := Hf_in_GE; have := S_in_GE; have := M3_in_GE
  have := exprIminusE_in (F := cst 1) (by clos_solve)
  have := exprIminusE_in (F := funE) (by clos_solve)
  cs

lemma Rt_expr_GE : exprRtGE = funRt := by
  funext x
  set n := funRt (4 * x + 1) with hn
  have z : funS (opPlusI funM3 x) = 4 * x + 1 := by simp only [funS, opPlusI, funM3]; ring
  have n1 : 1 ≤ n := by
    by_contra h; push Not at h
    have := funRt_lt (4 * x + 1); rw [← hn] at this; interval_cases n; omega
  have ie : exprIminusE funE (4 * x + 1) = n * n := by
    rw [exprIminusE_val (by simp only [funE]; omega)]
    have := funE_add (4 * x + 1); rw [← hn] at this; omega
  have i1 : exprIminusE (cst 1) (n * n) = (n - 1) * (n - 1) + 2 * (n - 1) := by
    rw [exprIminusE_val (by simp only [cst]; nlinarith)]
    simp only [cst]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
    rw [hm, Nat.add_sub_cancel, this]; omega
  have eE : funE ((n - 1) * (n - 1) + 2 * (n - 1)) = 2 * (n - 1) := funE_sq_add le_rfl
  have : exprRtGE x = funHf (funHf (funS (funS (funE (exprIminusE (cst 1)
      (exprIminusE funE (funS (opPlusI funM3 x)))))))) := rfl
  rw [this, z, ie, i1, eE, ← funRt_4x1 x, ← hn]
  simp only [funS, funHf]; omega

lemma Rt_in_GE : CGE funRt := by rw [← Rt_expr_GE]; exact exprRtGE_in

/-! ## Lemmas 6.2–6.6 in clos ⟨1, E, F⁺, FG, F⁻¹⟩

  Their expressions only use E, S, D, M₃, Sq, Hf, Rt, composition and F⁺; their values were
  computed in `UPRF.Sec6`. -/

lemma exprMinusI_in_GE {F : UFun} (h : CGE F) : CGE (exprMinusI F) := by
  unfold exprMinusI; have := S_in_GE; have := M3_in_GE; have := Sq_in_GE; cs
lemma exprOplus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (exprOplus F G) := by
  unfold exprOplus; have := exprMinusI_in_GE hF; have := Sq_in_GE; cs
lemma exprOminus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (exprOminus F G) := by
  unfold exprOminus; have := Sq_in_GE
  have : CGE (opPlusI F ∘ funE) := by cs
  have := exprMinusI_in_GE this; cs
lemma Phat_in_GE : CGE exprPhat := by
  unfold exprPhat
  exact exprOminus_in_GE (by have := Sq_in_GE; cs) S_in_GE
lemma exprOtimes_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (exprOtimes F G) := by
  unfold exprOtimes
  have sq := Sq_in_GE; have s := S_in_GE; have hf := Hf_in_GE; have rt := Rt_in_GE
  have ph := Phat_in_GE
  have a : CGE (funSq ∘ funS ∘ funSq ∘ F) := by cs
  have b := exprOplus_in_GE a hG
  have c := exprOminus_in_GE b (show CGE (funSq ∘ F) by cs)
  have d : CGE (funSq ∘ exprPhat ∘ exprOminus (exprOplus (funSq ∘ funS ∘ funSq ∘ F) G)
      (funSq ∘ F)) := by cs
  have e := exprOminus_in_GE d (show CGE (funSq ∘ G) by cs)
  have f : CGE (funHf ∘ funHf ∘ exprOminus (funSq ∘ exprPhat ∘ exprOminus (exprOplus
      (funSq ∘ funS ∘ funSq ∘ F) G) (funSq ∘ F)) (funSq ∘ G)) := by cs
  have g := exprOminus_in_GE f (show CGE (funSq ∘ F) by cs)
  cs
lemma exprPlus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (exprPlus F G) := by
  unfold exprPlus
  have pF : CGE (opPlusI F) := by cs
  have pG : CGE (opPlusI G) := by cs
  have t := exprOtimes_in_GE pF pG
  have d : CGE (funD ∘ exprOtimes (opPlusI F) (opPlusI G)) := by have := D_in_GE; cs
  have o := exprOplus_in_GE (exprOplus_in_GE d pF) pG
  have r : CGE (funRt ∘ exprOplus (exprOplus (funD ∘ exprOtimes (opPlusI F) (opPlusI G))
      (opPlusI F)) (opPlusI G)) := by have := Rt_in_GE; cs
  exact exprMinusI_in_GE (exprMinusI_in_GE r)
lemma exprMinus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (exprMinus F G) := by
  unfold exprMinus
  have a := exprPlus_in_GE hF hG
  have b : CGE (funSq ∘ exprPlus F G) := by have := Sq_in_GE; cs
  have c : CGE (funM3 ∘ F) := by have := M3_in_GE; cs
  have d := exprPlus_in_GE (exprPlus_in_GE b c) hG
  have := S_in_GE; cs

/-- Lemma 6.6 in clos ⟨1, E, F⁺, FG, F⁻¹⟩ -/
lemma plus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) : CGE (opPlus F G) :=
  exprPlus_eq F G ▸ exprPlus_in_GE hF hG

lemma minus_in_GE {F G : UFun} (hF : CGE F) (hG : CGE G) (h : ∀ x, G x ≤ F x) :
    CGE (opMinus F G) := by
  have : opDiffE F G = opMinus F G := funext fun x => dE_diff (h x)
  exact this ▸ exprMinus_eq F G ▸ exprMinus_in_GE hF hG

theorem JR_sub_GE : ∀ F, CJR F → CGE F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact S_in_GE | clos_solve)
    (fun u hu F hF => by basis_cases hu; clos_solve)
    (fun b hb F G hF hG => by basis_cases hb <;> first | exact plus_in_GE hF hG | clos_solve)

theorem GR_E_eq_JR (F : UFun) : CGE F ↔ CJR F := ⟨GE_sub_JR F, JR_sub_GE F⟩

/-! ## The bases with K and L -/

/-! ### K and L in clos ⟨1, E, F⁺, FG, F⁻¹⟩: K = I - A V and L = A S V - S, with
  A = Hf Sq⁺ and V = Hf (Rt S M₈ - 1) -/

def exprA : UFun := funHf ∘ opPlusI funSq
def exprV : UFun := funHf ∘ opMinus (funRt ∘ funS ∘ funD ∘ funD ∘ funD) (cst 1)

lemma A_expr : exprA = funA := by
  funext x; simp only [exprA, funA, funHf, opPlusI, funSq, Function.comp_apply]

lemma V_expr : exprV = funV := by
  funext x; simp only [exprV, funV, funHf, opMinus, funRt, funS, funD, cst, Function.comp_apply]
  ring_nf

lemma Rt_pos (n : ℕ) : 1 ≤ funRt (n + 1) := by
  by_contra h; push Not at h
  have := funRt_lt (n + 1)
  have h0 : funRt (n + 1) = 0 := by omega
  rw [h0] at this; omega

lemma A_in_GE : CGE funA := by
  rw [← A_expr]; unfold exprA; have := Hf_in_GE; have := Sq_in_GE; cs

lemma V_in_GE : CGE funV := by
  rw [← V_expr]; unfold exprV
  have m : CGE (opMinus (funRt ∘ funS ∘ funD ∘ funD ∘ funD) (cst 1)) := by
    apply minus_in_GE
    · have := Rt_in_GE; have := S_in_GE; have := D_in_GE; cs
    · cs
    · intro x; simp only [cst, Function.comp_apply, funS]; exact Rt_pos _
  have := Hf_in_GE; cs

lemma K_in_GE : CGE funK := by
  have h : opMinus funI (funA ∘ funV) = funK := by
    funext x; simp only [opMinus, funI, funK, Function.comp_apply]
  rw [← h]
  apply minus_in_GE I_in_GE
  · have := A_in_GE; have := V_in_GE; cs
  · intro x; exact (funA_V_le x).1

lemma L_in_GE : CGE funL := by
  have h : opMinus (funA ∘ funS ∘ funV) funS = funL := by
    funext x; simp only [opMinus, funS, funL, Function.comp_apply]; omega
  rw [← h]
  apply minus_in_GE _ S_in_GE
  · intro x; simp only [funS, Function.comp_apply]; have := (funA_V_le x).2; omega
  · have := A_in_GE; have := V_in_GE; have := S_in_GE; cs

theorem GK_sub_GE : ∀ F, CGK F → CGE F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact K_in_GE | cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

theorem GL_sub_GE : ∀ F, CGL F → CGE F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact L_in_GE | cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

/-! ### E in clos ⟨1, K, F⁺, FG, F⁻¹⟩ -/

lemma S_in_GK : CGK funS := by rw [← S_expr]; cs
lemma zero_in_GK : CGK (cst 0) := by rw [← zero_expr_K]; cs
lemma I_in_GK : CGK funI := by rw [← I_expr]; have := zero_in_GK; cs
lemma D_in_GK : CGK funD := by rw [← D_expr]; have := zero_in_GK; cs
lemma M3_in_GK : CGK funM3 := by rw [← M3_expr]; have := D_in_GK; cs

lemma surj_funK : Function.Surjective funK := fun x => ⟨funA x + x, funK_diag le_rfl⟩

lemma KZ (x : ℕ) : funK (funZ x) = x := funK_diag le_rfl

/-- K⁻¹ = Z -/
lemma Kinv_eq_Z : opInv funK = funZ := by
  funext x
  inv_eq surj_funK
  · exact KZ x
  · intro y hy
    obtain ⟨d1, d2⟩ := decomp y
    rw [hy] at d1 d2
    have := funA_mono d2
    simp only [funZ]; omega

lemma Z_in_GK : CGK funZ := by rw [← Kinv_eq_Z]; cs

lemma exprIminusF_in_GK {F : UFun} (h : CGK F) : CGK (exprIminusF F) := by
  unfold exprIminusF; have := Z_in_GK; have := S_in_GK; cs

/-- A ≡ Z - I, i.e. A ≡ K S S S (Y Z K)⁺ Z with Y ≡ (Z Z⁺ K)⁺ Z (Robinson's difference with
  α = Z(x), β = x; the sums with Z(x) use its left inverse K) -/
def exprAK : UFun :=
  funK ∘ funS ∘ funS ∘ funS ∘ opPlusI (opPlusI (funZ ∘ opPlusI funZ ∘ funK) ∘ funZ ∘ funK) ∘ funZ

lemma exprAK_in : CGK exprAK := by unfold exprAK; have := Z_in_GK; have := S_in_GK; cs

lemma A_expr_K : exprAK = funA := by
  funext x
  have h : exprAK x = funK (funZ (funZ x + x) + 2 * funZ x + 3) := by
    simp only [exprAK, Function.comp_apply, opPlusI, KZ, funS]; ring_nf
  rw [h, robinson_diff_K (by simp only [funZ]; omega)]
  simp only [funZ]; omega

lemma A_in_GK : CGK funA := by rw [← A_expr_K]; exact exprAK_in

/-- F⁻ ≡ K (S S S M₃ F K)⁺ (A F⁺)⁺ (if F(x) ≥ x) -/
def exprMinusIK (F : UFun) : UFun :=
  funK ∘ opPlusI (funS ∘ funS ∘ funS ∘ funM3 ∘ F ∘ funK) ∘ opPlusI (funA ∘ opPlusI F)

lemma exprMinusIK_in {F : UFun} (h : CGK F) : CGK (exprMinusIK F) := by
  unfold exprMinusIK; have := A_in_GK; have := S_in_GK; have := M3_in_GK; cs

lemma exprMinusIK_val {F : UFun} {x : ℕ} (h : x ≤ F x) : exprMinusIK F x = F x - x := by
  have k : funK (funA (F x + x) + x) = x := funK_diag (by omega)
  have e : exprMinusIK F x = funK (3 * F x + 1 + 1 + 1 + (funA (F x + x) + x)) := by
    simp only [exprMinusIK, Function.comp_apply, opPlusI, k, funS, funM3]
  have ar : 3 * F x + 1 + 1 + 1 + (funA (F x + x) + x) = funA (F x + x + 1 + 1) + (F x - x) := by
    have := funA_succ (F x + x); have := funA_succ (F x + x + 1); omega
  rw [e, ar, funK_diag (by omega)]

lemma Sq_expr_GK : exprMinusIK (exprMinusIK (exprMinusIK (funD ∘ funZ))) = funSq := by
  funext x
  have a : (funD ∘ funZ) x = x * x + 3 * x := by
    simp only [Function.comp_apply, funD, funZ]; have := two_funA x; linarith
  have b : exprMinusIK (funD ∘ funZ) x = x * x + 2 * x := by
    rw [exprMinusIK_val (by rw [a]; omega), a]; omega
  have c : exprMinusIK (exprMinusIK (funD ∘ funZ)) x = x * x + x := by
    rw [exprMinusIK_val (by rw [b]; omega), b]; omega
  rw [exprMinusIK_val (by rw [c]; omega), c]; simp only [funSq]; omega

lemma Sq_in_GK : CGK funSq := by
  rw [← Sq_expr_GK]
  have : CGK (funD ∘ funZ) := by have := D_in_GK; have := Z_in_GK; cs
  exact exprMinusIK_in (exprMinusIK_in (exprMinusIK_in this))

/-- the predecessor x - 1 -/
def funPred : UFun := fun x => x - 1

lemma surj_KS : Function.Surjective (funK ∘ funS) := by
  intro x
  refine ⟨funA (x + 1) + x - 1, ?_⟩
  have := funA_succ x
  have e : funA (x + 1) + x - 1 + 1 = funA (x + 1) + x := by omega
  simp only [Function.comp_apply, funS, e]; exact funK_diag (by omega)

/-- P ≡ K (K S)⁻¹ -/
lemma P_expr_K : funK ∘ opInv (funK ∘ funS) = funPred := by
  funext x
  simp only [Function.comp_apply, funPred]
  rcases x with _ | x
  · have : opInv (funK ∘ funS) 0 ≤ 0 := opInv_least surj_KS (by simpa [funS] using funK_one)
    have h0 : opInv (funK ∘ funS) 0 = 0 := by omega
    rw [h0]; simpa [funA_zero] using funK_diag (k := 0) (t := 0) le_rfl
  · have y := opInv_right surj_KS (x + 1)
    simp only [Function.comp_apply, funS] at y
    obtain ⟨d1, d2⟩ := decomp (opInv (funK ∘ funS) (x + 1) + 1)
    rw [y] at d1 d2
    have : opInv (funK ∘ funS) (x + 1) = funA (funV (opInv (funK ∘ funS) (x + 1) + 1)) + x := by
      omega
    rw [this, funK_diag (by omega)]; omega

lemma P_in_GK : CGK funPred := by rw [← P_expr_K]; have := S_in_GK; cs

lemma P_succ (y : ℕ) : funPred (y + 1) = y := by simp [funPred]

/-- U ≡ I - A K P (I - K), U(y) = V(y) + K(y) -/
def exprU : UFun := exprIminusF (funA ∘ funK ∘ funPred ∘ exprIminusF funK)

lemma exprU_in : CGK exprU := by
  unfold exprU
  have := A_in_GK; have := P_in_GK
  have := exprIminusF_in_GK (F := funK) (by cs)
  exact exprIminusF_in_GK (by cs)

lemma IminusK (y : ℕ) : exprIminusF funK y = funA (funV y) := by
  obtain ⟨d1, _⟩ := decomp y
  rw [exprIminusF_val (by omega)]; omega

lemma KP_sf (t : ℕ) : funK (funPred (funA t)) = t - 1 := by
  rcases t with _ | t
  · simp [funPred, funA_zero]; simpa [funA_zero] using funK_diag (k := 0) (t := 0) le_rfl
  · have : funPred (funA (t + 1)) = funA t + t := by simp only [funPred, funA_succ]; omega
    rw [this, funK_diag le_rfl]; omega

lemma exprU_val (y : ℕ) : exprU y = funV y + funK y := by
  obtain ⟨d1, d2⟩ := decomp y
  have inner : (funA ∘ funK ∘ funPred ∘ exprIminusF funK) y = funA (funV y - 1) := by
    simp only [Function.comp_apply, IminusK, KP_sf]
  have le : funA (funV y - 1) ≤ y := by have := funA_mono (Nat.sub_le (funV y) 1); omega
  unfold exprU
  rw [exprIminusF_val (by rw [inner]; exact le), inner]
  rcases h : funV y with _ | t
  · rw [h] at d1 d2; simp [funA_zero] at d1 ⊢; omega
  · rw [h] at d1; have := funA_succ t; simp only [Nat.add_sub_cancel]; omega

lemma exprU_pair {k t : ℕ} (h : k ≤ t) : exprU (funA t + k) = t + k := by
  rw [exprU_val, funV_diag h, funK_diag h]

lemma exprU_sf (t : ℕ) : exprU (funA t) = t := by
  simpa using exprU_pair (k := 0) (t := t) (Nat.zero_le t)

lemma surj_exprU : Function.Surjective exprU := fun x =>
  ⟨funA (x - x / 2) + x / 2, by rw [exprU_pair (by omega)]; omega⟩

lemma funA_lt_of_lt {s t : ℕ} (h : s < t) : funA s + s < funA t := by
  have := funA_mono (show s + 1 ≤ t from h); have := funA_succ s; omega

/-- Hf ≡ K U⁻¹ -/
lemma Hf_expr_K : funK ∘ opInv exprU = funHf := by
  funext x
  simp only [Function.comp_apply, funHf]
  set y := opInv exprU x with hy
  have u : funV y + funK y = x := by rw [← exprU_val]; exact opInv_right surj_exprU x
  obtain ⟨d1, d2⟩ := decomp y
  have : x / 2 ≤ funK y := by
    by_contra hc; push Not at hc
    have lt : x - x / 2 < funV y := by omega
    have w : exprU (funA (x - x / 2) + x / 2) = x := by rw [exprU_pair (by omega)]; omega
    have := opInv_least surj_exprU w
    rw [← hy] at this
    have := funA_lt_of_lt lt
    omega
  omega

lemma Hf_in_GK : CGK funHf := by rw [← Hf_expr_K]; have := exprU_in; cs

/-- B ≡ I - (I - Sq (I - Hf) U) (I - K), B(y) = K(y) + ⌈V(y)/2⌉² -/
def exprB : UFun :=
  exprIminusF (exprIminusF (funSq ∘ exprIminusF funHf ∘ exprU) ∘ exprIminusF funK)

lemma exprB_in : CGK exprB := by
  unfold exprB
  have := Sq_in_GK; have := exprU_in
  have := exprIminusF_in_GK Hf_in_GK
  have := exprIminusF_in_GK (F := funK) (by cs)
  have := exprIminusF_in_GK (F := funSq ∘ exprIminusF funHf ∘ exprU) (by cs)
  exact exprIminusF_in_GK (by cs)

lemma ceil_sq_le_sf (t : ℕ) : (t - t / 2) * (t - t / 2) ≤ funA t := by
  have h := two_funA t
  have h1 : 2 * (t - t / 2) ≤ t + 1 := by omega
  have h2 : t - t / 2 ≤ t := by omega
  nlinarith

lemma exprB_val (y : ℕ) :
    exprB y = funK y + (funV y - funV y / 2) * (funV y - funV y / 2) := by
  obtain ⟨d1, d2⟩ := decomp y
  have hf (t : ℕ) : exprIminusF funHf t = t - t / 2 := by
    rw [exprIminusF_val (by simp only [funHf]; omega)]; simp only [funHf]
  have inner : exprIminusF (funSq ∘ exprIminusF funHf ∘ exprU) (funA (funV y))
      = funA (funV y) - (funV y - funV y / 2) * (funV y - funV y / 2) := by
    rw [exprIminusF_val (by simp only [Function.comp_apply, exprU_sf, hf, funSq]; exact ceil_sq_le_sf _)]
    simp only [Function.comp_apply, exprU_sf, hf, funSq]
  have c := ceil_sq_le_sf (funV y)
  unfold exprB
  rw [exprIminusF_val (by simp only [Function.comp_apply, IminusK, inner]; omega)]
  simp only [Function.comp_apply, IminusK, inner]
  omega

lemma surj_exprB : Function.Surjective exprB := by
  intro x
  refine ⟨funA (2 * funRt x) + funE x, ?_⟩
  have b := funE_bound x
  rw [exprB_val, funV_diag b, funK_diag b]
  have := funE_add x
  have : 2 * funRt x - 2 * funRt x / 2 = funRt x := by omega
  rw [this]; omega

/-- E ≡ K B⁻¹: if B(y) = x then x = c² + K(y) with K(y) ≤ V(y) ≤ 2c, so E(x) = K(y) -/
lemma E_expr_GK : funK ∘ opInv exprB = funE := by
  funext x
  simp only [Function.comp_apply]
  have b := opInv_right surj_exprB x
  rw [exprB_val] at b
  obtain ⟨_, d2⟩ := decomp (opInv exprB x)
  set y := opInv exprB x
  set c := funV y - funV y / 2
  have : funK y ≤ 2 * c := by omega
  rw [← b, show funK y + c * c = c * c + funK y by ring, funE_sq_add this]

lemma E_in_GK : CGK funE := by rw [← E_expr_GK]; have := exprB_in; cs

theorem GE_sub_GK : ∀ F, CGE F → CGK F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact E_in_GK | cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

/-! ### K in clos ⟨1, L, F⁺, FG, F⁻¹⟩ -/

lemma K_in_GL : CGL funK := by rw [← K_expr_L]; cs

theorem GK_sub_GL : ∀ F, CGK F → CGL F :=
  clos_subset
    (fun F hF => by basis_cases hF <;> first | exact K_in_GL | cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

theorem GR_K_eq_JR (F : UFun) : CGK F ↔ CJR F :=
  ⟨fun h => GE_sub_JR F (GK_sub_GE F h), fun h => GE_sub_GK F (JR_sub_GE F h)⟩

theorem GR_L_eq_JR (F : UFun) : CGL F ↔ CJR F :=
  ⟨fun h => GE_sub_JR F (GL_sub_GE F h),
   fun h => GK_sub_GL F (GE_sub_GK F (JR_sub_GE F h))⟩

/-! ## The constant cannot be dropped

  In ⟨X, F⁺, FG, F⁻¹⟩ with X(0) = 0 every function fixes 0: F⁺(0) = F(0), and
  F⁻¹(0) = 0 when F(0) = 0. -/

lemma opInv_zero {F : UFun} (h : F 0 = 0) : opInv F 0 = 0 := by
  by_cases hs : Function.Surjective F
  · exact Nat.le_zero.1 (opInv_least hs h)
  · rw [opInv_not hs]; exact h

lemma GR0_fix0 {X : UFun} (X0 : X 0 = 0) {F : UFun} (h : Clos (basisGR0 X) F) : F 0 = 0 := by
  induction h with
  | init h => simp only [clos_defs, Set.mem_singleton_iff] at h; subst h; exact X0
  | unop hu _ ih =>
    simp only [clos_defs, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · simp [opPlusI, ih]
    · exact opInv_zero ih
  | binop hb _ _ ih₁ ih₂ =>
    simp only [clos_defs, Set.mem_singleton_iff] at hb; subst hb
    simp [ih₁, ih₂]

lemma funL_zero' : funL 0 = 0 := by simpa [funA_zero] using funL_diag (k := 0) (t := 0) le_rfl
lemma funK_zero' : funK 0 = 0 := by simpa [funA_zero] using funK_diag (k := 0) (t := 0) le_rfl

theorem GR0_not_one :
    ¬ Clos (basisGR0 funE) (cst 1) ∧ ¬ Clos (basisGR0 funK) (cst 1) ∧
      ¬ Clos (basisGR0 funL) (cst 1) :=
  ⟨fun h => by simpa [cst] using GR0_fix0 funE_small.1 h,
   fun h => by simpa [cst] using GR0_fix0 funK_zero' h,
   fun h => by simpa [cst] using GR0_fix0 funL_zero' h⟩

/-! ## Assuming Robinson's theorem

  J. Robinson's theorem (1950, §4, Thm. 3) is a hypothesis: her basis generates the set `GR`
  of unary general recursive functions. -/

section Robinson_1950

variable {GR : UFun → Prop} (Robinson_1950_sec4_thm3 : ∀ F, CJR F ↔ GR F)
include Robinson_1950_sec4_thm3

theorem Ext_GR :
    (∀ F, CGE F ↔ GR F) ∧ (∀ F, CGK F ↔ GR F) ∧ (∀ F, CGL F ↔ GR F) :=
  ⟨fun F => (GR_E_eq_JR F).trans (Robinson_1950_sec4_thm3 F),
   fun F => (GR_K_eq_JR F).trans (Robinson_1950_sec4_thm3 F),
   fun F => (GR_L_eq_JR F).trans (Robinson_1950_sec4_thm3 F)⟩

theorem Ext_GR0 :
    ¬ (∀ F, Clos (basisGR0 funE) F ↔ GR F) ∧ ¬ (∀ F, Clos (basisGR0 funK) F ↔ GR F) ∧
      ¬ (∀ F, Clos (basisGR0 funL) F ↔ GR F) := by
  have one : GR (cst 1) := (Robinson_1950_sec4_thm3 _).1 one_in_JR
  exact ⟨fun h => GR0_not_one.1 ((h _).2 one), fun h => GR0_not_one.2.1 ((h _).2 one),
    fun h => GR0_not_one.2.2 ((h _).2 one)⟩

end Robinson_1950

/-! ## Remark: 1 and S are interchangeable

  ⟨S, X, F⁺, FG, F⁻¹⟩ generates the same closure as ⟨1, X, F⁺, FG, F⁻¹⟩: S = 1⁺, and 1 = S 0,
  where 0 ≡ K S K⁻¹, 0 ≡ (E S E⁻¹)², 0 ≡ L (L S)⁻¹ S. -/

@[clos_defs] def basisGRS (X : UFun) : Basis := ⟨{funS, X}, {opPlusI, opInv}, {(· ∘ ·)}⟩

lemma GRS_sub_GR (X : UFun) : ∀ F, Clos (basisGRS X) F → Clos (basisGR X) F :=
  clos_subset
    (fun F hF => by
      basis_cases hF
      · rw [← S_expr]; cs
      · cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

lemma GR_sub_GRS {X : UFun} (Z : Clos (basisGRS X) (cst 0)) :
    ∀ F, Clos (basisGR X) F → Clos (basisGRS X) F := by
  have one : Clos (basisGRS X) (cst 1) := by rw [← one_expr]; cs
  exact clos_subset
    (fun F hF => by basis_cases hF <;> cs)
    (fun u hu F hF => by basis_cases hu <;> cs)
    (fun b hb F G hF hG => by basis_cases hb; cs)

/-- 0 ≡ K S K⁻¹: K⁻¹(x) + 1 = A(x) + x + 1 = A(x + 1) -/
lemma zero_expr_GRS_K : funK ∘ funS ∘ opInv funK = cst 0 := by
  funext x
  simp only [Function.comp_apply, Kinv_eq_Z, funS, funZ, cst]
  rw [show funA x + x + 1 = funA (x + 1) + 0 by rw [funA_succ]]
  exact funK_diag (Nat.zero_le _)

/-- E S E⁻¹ maps 2j to 0 and 2j + 1 to 2j + 2 -/
lemma ESEinv_val (x : ℕ) : (funE ∘ funS ∘ opInv funE) x = if x % 2 = 0 then 0 else x + 1 := by
  simp only [Function.comp_apply, funS, Einv_val]
  rcases Nat.even_or_odd x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h : (j + j + 1) / 2 = j := by omega
    rw [h, show (j + j) % 2 = 0 by omega, show j * j + (j + j) + 1 = (j + 1) * (j + 1) + 0 by ring]
    simp only [↓reduceIte]
    exact funE_sq_add (by omega)
  · have h : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [h, show (2 * j + 1) % 2 = 1 by omega,
      show (j + 1) * (j + 1) + (2 * j + 1) + 1 = (j + 1) * (j + 1) + (2 * j + 2) by ring]
    simp only [one_ne_zero, ↓reduceIte]
    rw [funE_sq_add (by omega)]

/-- 0 ≡ (E S E⁻¹)² -/
lemma zero_expr_GRS_E :
    (funE ∘ funS ∘ opInv funE) ∘ (funE ∘ funS ∘ opInv funE) = cst 0 := by
  funext x
  rw [Function.comp_apply (f := funE ∘ funS ∘ opInv funE), ESEinv_val x]
  split_ifs with h
  · rw [ESEinv_val]; simp [cst]
  · rw [ESEinv_val, show (x + 1) % 2 = 0 by omega]; rfl

lemma surj_LS : Function.Surjective (funL ∘ funS) := fun v =>
  ⟨funA (v + 1), by simpa [funS] using funL_diag (k := 1) (t := v + 1) (by omega)⟩

/-- the least y with L(y + 1) = x + 1 is A(x) + x -/
lemma LSinv_succ (x : ℕ) : opInv (funL ∘ funS) (x + 1) = funA x + x := by
  apply le_antisymm
  · apply opInv_least surj_LS
    simp only [Function.comp_apply, funS]
    rw [show funA x + x + 1 = funA (x + 1) + 0 by rw [funA_succ]]
    rw [funL_diag (Nat.zero_le _)]; omega
  · have y := opInv_right surj_LS (x + 1)
    simp only [Function.comp_apply, funS] at y
    obtain ⟨d1, d2⟩ := decomp (opInv (funL ∘ funS) (x + 1) + 1)
    have hl := funL_eq (opInv (funL ∘ funS) (x + 1) + 1)
    rw [y] at hl
    have := funA_mono (show x + 1 ≤ funV (opInv (funL ∘ funS) (x + 1) + 1) by omega)
    have := funA_succ x
    omega

/-- 0 ≡ L (L S)⁻¹ S -/
lemma zero_expr_GRS_L : funL ∘ opInv (funL ∘ funS) ∘ funS = cst 0 := by
  funext x
  simp only [Function.comp_apply, funS, LSinv_succ, cst]
  rw [funL_diag le_rfl]; omega

theorem GRS_eq_GR :
    (∀ F, Clos (basisGRS funE) F ↔ CGE F) ∧ (∀ F, Clos (basisGRS funK) F ↔ CGK F) ∧
      (∀ F, Clos (basisGRS funL) F ↔ CGL F) := by
  have zE : Clos (basisGRS funE) (cst 0) := by rw [← zero_expr_GRS_E]; cs
  have zK : Clos (basisGRS funK) (cst 0) := by rw [← zero_expr_GRS_K]; cs
  have zL : Clos (basisGRS funL) (cst 0) := by rw [← zero_expr_GRS_L]; cs
  exact ⟨fun F => ⟨GRS_sub_GR _ F, GR_sub_GRS zE F⟩, fun F => ⟨GRS_sub_GR _ F, GR_sub_GRS zK F⟩,
    fun F => ⟨GRS_sub_GR _ F, GR_sub_GRS zL F⟩⟩

theorem Ext_GRS {GR : UFun → Prop} (Robinson_1950_sec4_thm3 : ∀ F, CJR F ↔ GR F) :
    (∀ F, Clos (basisGRS funE) F ↔ GR F) ∧ (∀ F, Clos (basisGRS funK) F ↔ GR F) ∧
      (∀ F, Clos (basisGRS funL) F ↔ GR F) := by
  obtain ⟨hE, hK, hL⟩ := Ext_GR Robinson_1950_sec4_thm3
  exact ⟨fun F => (GRS_eq_GR.1 F).trans (hE F), fun F => (GRS_eq_GR.2.1 F).trans (hK F),
    fun F => (GRS_eq_GR.2.2 F).trans (hL F)⟩

end

end UPRF
