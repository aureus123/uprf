/-
  D. E. Severin, "Unary primitive recursive functions", J. Symbolic Logic 73(4), 2008.

  Section 2 (notation), bases and closures, Definition 3.2 (suitable bases),
  and the elementary arithmetic used silently in the paper.

  Naming: a function X of the paper is `funX`, an operator is `opX`; the juxtaposition
  FG of the paper is `F ∘ G`.
  Prim(ℕ,ℕ) is Mathlib's `Nat.Primrec` (zero, succ, unpair, pair, comp, prec).
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

namespace UPRF

/-- one-argument functions ℕ → ℕ -/
abbrev UFun := ℕ → ℕ

/-! ## Section 2: basic and arithmetic functions -/

def funI : UFun := fun x => x
def cst (n : ℕ) : UFun := fun _ => n
def funS : UFun := fun x => x + 1
def funD : UFun := fun x => 2 * x
def funSq : UFun := fun x => x * x
def funHf : UFun := fun x => x / 2
def funRt : UFun := Nat.sqrt
def funE : UFun := fun x => x - funRt x * funRt x
def funO : UFun := fun x => if x = 0 then 1 else 0
def funSgn : UFun := fun x => if x = 0 then 0 else 1
open Classical in
noncomputable def funQ : UFun := fun x => if ∃ k, x = k * k then 1 else 0

/-! Cantor pairing functions: A(x) = x(x+1)/2, V(x) = (Rt(8x+1) - 1)/2,
  K(x) = x - A(V(x)), L(x) = A(V(x)+1) - x - 1, J(x,y) = A(x+y) + x. -/
def funA : UFun := fun x => (x * x + x) / 2
def funV : UFun := fun x => (funRt (8 * x + 1) - 1) / 2
def funK : UFun := fun x => x - funA (funV x)
def funL : UFun := fun x => funA (funV x + 1) - x - 1
def funJ (x y : ℕ) : ℕ := funA (x + y) + x

/-! ## Operators -/

def opPlusI (F : UFun) : UFun := fun x => F x + x
def opPlus (F G : UFun) : UFun := fun x => F x + G x
def opMinus (F G : UFun) : UFun := fun x => F x - G x

/-- iteration F^□(a): F^□(a)(0) = a, F^□(a)(x+1) = F(F^□(a)(x)) -/
def opBoxA (a : ℕ) (F : UFun) : UFun := fun n => F^[n] a
/-- pure iteration F^□ = F^□(0) -/
def opBox (F : UFun) : UFun := opBoxA 0 F

@[simp] lemma opBox_zero (F : UFun) : opBox F 0 = 0 := rfl
@[simp] lemma opBox_succ (F : UFun) (n : ℕ) : opBox F (n + 1) = F (opBox F n) :=
  Function.iterate_succ_apply' F n 0
@[simp] lemma opBoxA_zero (a : ℕ) (F : UFun) : opBoxA a F 0 = a := rfl
@[simp] lemma opBoxA_succ (a : ℕ) (F : UFun) (n : ℕ) :
    opBoxA a F (n + 1) = F (opBoxA a F n) :=
  Function.iterate_succ_apply' F n a

/-! ## Bases and closures (end of Section 2) -/

/-- A basis ⟨F₁,…,Fₙ, F^⊕,…, F ⊗ G,…⟩: initial functions, unary and binary operators. -/
structure Basis where
  inits : Set UFun
  unops : Set (UFun → UFun)
  binops : Set (UFun → UFun → UFun)

/-- `Clos B F`: F is in the closure of the basis B (the least set containing the
  initial functions and closed under the operators). -/
inductive Clos (B : Basis) : UFun → Prop
  | init {F} : F ∈ B.inits → Clos B F
  | unop {u F} : u ∈ B.unops → Clos B F → Clos B (u F)
  | binop {b F G} : b ∈ B.binops → Clos B F → Clos B G → Clos B (b F G)

/-- Prim(ℕ,ℕ) -/
def PrimNN (F : UFun) : Prop := Nat.Primrec F

/-- Definition 3.2 -/
def Suitable (B : Basis) : Prop := ∀ F, Clos B F ↔ PrimNN F

/-- If the initial functions of B₁ lie in clos B₂ and clos B₂ is closed under the
  operators of B₁, then clos B₁ ⊆ clos B₂. -/
theorem clos_subset {B₁ B₂ : Basis} (I : ∀ F ∈ B₁.inits, Clos B₂ F)
    (U : ∀ u ∈ B₁.unops, ∀ F, Clos B₂ F → Clos B₂ (u F))
    (Bi : ∀ b ∈ B₁.binops, ∀ F G, Clos B₂ F → Clos B₂ G → Clos B₂ (b F G)) :
    ∀ F, Clos B₁ F → Clos B₂ F := by
  intro F h
  induction h with
  | init h => exact I _ h
  | unop hu _ ih => exact U _ hu _ ih
  | binop hb _ _ ih₁ ih₂ => exact Bi _ hb _ _ ih₁ ih₂

/-- Soundness: primitive recursive initial functions and operators preserving
  primitive recursiveness only generate primitive recursive functions. -/
theorem clos_sound {B : Basis} (I : ∀ F ∈ B.inits, PrimNN F)
    (U : ∀ u ∈ B.unops, ∀ F, PrimNN F → PrimNN (u F))
    (Bi : ∀ b ∈ B.binops, ∀ F G, PrimNN F → PrimNN G → PrimNN (b F G)) :
    ∀ F, Clos B F → PrimNN F := by
  intro F h
  induction h with
  | init h => exact I _ h
  | unop hu _ ih => exact U _ hu _ ih
  | binop hb _ _ ih₁ ih₂ => exact Bi _ hb _ _ ih₁ ih₂

/-- Every suitability proof of the paper simulates a suitable basis B₁ inside clos B₂. -/
theorem suitable_by_simulation {B₁ B₂ : Basis} (S : Suitable B₁)
    (I : ∀ F ∈ B₁.inits, Clos B₂ F)
    (U : ∀ u ∈ B₁.unops, ∀ F, Clos B₂ F → Clos B₂ (u F))
    (Bi : ∀ b ∈ B₁.binops, ∀ F G, Clos B₂ F → Clos B₂ G → Clos B₂ (b F G))
    (P : ∀ F, Clos B₂ F → PrimNN F) : Suitable B₂ := fun F =>
  ⟨P F, fun h => clos_subset I U Bi F ((S F).2 h)⟩

/-! ## Arithmetic facts used silently in the paper -/

lemma funRt_sq_le (n : ℕ) : funRt n * funRt n ≤ n := by
  have := Nat.sqrt_le' n; simp only [funRt]; nlinarith

lemma funRt_lt (n : ℕ) : n < (funRt n + 1) * (funRt n + 1) := by
  have := Nat.lt_succ_sqrt' n; simp only [funRt]; nlinarith

lemma funRt_unique {r n : ℕ} (h1 : r * r ≤ n) (h2 : n < (r + 1) * (r + 1)) : funRt n = r := by
  have a := funRt_sq_le n; have b := funRt_lt n
  rcases Nat.lt_trichotomy (funRt n) r with h | h | h
  · have : funRt n + 1 ≤ r := h
    nlinarith
  · exact h
  · have : r + 1 ≤ funRt n := h
    nlinarith

/-- ⌊√(m² + k)⌋ = m and E(m² + k) = k whenever k ≤ 2m -/
lemma funRt_sq_add {m k : ℕ} (h : k ≤ 2 * m) : funRt (m * m + k) = m :=
  funRt_unique (by omega) (by nlinarith)

lemma funE_sq_add {m k : ℕ} (h : k ≤ 2 * m) : funE (m * m + k) = k := by
  simp only [funE, funRt_sq_add h]; omega

@[simp] lemma funRt_sq (m : ℕ) : funRt (m * m) = m := by
  simpa using funRt_sq_add (m := m) (k := 0) (by omega)

lemma funE_add (x : ℕ) : funE x + funRt x * funRt x = x := by
  have := funRt_sq_le x; simp only [funE]; omega

/-- Robinson's difference formula: if b ≤ a then a - b = E((a+b)² + 3a + b + 1) -/
lemma robinson_diff_E {a b : ℕ} (h : b ≤ a) :
    funE ((a + b) * (a + b) + 3 * a + b + 1) = a - b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (b + d + b) * (b + d + b) + 3 * (b + d) + b + 1
      = (2 * b + d + 1) * (2 * b + d + 1) + d := by ring
  rw [this, funE_sq_add (by omega)]; omega

lemma funQ_iff (x : ℕ) : funQ x = if funE x = 0 then 1 else 0 := by
  have h : (∃ k, x = k * k) ↔ funE x = 0 := by
    constructor
    · rintro ⟨k, rfl⟩; simpa using funE_sq_add (m := k) (k := 0) (by omega)
    · intro h0; have := funE_add x; exact ⟨funRt x, by omega⟩
  unfold funQ; simp only [h]

/-! Cantor pairing -/

lemma two_funA (x : ℕ) : 2 * funA x = x * x + x := by
  have : 2 ∣ x * x + x := by
    have : x * x + x = x * (x + 1) := by ring
    rw [this]; exact (Nat.even_mul_succ_self x).two_dvd
  simp only [funA]; omega

lemma funA_succ (x : ℕ) : funA (x + 1) = funA x + x + 1 := by
  have h1 := two_funA x; have h2 := two_funA (x + 1); nlinarith

lemma funA_mono {m n : ℕ} (h : m ≤ n) : funA m ≤ funA n := by
  have h1 := two_funA m; have h2 := two_funA n; nlinarith

lemma funA_lt_imp {m n : ℕ} (h : funA m < funA n) : m < n := by
  by_contra h'; exact absurd (funA_mono (not_lt.1 h')) (not_le.2 h)

/-- V is the inverse of A: if A(t) ≤ x < A(t+1) then V(x) = t -/
lemma funV_char {t x : ℕ} (h1 : funA t ≤ x) (h2 : x < funA (t + 1)) : funV x = t := by
  have a := two_funA t; have b := two_funA (t + 1)
  have lo : (2 * t + 1) * (2 * t + 1) ≤ 8 * x + 1 := by nlinarith
  have hi : 8 * x + 1 < (2 * t + 3) * (2 * t + 3) := by nlinarith
  have : funRt (8 * x + 1) = 2 * t + 1 ∨ funRt (8 * x + 1) = 2 * t + 2 := by
    by_cases hc : (2 * t + 2) * (2 * t + 2) ≤ 8 * x + 1
    · exact Or.inr (funRt_unique hc (by nlinarith))
    · exact Or.inl (funRt_unique lo (by nlinarith))
  simp only [funV]; omega

lemma funA_index (x : ℕ) : ∃ t, funA t ≤ x ∧ x < funA (t + 1) := by
  induction x with
  | zero => exact ⟨0, by simp [funA], by simp [funA]⟩
  | succ x ih =>
    obtain ⟨t, h1, h2⟩ := ih
    by_cases h : x + 1 < funA (t + 1)
    · exact ⟨t, by omega, h⟩
    · refine ⟨t + 1, by omega, ?_⟩
      have := funA_succ (t + 1); omega

/-- values on a diagonal of the Cantor table: for k ≤ t,
  V(A(t)+k) = t, K(A(t)+k) = k and L(A(t)+k) = t - k -/
lemma funV_diag {k t : ℕ} (h : k ≤ t) : funV (funA t + k) = t :=
  funV_char (by omega) (by have := funA_succ t; omega)

lemma funK_diag {k t : ℕ} (h : k ≤ t) : funK (funA t + k) = k := by
  simp only [funK, funV_diag h]; omega

lemma funL_diag {k t : ℕ} (h : k ≤ t) : funL (funA t + k) = t - k := by
  simp only [funL, funV_diag h, funA_succ]; omega

lemma funA_V_le (x : ℕ) : funA (funV x) ≤ x ∧ x < funA (funV x + 1) := by
  obtain ⟨t, h1, h2⟩ := funA_index x
  rw [funV_char h1 h2]; exact ⟨h1, h2⟩

lemma decomp (x : ℕ) : x = funA (funV x) + funK x ∧ funK x ≤ funV x := by
  have ⟨h1, h2⟩ := funA_V_le x
  have := funA_succ (funV x)
  simp only [funK]; omega

lemma funL_eq (x : ℕ) : funL x = funV x - funK x := by
  obtain ⟨h1, h2⟩ := decomp x
  conv_lhs => rw [h1]
  exact funL_diag h2

lemma funK_J (x y : ℕ) : funK (funJ x y) = x := funK_diag (by omega)
lemma funL_J (x y : ℕ) : funL (funJ x y) = y := by
  rw [funJ, funL_diag (by omega)]; omega

/-! ## Primitive recursiveness of the functions and operators of the paper -/

lemma prim_of {f : UFun} (h : Primrec f) : PrimNN f := Primrec.nat_iff.1 h
lemma primrec_of {f : UFun} (h : PrimNN f) : Primrec f := Primrec.nat_iff.2 h

lemma cst_PR (n : ℕ) : PrimNN (cst n) := prim_of (Primrec.const n)
lemma funS_PR : PrimNN funS := prim_of Primrec.succ
lemma funRt_PR : PrimNN funRt := prim_of Primrec.nat_sqrt
lemma funE_PR : PrimNN funE :=
  prim_of (Primrec.nat_sub.comp Primrec.id
    (Primrec.nat_mul.comp Primrec.nat_sqrt Primrec.nat_sqrt))
lemma funSq_PR : PrimNN funSq := prim_of (Primrec.nat_mul.comp Primrec.id Primrec.id)
lemma funHf_PR : PrimNN funHf := prim_of (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
lemma funO_PR : PrimNN funO :=
  prim_of (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 1) (Primrec.const 0))
lemma funA_PR : PrimNN funA :=
  prim_of (Primrec.nat_div.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp Primrec.id Primrec.id) Primrec.id) (Primrec.const 2))
lemma funV_PR : PrimNN funV :=
  prim_of (Primrec.nat_div.comp (Primrec.nat_sub.comp (Primrec.nat_sqrt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id)
      (Primrec.const 1))) (Primrec.const 1)) (Primrec.const 2))
lemma funK_PR : PrimNN funK :=
  prim_of (Primrec.nat_sub.comp Primrec.id
    ((primrec_of funA_PR).comp (primrec_of funV_PR)))
lemma funL_PR : PrimNN funL :=
  prim_of (Primrec.nat_sub.comp (Primrec.nat_sub.comp ((primrec_of funA_PR).comp
    (Primrec.succ.comp (primrec_of funV_PR))) Primrec.id) (Primrec.const 1))

lemma comp_PR {F G : UFun} (hF : PrimNN F) (hG : PrimNN G) : PrimNN (F ∘ G) :=
  prim_of ((primrec_of hF).comp (primrec_of hG))
lemma opPlus_PR {F G : UFun} (hF : PrimNN F) (hG : PrimNN G) : PrimNN (opPlus F G) :=
  prim_of (Primrec.nat_add.comp (primrec_of hF) (primrec_of hG))
lemma opPlusI_PR {F : UFun} (hF : PrimNN F) : PrimNN (opPlusI F) :=
  prim_of (Primrec.nat_add.comp (primrec_of hF) Primrec.id)
lemma opBoxA_PR (a : ℕ) {F : UFun} (hF : PrimNN F) : PrimNN (opBoxA a F) :=
  prim_of (Primrec.nat_iterate Primrec.id (Primrec.const a)
    ((primrec_of hF).comp Primrec.snd).to₂)
lemma opBox_PR {F : UFun} (hF : PrimNN F) : PrimNN (opBox F) := opBoxA_PR 0 hF

end UPRF
