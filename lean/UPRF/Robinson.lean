/-
  Robinson [15] (R. M. Robinson, Primitive recursive functions, Bull. AMS 53 (1947)),
  Section 7, Theorem 3, in the form Prim(ℕ,ℕ) ⊆ clos 𝓕.

  This is not Robinson's proof.  We induct on Mathlib's `Nat.Primrec` (zero, succ, the
  two components of `Nat.unpair`, `Nat.pair`, composition and primitive recursion) using
  only Lemmas 6.2-6.6.  Comparisons are obtained from the difference function dE of
  Lemma 6.6, and primitive recursion from F^□ by iterating one step function along the
  rows of a triangle (Cantor pairing J, K, L).
-/
import UPRF.Sec6

namespace UPRF

/-! ## More functions and operators in clos 𝓕 -/

lemma funI_eq_box_S : opBox funS = funI := by
  funext x; induction x with
  | zero => rfl
  | succ n ih => rw [opBox_succ, ih]; rfl

lemma I_in : C6 funI := funI_eq_box_S ▸ C6_box S_in

lemma plus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opPlus F G) := (Lemma_6_6 hF hG).1
lemma diffE_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opDiffE F G) := (Lemma_6_6 hF hG).2.1
lemma minus_le_in {F G} (hF : C6 F) (hG : C6 G) (h : ∀ x, G x ≤ F x) : C6 (opMinus F G) :=
  (Lemma_6_6 hF hG).2.2 h

/-- product without restrictions: FG = Hf((F + G)² - (F² + G²)) -/
lemma times_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opOtimes F G) := by
  have hX : C6 (opMinus (funSq ∘ opPlus F G) (opPlus (funSq ∘ F) (funSq ∘ G))) :=
    minus_le_in (C6_comp Sq_in (plus_in hF hG)) (plus_in (C6_comp Sq_in hF) (C6_comp Sq_in hG))
      (fun x => by simp only [opPlus, Function.comp, funSq]; nlinarith)
  have : funHf ∘ opMinus (funSq ∘ opPlus F G) (opPlus (funSq ∘ F) (funSq ∘ G))
      = opOtimes F G := by
    funext x
    simp only [Function.comp, opMinus, opPlus, funSq, funHf, opOtimes]
    have : (F x + G x) * (F x + G x) = F x * F x + G x * G x + 2 * (F x * G x) := by ring
    omega
  exact this ▸ C6_comp Hf_in hX

/-- definition by cases: F(x) if C(x) ≠ 0, G(x) otherwise; it is Sgn C · F + O C · G -/
def opCond (C F G : UFun) : UFun := fun x => if C x = 0 then G x else F x

lemma cond_in {C F G} (hC : C6 C) (hF : C6 F) (hG : C6 G) : C6 (opCond C F G) := by
  have : opPlus (opOtimes (funSgn ∘ C) F) (opOtimes (funO ∘ C) G) = opCond C F G := by
    funext x; by_cases h : C x = 0 <;> simp [opPlus, opOtimes, funSgn, funO, opCond, h]
  exact this ▸ plus_in (times_in (C6_comp Sgn_in hC) hF) (times_in (C6_comp O_in hC) hG)

/-! ## Comparison and truncated subtraction for arbitrary functions -/

lemma dE_lt {a b : ℕ} (h : a < b) : dE a b = 3 * a + b + 1 := by
  rw [dE, show (a + b) * (a + b) + 3 * a + b + 1 = (a + b) * (a + b) + (3 * a + b + 1) by ring]
  exact funE_sq_add (by omega)

/-- the indicator of F(x) < G(x): Sgn((F - G + G) - F) with the difference dE -/
def opLt (F G : UFun) : UFun := fun x => if F x < G x then 1 else 0

lemma lt_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opLt F G) := by
  have : funSgn ∘ opDiffE (opPlus (opDiffE F G) G) F = opLt F G := by
    funext x
    simp only [Function.comp, opDiffE, opPlus, opLt, funSgn]
    by_cases h : F x < G x
    · have e : dE (dE (F x) (G x) + G x) (F x) = 2 * F x + 2 * G x + 1 := by
        rw [dE_lt h, dE_diff (by omega)]; omega
      simp [e, h]
    · have e : dE (dE (F x) (G x) + G x) (F x) = 0 := by
        rw [dE_diff (a := F x) (b := G x) (by omega), Nat.sub_add_cancel (by omega),
          dE_diff le_rfl]; simp
      simp [e, h]
  exact this ▸ C6_comp Sgn_in (diffE_in (plus_in (diffE_in hF hG) hG) hF)

lemma minus_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opMinus F G) := by
  have : opCond (opLt F G) (cst 0) (opDiffE F G) = opMinus F G := by
    funext x
    simp only [opCond, opLt, opDiffE, opMinus, cst]
    by_cases h : F x < G x
    · simp [h]; omega
    · simp [h, dE_diff (show G x ≤ F x by omega)]
  exact this ▸ cond_in (lt_in hF hG) zero_in (diffE_in hF hG)

/-! ## The Cantor functions A, V, K, L and J(F, G) -/

lemma A_in : C6 funA := by
  have : funHf ∘ opPlusI funSq = funA := by funext x; rfl
  exact this ▸ C6_comp Hf_in (C6_plusI Sq_in)

lemma Phat_pos {n : ℕ} (h : 0 < n) : exprPhat n = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h; simpa using Phat_succ m

lemma V_in : C6 funV := by
  have : funHf ∘ exprPhat ∘ funRt ∘ funS ∘ funD ∘ funD ∘ funD = funV := by
    funext x
    have pos : 0 < funRt (8 * x + 1) := by
      have := funRt_lt (8 * x + 1); by_contra h; simp at h; rw [h] at this; omega
    simp only [Function.comp, funS, funD, funHf, funV]
    rw [show 2 * (2 * (2 * x)) + 1 = 8 * x + 1 by ring, Phat_pos pos]
  exact this ▸ C6_comp Hf_in (C6_comp Phat_in (C6_comp Rt_in (C6_comp S_in
    (C6_comp D_in (C6_comp D_in D_in)))))

lemma K_in : C6 funK := by
  have : opMinus funI (funA ∘ funV) = funK := by funext x; rfl
  exact this ▸ minus_in I_in (C6_comp A_in V_in)

lemma L_in : C6 funL := by
  have : opMinus funV funK = funL := by funext x; exact (funL_eq x).symm
  exact this ▸ minus_in V_in K_in

/-- J(F, G)(x) = J(F(x), G(x)) = A(F(x) + G(x)) + F(x) -/
def opJ (F G : UFun) : UFun := fun x => funJ (F x) (G x)

lemma J_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opJ F G) := by
  have : opPlus (funA ∘ opPlus F G) F = opJ F G := by funext x; rfl
  exact this ▸ plus_in (C6_comp A_in (plus_in hF hG)) hF

/-! ## Mathlib's pairing functions -/

def opPair (F G : UFun) : UFun := fun x => Nat.pair (F x) (G x)

lemma pair_in {F G} (hF : C6 F) (hG : C6 G) : C6 (opPair F G) := by
  have : opCond (opLt F G) (opPlus (funSq ∘ G) F) (opPlus (opPlus (funSq ∘ F) F) G)
      = opPair F G := by
    funext x
    simp only [opCond, opLt, opPlus, Function.comp, funSq, opPair, Nat.pair]
    by_cases h : F x < G x <;> simp [h]
  exact this ▸ cond_in (lt_in hF hG) (plus_in (C6_comp Sq_in hG) hF)
    (plus_in (plus_in (C6_comp Sq_in hF) hF) hG)

lemma unpair_eq (n : ℕ) : Nat.unpair n =
    if funE n < funRt n then (funE n, funRt n) else (funRt n, funE n - funRt n) := rfl

lemma unpair1_in : C6 (fun n => (Nat.unpair n).1) := by
  have : opCond (opLt funE funRt) funE funRt = fun n => (Nat.unpair n).1 := by
    funext n; rw [unpair_eq]; by_cases h : funE n < funRt n <;> simp [opCond, opLt, h]
  exact this ▸ cond_in (lt_in C6_E Rt_in) C6_E Rt_in

lemma unpair2_in : C6 (fun n => (Nat.unpair n).2) := by
  have : opCond (opLt funE funRt) funRt (opMinus funE funRt) = fun n => (Nat.unpair n).2 := by
    funext n; rw [unpair_eq]
    by_cases h : funE n < funRt n <;> simp [opCond, opLt, opMinus, h]
  exact this ▸ cond_in (lt_in C6_E Rt_in) Rt_in (minus_in C6_E Rt_in)

/-! ## Primitive recursion from iteration -/

section Rec

variable (f g : UFun)

/-- the recursion of `Nat.Primrec.prec`: R(z, 0) = f(z), R(z, y+1) = g(⟨z, ⟨y, R(z, y)⟩⟩) -/
def recF (z m : ℕ) : ℕ := Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) m

/-- A state J(J(N, y), v) stands for row N, column y ≤ N, value v = R(L(N - 1), y).
  The step function T moves to the next column, or to the start of the next row:
  T(J(J(N, y), v)) = J(J(N, y + 1), g⟨L(N - 1), ⟨y, v⟩⟩) if y < N, and
  T(J(J(N, N), v)) = J(J(N + 1, 0), f(L(N))). -/
def stepT : UFun :=
  opCond (opLt (funL ∘ funK) (funK ∘ funK))
    (opJ (opJ (funK ∘ funK) (funS ∘ funL ∘ funK))
      (g ∘ opPair (funL ∘ exprPhat ∘ funK ∘ funK) (opPair (funL ∘ funK) funL)))
    (opJ (opJ (funS ∘ funK ∘ funK) (cst 0)) (f ∘ funL ∘ funK ∘ funK))

def stT (N y : ℕ) : ℕ := funJ (funJ N y) (recF f g (funL (N - 1)) y)

variable {f g}

lemma stepT_in (hf : C6 f) (hg : C6 g) : C6 (stepT f g) :=
  cond_in (lt_in (C6_comp L_in K_in) (C6_comp K_in K_in))
    (J_in (J_in (C6_comp K_in K_in) (C6_comp S_in (C6_comp L_in K_in)))
      (C6_comp hg (pair_in (C6_comp L_in (C6_comp Phat_in (C6_comp K_in K_in)))
        (pair_in (C6_comp L_in K_in) L_in))))
    (J_in (J_in (C6_comp S_in (C6_comp K_in K_in)) zero_in)
      (C6_comp hf (C6_comp L_in (C6_comp K_in K_in))))

lemma stepT_val {N y v : ℕ} (h : y ≤ N) :
    stepT f g (funJ (funJ N y) v) =
      if y < N then funJ (funJ N (y + 1)) (g (Nat.pair (funL (N - 1)) (Nat.pair y v)))
      else funJ (funJ (N + 1) 0) (f (funL N)) := by
  by_cases hy : y < N
  · simp [stepT, opCond, opLt, opJ, opPair, Function.comp, funK_J, funL_J, funS, hy,
      Phat_pos (show 0 < N by omega)]
  · simp [stepT, opCond, opLt, opJ, Function.comp, funK_J, funL_J, funS, cst,
      show y = N by omega]

lemma funK_zero : funK 0 = 0 := by simpa [funA] using funK_diag (k := 0) (t := 0) le_rfl
lemma funL_zero : funL 0 = 0 := by simpa [funA] using funL_diag (k := 0) (t := 0) le_rfl
lemma funJ_zero : funJ 0 0 = 0 := rfl

lemma step_start : stepT f g 0 = stT f g 1 0 := by
  have := stepT_val (f := f) (g := g) (N := 0) (y := 0) (v := 0) le_rfl
  rw [funJ_zero, funJ_zero] at this
  rw [this]; simp [stT, recF, funL_zero]

lemma step_in_row {N y : ℕ} (h : y < N) : stepT f g (stT f g N y) = stT f g N (y + 1) := by
  rw [stT, stepT_val h.le]; simp [h]; rfl

lemma step_row_end (N : ℕ) : stepT f g (stT f g N N) = stT f g (N + 1) 0 := by
  rw [stT, stepT_val le_rfl]; simp [stT, recF]

lemma in_row {N : ℕ} (start : (stepT f g)^[funA N] 0 = stT f g N 0) :
    ∀ y ≤ N, (stepT f g)^[funA N + y] 0 = stT f g N y := by
  intro y hy
  induction y with
  | zero => exact start
  | succ y ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega), step_in_row (by omega)]

lemma row_start : ∀ N, 1 ≤ N → (stepT f g)^[funA N] 0 = stT f g N 0
  | 0, h => absurd h (by omega)
  | N + 1, _ => by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa [funA] using step_start (f := f) (g := g)
    · rw [funA_succ, Function.iterate_succ_apply', in_row (row_start N hN) N le_rfl,
        step_row_end]

/-- R(z, m) = L(T^□(A(J(m, z) + 1) + m)): the pair is computed in row J(m, z) + 1,
  whose parameter is L(J(m, z)) = z. -/
lemma recF_box (z m : ℕ) :
    recF f g z m = funL (opBox (stepT f g) (funA (funJ m z + 1) + m)) := by
  have hm : m ≤ funJ m z + 1 := by simp [funJ]; omega
  rw [opBox, opBoxA, in_row (row_start _ (by omega)) m hm, stT, funL_J]
  simp [funL_J]

lemma prec_in (hf : C6 f) (hg : C6 g) :
    C6 (Nat.unpaired fun z n => Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n) := by
  have : funL ∘ opBox (stepT f g) ∘ opPlus (funA ∘ funS ∘ opJ (fun n => (Nat.unpair n).2)
      (fun n => (Nat.unpair n).1)) (fun n => (Nat.unpair n).2)
      = Nat.unpaired fun z n => Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n := by
    funext n
    simp only [Function.comp, opPlus, opJ, funS, Nat.unpaired]
    exact (recF_box _ _).symm
  exact this ▸ C6_comp L_in (C6_comp (C6_box (stepT_in hf hg)) (plus_in (C6_comp A_in
    (C6_comp S_in (J_in unpair2_in unpair1_in))) unpair2_in))

end Rec

/-! ## Every primitive recursive function is in clos 𝓕 -/

theorem PrimNN_sub_C6 {F : UFun} (h : PrimNN F) : C6 F := by
  induction h with
  | zero => exact zero_in
  | succ => exact S_in
  | left => exact unpair1_in
  | right => exact unpair2_in
  | pair _ _ ihf ihg => exact pair_in ihf ihg
  | comp _ _ ihf ihg => exact C6_comp ihf ihg
  | prec _ _ ihf ihg => exact prec_in ihf ihg

/-! ## Robinson's basis ⟨S, E, F + G, FG, F^□⟩ -/

def basisRobinson : Basis := ⟨{funS, funE}, {opBox}, {opPlus, (· ∘ ·)}⟩

theorem Robinson_sound : ∀ F, Clos basisRobinson F → PrimNN F :=
  clos_sound
    (by rintro F (rfl | rfl); exacts [funS_PR, funE_PR])
    (by rintro u rfl F hF; exact opBox_PR hF)
    (by rintro b (rfl | rfl) F G hF hG; exacts [opPlus_PR hF hG, comp_PR hF hG])

theorem C6_sub_CR : ∀ F, C6 F → Clos basisRobinson F := by
  have S : Clos basisRobinson funS := .init (by simp [basisRobinson])
  have E : Clos basisRobinson funE := .init (by simp [basisRobinson])
  have box : ∀ {F}, Clos basisRobinson F → Clos basisRobinson (opBox F) :=
    fun h => .unop (u := opBox) (by simp [basisRobinson]) h
  have plus : ∀ {F G}, Clos basisRobinson F → Clos basisRobinson G →
      Clos basisRobinson (opPlus F G) :=
    fun h1 h2 => .binop (b := opPlus) (by simp [basisRobinson]) h1 h2
  have comp : ∀ {F G}, Clos basisRobinson F → Clos basisRobinson G →
      Clos basisRobinson (F ∘ G) :=
    fun h1 h2 => .binop (b := (· ∘ ·)) (by simp [basisRobinson]) h1 h2
  have I : Clos basisRobinson funI := funI_eq_box_S ▸ box S
  have boxE : opBox funE = cst 0 := by
    funext x; induction x with
    | zero => rfl
    | succ n ih => rw [opBox_succ, ih]; exact funE_small.1
  have one : funS ∘ opBox funE = cst 1 := by rw [boxE]; rfl
  apply clos_subset
  · rintro F (rfl | rfl)
    · exact one ▸ comp S (box E)
    · exact E
  · rintro u (rfl | rfl) F hF
    · exact (show opPlus F funI = opPlusI F from rfl) ▸ plus hF I
    · exact box hF
  · rintro b rfl F G hF hG; exact comp hF hG

/-- Robinson [15, §7, Theorem 3]: ⟨S, E, F + G, FG, F^□⟩ is suitable. -/
theorem Robinson_1947_sec7_thm3 : Suitable basisRobinson := fun F =>
  ⟨Robinson_sound F, fun h => C6_sub_CR F (PrimNN_sub_C6 h)⟩

end UPRF
