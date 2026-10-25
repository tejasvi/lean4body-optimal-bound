module

public import C4.Chart
public import C4Check.Formulas2
public import C4Check.Grid2
public import C4.SearchSound
public import C4.SearchSound2
public import C4.Chart2

@[expose] public section

/-!
# The covers of the region `𝒞`, and `sharp_cap`

The certificates prove the midpoint test on three regions, after the symmetry `ι` (`a ↦ 1/a`,
`C4.Symmetry`) has reduced every point of `𝒞` to one with `a ≤ 1`:
* the direct region `b ≥ 1/2`, in the coordinates `(a, b, c)`;
* the blow-up chart `0 < b ≤ 1/2`, in the coordinates `(b, al, ga)` with `a = 1 + b al`,
  `c = b ga`, outside the corner disc `b² + (ga - 1)² ≤ r₀²`;
* the corner disc, by the exact Taylor-form theorem `C4.CTF.corner_cap`.

This file collects the bounds that place every point in one of the covers, and assembles
`sharp_cap`.
-/

namespace C4

noncomputable section

/-- the six inequalities of `𝒞`, unfolded (as in `C4.Chart`) -/
private theorem inC_facts2 {a b c x : ℝ} (h : InC a b c x) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ -1 < x ∧ x < 1 ∧
    0 < b * b + 2 * b - a * a + 2 * a * x ∧ 0 < c * c + 2 * a * c - 1 + 2 * a * x ∧
    0 ≤ a - c - 2 * x ∧ 0 ≤ 1 - b - 2 * a * x ∧ 0 ≤ a - c + 2 * b * x ∧
    0 ≤ 1 - b + 2 * c * x := by
  obtain ⟨ha, hb, hc, hx0, hx1, g1, g2, g3, g4, g5, g6⟩ := h
  simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat] at g1 g2 g3 g4 g5 g6
  push_cast at g1 g2 g3 g4 g5 g6
  exact ⟨ha, hb, hc, hx0, hx1, g1, g2, by linarith, by linarith, g5, g6⟩

/-- `a c < 2 b + b²` on `𝒞` -/
private theorem inC_ac {a b c x : ℝ} (h : InC a b c x) : a * c < 2 * b + b * b := by
  obtain ⟨ha, hb, hc, hx0, hx1, g1, g2, g3, g4, g5, g6⟩ := inC_facts2 h
  nlinarith [mul_nonneg hc.le g4, mul_nonneg ha.le g6]

/-- **Bounds in the extended chart.**  For `0 < b ≤ 1/2` and `a ≤ 1` (after `ι`):
`-1/(2b) ≤ al ≤ 0` and `0 ≤ ga ≤ 5`, where `al = (a - 1)/b` and `ga = c/b`. -/
theorem chart_bounds2 {a b c x : ℝ} (h : InC a b c x) (hb2 : b ≤ 1 / 2) (ha1 : a ≤ 1) :
    -1 / (2 * b) ≤ (a - 1) / b ∧ (a - 1) / b ≤ 0 ∧ 0 ≤ c / b ∧ c / b ≤ 5 := by
  obtain ⟨ha, hb, hc, -⟩ := inC_facts2 h
  obtain ⟨ha12, -, -, -⟩ := bounds h
  have hac := inC_ac h
  have hc5 : c ≤ 5 * b := by
    refine le_of_not_gt fun hlt => ?_
    nlinarith [mul_le_mul_of_nonneg_right ha12 hc.le]
  refine ⟨?_, ?_, div_nonneg hc.le hb.le, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) hb]; nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  · rw [div_le_iff₀ hb]; linarith

/-! ## the root grids: every point of a region lies in a cell -/

theorem val_addsubBb2 {b c : ℕ} (h : c ≤ Nat.add Bb b) :
    val (Nat.sub (Nat.add Bb b) c) = ((b : ℝ) - c) / 2 ^ 96 := by
  unfold val
  rw [cast_sub_of_le h, cast_add, cBb]
  ring

theorem mul_pow_le2 {n s : ℕ} (hn : n ≤ 1001) (hs : s ≤ 96) : Nat.mul n (2 ^ s) ≤ Bb := by
  change n * 2 ^ s ≤ 2 ^ 256
  calc n * 2 ^ s ≤ 1001 * 2 ^ 96 :=
        Nat.mul_le_mul hn (Nat.pow_le_pow_right (by norm_num) hs)
    _ ≤ 2 ^ 256 := by norm_num

/-- a real `t` between the ends of cell `n` of `ivG s o n` lies in it -/
theorem mem_ivG {t : ℝ} {s o n : ℕ} (hs : s ≤ 96) (ho : o ≤ 1000) (hn : n ≤ 1000)
    (h1 : ((n : ℝ) - o) * 2 ^ s / 2 ^ 96 ≤ t) (h2 : t ≤ ((n : ℝ) + 1 - o) * 2 ^ s / 2 ^ 96) :
    I.mem t (ivG s o n) := by
  refine ⟨?_, ?_⟩
  · change -t ≤ val (Nat.sub (Nat.add Bb (Nat.mul o (2 ^ s))) (Nat.mul n (2 ^ s)))
    rw [val_addsubBb2 (le_trans (mul_pow_le2 (by omega) hs) (Nat.le_add_right _ _))]
    simp only [Nat.mul_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have e : ((o : ℝ) * 2 ^ s - n * 2 ^ s) / 2 ^ 96 = -(((n : ℝ) - o) * 2 ^ s / 2 ^ 96) := by ring
    rw [e]; linarith
  · change t ≤ val (Nat.sub (Nat.add Bb (Nat.mul (Nat.succ n) (2 ^ s))) (Nat.mul o (2 ^ s)))
    rw [val_addsubBb2 (le_trans (mul_pow_le2 (by omega) hs) (Nat.le_add_right _ _))]
    simp only [Nat.mul_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_succ]
    have e : (((n : ℝ) + 1) * 2 ^ s - o * 2 ^ s) / 2 ^ 96 = ((n : ℝ) + 1 - o) * 2 ^ s / 2 ^ 96 := by
      ring
    rw [e]; linarith

/-- a point of `[0, N]` lies in one of the cells `[i, i + 1]`, `i < N` -/
theorem cell_of2 {t : ℝ} {N : ℕ} (hN : 0 < N) (h0 : 0 ≤ t) (h1 : t ≤ N) :
    ∃ i : ℕ, i < N ∧ (i : ℝ) ≤ t ∧ t ≤ i + 1 := by
  refine ⟨min ⌊t⌋₊ (N - 1), by omega, ?_, ?_⟩
  · calc ((min ⌊t⌋₊ (N - 1) : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ t := Nat.floor_le h0
  · rcases le_total ⌊t⌋₊ (N - 1) with h | h
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one t).le
    · rw [min_eq_right h]
      have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [this]
      linarith

/-- the direct root grid covers `[1/2, 1] × [1/2, 1] × [0, 7/4]` -/
theorem dir2_cell {a b c : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) (hb1 : 1 / 2 ≤ b) (hb2 : b ≤ 1)
    (hc1 : 0 ≤ c) (hc2 : c ≤ 7 / 4) : ∃ n, n < 28 ∧ (dir2CellBox n).mem a b c := by
  obtain ⟨i, hi, hi1, hi2⟩ := cell_of2 (N := 2) (t := 4 * a - 2) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨j, hj, hj1, hj2⟩ := cell_of2 (N := 2) (t := 4 * b - 2) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨k, hk, hk1, hk2⟩ := cell_of2 (N := 7) (t := 4 * c) (by norm_num) (by linarith)
    (by push_cast; linarith)
  refine ⟨(2 * i + j) * 7 + k, by omega, ?_⟩
  have e1 : ((2 * i + j) * 7 + k) / 14 = i := by omega
  have e2 : ((2 * i + j) * 7 + k) / 7 % 2 = j := by omega
  have e3 : ((2 * i + j) * 7 + k) % 7 = k := by omega
  simp only [dir2CellBox, e1, e2, e3]
  refine ⟨mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_⟩ <;> push_cast <;>
    norm_num <;> linarith

/-- the chart root grid A covers `[1/4, 1/2] × [-2, 0] × [0, 5]` -/
theorem chA_cell {b al ga : ℝ} (hb1 : 1 / 4 ≤ b) (hb2 : b ≤ 1 / 2) (hal1 : -2 ≤ al)
    (hal2 : al ≤ 0) (hga1 : 0 ≤ ga) (hga2 : ga ≤ 5) : ∃ n, n < 20 ∧ (chACellBox n).mem b al ga := by
  obtain ⟨i, hi, hi1, hi2⟩ := cell_of2 (N := 2) (t := 8 * b - 2) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨j, hj, hj1, hj2⟩ := cell_of2 (N := 2) (t := al + 2) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨k, hk, hk1, hk2⟩ := cell_of2 (N := 5) (t := ga) (by norm_num) hga1
    (by push_cast; linarith)
  refine ⟨(2 * i + j) * 5 + k, by omega, ?_⟩
  have e1 : ((2 * i + j) * 5 + k) / 10 = i := by omega
  have e2 : ((2 * i + j) * 5 + k) / 5 % 2 = j := by omega
  have e3 : ((2 * i + j) * 5 + k) % 5 = k := by omega
  simp only [chACellBox, e1, e2, e3]
  refine ⟨mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_⟩ <;> push_cast <;>
    norm_num <;> linarith

/-- the chart root grid B covers `[1/8, 1/4] × [-4, 0] × [0, 5]` -/
theorem chB_cell {b al ga : ℝ} (hb1 : 1 / 8 ≤ b) (hb2 : b ≤ 1 / 4) (hal1 : -4 ≤ al)
    (hal2 : al ≤ 0) (hga1 : 0 ≤ ga) (hga2 : ga ≤ 5) : ∃ n, n < 20 ∧ (chBCellBox n).mem b al ga := by
  obtain ⟨j, hj, hj1, hj2⟩ := cell_of2 (N := 4) (t := al + 4) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨k, hk, hk1, hk2⟩ := cell_of2 (N := 5) (t := ga) (by norm_num) hga1
    (by push_cast; linarith)
  refine ⟨j * 5 + k, by omega, ?_⟩
  have e2 : (j * 5 + k) / 5 % 4 = j := by omega
  have e3 : (j * 5 + k) % 5 = k := by omega
  simp only [chBCellBox, e2, e3]
  refine ⟨mem_ivG (by norm_num) (by norm_num) (by norm_num) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_⟩ <;> push_cast <;>
    norm_num <;> linarith

/-- the chart root grid C covers `[0, 1/8] × [-2, 0] × [0, 3]` -/
theorem chC_cell {b al ga : ℝ} (hb1 : 0 ≤ b) (hb2 : b ≤ 1 / 8) (hal1 : -2 ≤ al)
    (hal2 : al ≤ 0) (hga1 : 0 ≤ ga) (hga2 : ga ≤ 3) : ∃ n, n < 24 ∧ (chCCellBox n).mem b al ga := by
  obtain ⟨j, hj, hj1, hj2⟩ := cell_of2 (N := 4) (t := 2 * al + 4) (by norm_num) (by linarith)
    (by push_cast; linarith)
  obtain ⟨k, hk, hk1, hk2⟩ := cell_of2 (N := 6) (t := 2 * ga) (by norm_num) (by linarith)
    (by push_cast; linarith)
  refine ⟨j * 6 + k, by omega, ?_⟩
  have e2 : (j * 6 + k) / 6 % 4 = j := by omega
  have e3 : (j * 6 + k) % 6 = k := by omega
  simp only [chCCellBox, e2, e3]
  refine ⟨mem_ivG (by norm_num) (by norm_num) (by norm_num) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_,
    mem_ivG (by norm_num) (by norm_num) (by omega) ?_ ?_⟩ <;> push_cast <;>
    norm_num <;> linarith

/-! ## the cap, assembled from the three covers -/

/-- the normalized midpoint test of `C4Check.Formulas2` at `ℝ`, direct chart -/
abbrev dirMidNR (a b c x : ℝ) : Out ℝ := @dirMidN ℝ opsReal a b c x

/-- the normalized midpoint test at `ℝ`, blow-up chart -/
abbrev chMidNR (b al ga xi : ℝ) : Out ℝ := @chMidN ℝ opsReal b al ga xi

/-- **The cap.**  Every normal-form CC with `a ≤ 1` passes the normalized midpoint test.  (The
points with `a > 1` are reduced to it by `ι` in `C4.Symmetry`.) -/
def SharpCapN : Prop :=
  ∀ a b c x : ℝ, InC a b c x → dirPR a b c x = 0 → a ≤ 1 →
    0 < (dirMidNR a b c x).det ∧ 0 < (dirMidNR a b c x).tr

/-- what the direct cover gives: the test on `b ≥ 1/2` -/
def DirCapN : Prop :=
  ∀ a b c x : ℝ, InC a b c x → dirPR a b c x = 0 → 1 / 2 ≤ b → a ≤ 1 →
    0 < (dirMidNR a b c x).det ∧ 0 < (dirMidNR a b c x).tr

/-- what the chart covers give: the chart test on `0 < b ≤ 1/2`, `al ≤ 0`, outside the corner
disc -/
def ChartCapN : Prop :=
  ∀ b al ga xi : ℝ, InC (1 + b * al) b (b * ga) (1 / 2 + b * xi) → chPR b al ga xi = 0 →
    0 < b → b ≤ 1 / 2 → al ≤ 0 → (1 / 128) ^ 2 < b ^ 2 + (ga - 1) ^ 2 →
    0 < (chMidNR b al ga xi).det ∧ 0 < (chMidNR b al ga xi).tr

/-- what the corner theorem gives (`C4.CTF.corner_cap`) -/
def CornerCapN : Prop :=
  ∀ b al ga xi : ℝ, 0 < b → al ≤ 0 → b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2 →
    InC (1 + b * al) b (b * ga) (1 / 2 + b * xi) → chPR b al ga xi = 0 →
    0 < (chMidNR b al ga xi).det ∧ 0 < (chMidNR b al ga xi).tr

/-- the chart test is the direct test at the image point (`C4.Chart2`) -/
def ChartEqN : Prop :=
  ∀ a b c x : ℝ, 0 < b → InC a b c x →
    (chMidNR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).det = (dirMidNR a b c x).det ∧
    (chMidNR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).tr = (dirMidNR a b c x).tr

/-- **Assembly.**  The three covers and the chart identity give the cap. -/
theorem sharp_cap_of (hD : DirCapN) (hCh : ChartCapN) (hK : CornerCapN) (hE : ChartEqN) :
    SharpCapN := by
  intro a b c x hC hP ha1
  obtain ⟨ha, hb, hc, -⟩ := inC_facts2 hC
  rcases le_total (1 / 2) b with hb2 | hb2
  · exact hD a b c x hC hP hb2 ha1
  -- the blow-up chart `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi`
  have ea : 1 + b * ((a - 1) / b) = a := by field_simp; ring
  have ec : b * (c / b) = c := by field_simp
  have ex : 1 / 2 + b * ((x - 1 / 2) / b) = x := by field_simp; ring
  have hC' : InC (1 + b * ((a - 1) / b)) b (b * (c / b)) (1 / 2 + b * ((x - 1 / 2) / b)) := by
    rw [ea, ec, ex]; exact hC
  obtain ⟨-, -, -, -, -, -, eP, -⟩ := chart_ids hC'
  rw [ea, ec, ex] at eP
  have hP' : chPR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b) = 0 := by rw [eP, hP, mul_zero]
  have hal : (a - 1) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le
  obtain ⟨e1, e2⟩ := hE a b c x hb hC
  rw [← e1, ← e2]
  rcases le_or_gt (b ^ 2 + (c / b - 1) ^ 2) ((1 / 128) ^ 2) with hr | hr
  · exact hK b _ _ _ hb hal hr hC' hP'
  · exact hCh b _ _ _ hC' hP' hb hb2 hal hr

/-! ## the covers give the region caps -/

/-- **The direct cap from the direct cover.** -/
theorem dirCapN_of_cover {M : Mode2} (hM : ModeSound2 M dirSem2) (hdisc : M.disc = none)
    (hcov : Cover2 M dir2CellBox 0 28) : DirCapN := by
  intro a b c x hC hP hb2 ha1
  obtain ⟨ha, hb, hc, hx0, hx1, -⟩ := inC_facts2 hC
  obtain ⟨ha12, -, hb1, hc74⟩ := bounds hC
  obtain ⟨n, hn, hmem⟩ := dir2_cell ha12 ha1 hb2 hb1 hc.le hc74
  have hgood := Certified2.good hM (hcov n (Nat.zero_le _) hn)
  obtain ⟨-, -, -, -, -, g1, g2, g3, g4, g5, g6⟩ := hC
  have hG : ∀ i, 0 ≤ (dirSem2.G a b c x).get i := by
    intro i
    fin_cases i
    exacts [g1.le, g2.le, g3, g4, g5, g6]
  have hPP : dirSem2.P a b c x = 0 := by
    change @dirP2 ℝ opsReal a b c x = 0
    rw [dirP2_eq (by linarith) (by linarith)]; exact hP
  rcases hgood a b c x hmem (fun _ => ⟨hx0.le, hx1.le⟩) hG hPP with h | ⟨k, hk, -⟩
  · exact h
  · rw [hdisc] at hk; exact absurd hk (by simp)

/-- **The chart cap from the three chart covers.** -/
theorem chartCapN_of_covers {M : Mode2} (hM : ModeSound2 M chSem2) (hclamp : M.clamp = false)
    (hdisc : M.disc = some 7) (hA : Cover2 M chACellBox 0 20) (hB : Cover2 M chBCellBox 0 20)
    (hCc : Cover2 M chCCellBox 0 24) : ChartCapN := by
  intro b al ga xi hC hP hb hb2 hal hr
  have hC0 := hC
  have hb' : b ≠ 0 := hb.ne'
  have ea : (1 + b * al - 1) / b = al := by field_simp; ring
  have ec : b * ga / b = ga := by field_simp
  obtain ⟨hal1, -, hga0, hga5⟩ := chart_bounds2 hC hb2 (by nlinarith)
  rw [ea] at hal1
  rw [ec] at hga0 hga5
  obtain ⟨G1, G2, G3, G4, G5, G6, -, -⟩ := chart_ids hC
  obtain ⟨-, -, -, -, -, g1, g2, g3, g4, g5, g6⟩ := hC
  have hG : ∀ i, 0 ≤ (chSem2.G b al ga xi).get i := by
    intro i
    fin_cases i
    · change 0 ≤ (chGR b al ga xi).x1; rw [G1]; exact div_nonneg g1.le hb.le
    · change 0 ≤ (chGR b al ga xi).x2; rw [G2]; exact div_nonneg g2.le hb.le
    · change 0 ≤ (chGR b al ga xi).x3; rw [G3]; exact div_nonneg g3 hb.le
    · change 0 ≤ (chGR b al ga xi).x4; rw [G4]; exact div_nonneg g4 hb.le
    · change 0 ≤ (chGR b al ga xi).x5; rw [G5]; exact g5
    · change 0 ≤ (chGR b al ga xi).x6; rw [G6]; exact g6
  have hPP : chSem2.P b al ga xi = 0 := by
    change @chP2 ℝ opsReal b al ga xi = 0
    have h24 : 0 ≤ 1 + b * (al + ga) := by
      obtain ⟨ha0, -, hc0, -⟩ := inC_facts2 hC0
      nlinarith
    rw [chP2_eq (by linarith) h24]; exact hP
  have key : ∀ {box : Nat → Box} {N : Nat}, Cover2 M box 0 N →
      (∃ n, n < N ∧ (box n).mem b al ga) →
      0 < (chMidNR b al ga xi).det ∧ 0 < (chMidNR b al ga xi).tr := by
    intro box N hcov ⟨n, hn, hmem⟩
    have hgood := Certified2.good hM (hcov n (Nat.zero_le _) hn)
    rcases hgood b al ga xi hmem (fun h => absurd h (by rw [hclamp]; simp)) hG hPP with
      h | ⟨k, hk, -, hk2⟩
    · exact h
    · have : k = 7 := by rw [hdisc] at hk; exact (Option.some.inj hk).symm
      subst this
      norm_num at hk2 hr
      linarith
  rcases le_total (1 / 4) b with hb4 | hb4
  · exact key hA (chA_cell hb4 hb2 (by
      have : -1 / (2 * b) ≥ -2 := by rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
      linarith) hal hga0 hga5)
  rcases le_total (1 / 8) b with hb8 | hb8
  · exact key hB (chB_cell hb8 hb4 (by
      have : -1 / (2 * b) ≥ -4 := by rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
      linarith) hal hga0 hga5)
  · have hcb := chart_bounds hC0 hb8
    rw [ea, ec] at hcb
    exact key hCc (chC_cell hb.le hb8 hcb.1 hal hga0 hcb.2.2.2)

/-- the chart identity (`C4.Chart2.ch2N_eq_inC`) -/
theorem chartEqN : ChartEqN := fun _ _ _ _ _ hC => ch2N_eq_inC hC

/-- **The cap from the four covers and the corner theorem**, for any sound direct mode without a
corner disc and any sound chart mode with the disc `r ≤ 1/128` -/
theorem sharp_cap_of_covers {Md Mc : Mode2} (hMd : ModeSound2 Md dirSem2) (hdd : Md.disc = none)
    (hMc : ModeSound2 Mc chSem2) (hcl : Mc.clamp = false) (hdc : Mc.disc = some 7)
    (hD : Cover2 Md dir2CellBox 0 28) (hA : Cover2 Mc chACellBox 0 20)
    (hB : Cover2 Mc chBCellBox 0 20) (hC : Cover2 Mc chCCellBox 0 24) (hK : CornerCapN) :
    SharpCapN :=
  sharp_cap_of (dirCapN_of_cover hMd hdd hD) (chartCapN_of_covers hMc hcl hdc hA hB hC) hK chartEqN

end

end C4
