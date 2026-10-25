module

public import C4.CornerSound
public import C4.SearchSound
public import C4.Chart
public import C4.TFCommon

@[expose] public section

/-!
# The corner theorem

`corner_cap`: at every point of the blow-up chart with `al ≤ 0` in the corner disc
`b² + (ga - 1)² ≤ (1/128)²` that lies in `𝒞` and satisfies `P̂ = 0`, the normalized midpoint test
`chMidN` of `C4Check.Formulas2` is positive: `det > 0` and `tr > 0`.

Proof: the CC conditions put `al ≥ -17/32` (`alpha_range`), so `al` lies in one of three
`α`-intervals, each certified by a staged certificate (`staged_box_sound`).  In a box:
1. the root `ξ` of the CC lies in the interval `XB` (localisation, `loc_sound`);
2. a slope of `P̂` in `ξ` over the box (jets) relates `ξ` to the exact polynomial `Ξ`:
   `ξ = Ξ - P̂(Ξ)/s` (`slope_rel`), and `P̂(Ξ)` has a Taylor form without exact part;
3. the Taylor-form evaluation of `chMidN` at `ξ` (carrier `ET`) encloses `det` and `tr`;
   `finalOK` gives `det · (1 + p b + q g) > 0` on the disc, and the ranges give `tr > 0` and
   `1 + p b + q g > 0`.
-/

namespace C4
namespace CTF

noncomputable section

set_option exponentiation.threshold 1024

/-! ## small facts about the checker -/

theorem within_mem {X Y : I} (h : within X Y = true) {v : ℝ} (hv : I.mem v X) : I.mem v Y := by
  unfold within at h
  rw [sel_eq] at h
  split at h
  · next h1 =>
    have h1' : X.L ≤ Y.L := Nat.le_of_ble_eq_true h1
    have h2' : X.H ≤ Y.H := Nat.le_of_ble_eq_true h
    exact ⟨le_trans hv.1 (val_le_val h1'), le_trans hv.2 (val_le_val h2')⟩
  · exact absurd h Bool.false_ne_true

theorem allWithin_mem {Y : I} : ∀ {Xs : List I}, allWithin Y Xs = true → ∀ {X : I}, X ∈ Xs →
    ∀ {v : ℝ}, I.mem v X → I.mem v Y
  | [], _, _, hX, _, _ => absurd hX List.not_mem_nil
  | X0 :: Xs, h, X, hX, v, hv => by
    unfold allWithin at h
    rw [sel_eq] at h
    split at h
    · next h1 =>
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact within_mem h1 hv
      · exact allWithin_mem h hX' hv
    · exact absurd h Bool.false_ne_true

theorem posI_pos {A : I} (h : posI A = true) {v : ℝ} (hv : I.mem v A) : 0 < v := by
  have hlt : A.L < Bb := by unfold posI at h; simpa [Nat.blt_eq] using h
  exact I.pos_of_mem hv (by
    intro hb
    have := Nat.le_of_ble_eq_true hb
    omega)

/-! ## the slope of `P̂` in `ξ` -/

theorem wid_ge {X : I} {u v : ℝ} (hu : I.mem u X) (hv : I.mem v X) :
    |u - v| * 2 ^ 96 ≤ (wid X : ℝ) := by
  have h1 := sub_le_cast (Nat.add X.L X.H) B2
  rw [cast_add, cB2] at h1
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  unfold val at hu1 hu2 hv1 hv2
  unfold wid
  have hx : |u - v| ≤ ((X.H : ℝ) - 2 ^ 256) / 2 ^ 96 + ((X.L : ℝ) - 2 ^ 256) / 2 ^ 96 := by
    rw [abs_le]; constructor <;> linarith
  have : |u - v| * 2 ^ 96 ≤ (X.H : ℝ) + X.L - 2 ^ 257 := by
    have e : ((X.H : ℝ) - 2 ^ 256) / 2 ^ 96 + ((X.L : ℝ) - 2 ^ 256) / 2 ^ 96 =
        ((X.H : ℝ) + X.L - 2 ^ 257) / 2 ^ 96 := by ring
    rw [e, le_div_iff₀ (by positivity)] at hx
    exact hx
  linarith

theorem jvR_enc {S : Set P4} {zc : P4} {X : I} (k : Fin 4) (hS : ∀ z ∈ S, I.mem (z k) X)
    (hzc : I.mem (zc k) X) : JEnc S zc (fun z => z k) (jvR X k.val) := by
  refine ⟨hS, hzc, fun z _ => ⟨fun i => if i = k then 1 else 0, ?_, ?_⟩⟩
  · intro i
    fin_cases k <;> fin_cases i <;> simp [jvR, J.slope, I.mem_one, I.mem_zero]
  · simp

theorem radOK_full (B : Box) (XB : I) {zc : P4} (hzc : zc ∈ box4 B XB) :
    RadOK (box4 B XB) zc (radOf B XB) := by
  intro w hw
  obtain ⟨⟨w0, w1, w2⟩, w3⟩ := hw
  obtain ⟨⟨c0, c1, c2⟩, c3⟩ := hzc
  simp only [radOf]
  exact ⟨wid_ge w0 c0, wid_ge w1 c1, wid_ge w2 c2, wid_ge w3 c3⟩

/-- the jet of `P̂` over `B × XB` (centred anywhere in it) encloses `P̂` -/
theorem chP_jet {B : Box} {XB : I} {zc : P4} (hzc : zc ∈ box4 B XB) :
    OJEnc (box4 B XB) zc (fun z => chPR (z 0) (z 1) (z 2) (z 3))
      (@chP _ (jetOps (radOf B XB)) (some (jvR B.X0 0)) (some (jvR B.X1 1)) (some (jvR B.X2 2))
        (some (jvR XB 3))) := by
  obtain ⟨⟨c0, c1, c2⟩, c3⟩ := hzc
  exact chP_enc (radOK_full B XB ⟨⟨c0, c1, c2⟩, c3⟩)
    (OJEnc.some (jvR_enc (S := box4 B XB) 0 (fun w hw => hw.1.1) c0))
    (OJEnc.some (jvR_enc (S := box4 B XB) 1 (fun w hw => hw.1.2.1) c1))
    (OJEnc.some (jvR_enc (S := box4 B XB) 2 (fun w hw => hw.1.2.2) c2))
    (OJEnc.some (jvR_enc (S := box4 B XB) 3 (fun w hw => hw.2) c3))

theorem slope_rel {B : Box} {XB iS : I} (h : slopeInv B XB = some iS) {b al ga x1 x2 : ℝ}
    (hz : B.mem b al ga) (h1 : I.mem x1 XB) (h2 : I.mem x2 XB) :
    ∃ s : ℝ, s ≠ 0 ∧ I.mem s⁻¹ iS ∧ chPR b al ga x1 - chPR b al ga x2 = s * (x1 - x2) := by
  unfold slopeInv at h
  rcases hj : @chP _ (jetOps (radOf B XB)) (some (jvR B.X0 0)) (some (jvR B.X1 1))
      (some (jvR B.X2 2)) (some (jvR XB 3)) with _ | j
  · rw [hj] at h; cases h
  rw [hj] at h
  change j.s3.inv = some iS at h
  have hzc : (![b, al, ga, x2] : P4) ∈ box4 B XB := ⟨hz, h2⟩
  have hzS : (![b, al, ga, x1] : P4) ∈ box4 B XB := ⟨hz, h1⟩
  obtain ⟨-, -, hsl⟩ := chP_jet hzc j hj
  obtain ⟨s, hs, he⟩ := hsl _ hzS
  obtain ⟨hne, hinv⟩ := I.mem_inv (hs 3) h
  refine ⟨s 3, hne, hinv, ?_⟩
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_self, mul_zero,
    zero_add] at he
  exact he

/-! ## the localisation of the root -/

theorem loc_sound {B : Box} {XB : I} {hl : Nat} (h : locOK B XB hl = true) {b al ga xi : ℝ}
    (hz : B.mem b al ga) (hG : ∀ i, 0 ≤ (chSem.G b al ga xi).get i)
    (hP : chPR b al ga xi = 0) : I.mem xi XB := by
  unfold locOK at h
  have h' := beq_iff_eq.mp h
  obtain ⟨X, hX, hin⟩ := Option.bind_eq_some_iff.mp h'
  have hxX := xrange_sound chMode_sound hX hz (fun hc => absurd hc Bool.false_ne_true) hG
  by_cases ce : I.isEmpty X = true
  · exact absurd hxX (I.not_mem_of_isEmpty ce)
  · rw [sel_neg _ _ ce] at hin
    obtain ⟨r, hr, hall⟩ := Option.map_eq_some_iff.mp hin
    obtain ⟨Y, hY, hxY⟩ := locH_sound chMode_sound hz ⟨hG, hP⟩ 4096 hl [X] [] r hr
      (Or.inl ⟨X, List.mem_singleton_self X, hxX⟩)
    exact allWithin_mem hall hY hxY


/-! ## the final test -/

set_option exponentiation.threshold 256

/-- the quadratic part on the disc -/
theorem quad_lower {A B C l b g : ℝ} (pA : 0 < A - l) (pC : 0 < C - l)
    (pZ : 0 < (A - l) * (C - l) - B ^ 2 * (1 / 4)) :
    l * (b ^ 2 + g ^ 2) ≤ A * b ^ 2 + B * (b * g) + C * g ^ 2 := by
  nlinarith [sq_nonneg (2 * (A - l) * b + B * g), sq_nonneg g, mul_pos pA pC, mul_nonneg pZ.le (sq_nonneg g)]

theorem final_combine {v Q R m2 r2 l L : ℝ} (hv : v = Q + R) (hQ : l * r2 ≤ Q) (hR : -(m2 * L) ≤ R)
    (hm : m2 ≤ r2) (hL : 0 ≤ L) (hlL : 0 < l - L) (hr : 0 < r2) : 0 < v := by
  have h1 := mul_le_mul_of_nonneg_right hm hL
  have h2 := mul_pos hr hlL
  rw [hv]; nlinarith

section final
variable {D : Dom} {b g d : ℝ}

theorem eev_split3 (E : Ex) : eev E 0 b g d = hev (eget E 0) 0 0 b g d + hev (eget E 1) 0 1 b g d +
    hev (eget E 2) 0 2 b g d + eev (E.drop 3) 3 b g d := by
  rcases E with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, E⟩⟩⟩ <;> simp [eev_cons, eget] <;> ring

theorem lossE_drop3 (E : Ex) :
    lossE D 0 (kcomp (erng D E)) = lossE D 3 (kcomp (erng D (E.drop 3))) := by
  rcases E with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, E⟩⟩⟩ <;> simp [erng, kcomp, lossE, sel_eq]

/-- the parts of degree `≥ 3` are bounded by `m² Σ KC[d] ρ^(d-2)` -/
theorem eev_mag3 (hz : InBox D b g d) : ∀ (E : Ex) (k : ℕ), 3 ≤ k →
    |eev E k b g d / S| ≤ mx b g ^ 2 * ((lossE D k (kcomp (erng D E)) : ℝ) / 2 ^ 96)
  | [], k, _ => by
    simp only [eev_nil, erng, kcomp, lossE, zero_div, abs_zero, Nat.cast_zero, mul_zero, le_refl]
  | a :: E, k, hk => by
    simp only [eev_cons, erng, kcomp, lossE, sel_eq]
    rw [if_pos (Nat.ble_eq.mpr hk), cast_add]
    have hmx := mx_nonneg hz.b0 (g := g)
    have ha := hev_mag hz a 0 k
    have hm : mx b g ^ k ≤ mx b g ^ 2 * ((rpow D (k - 2) : ℝ) / 2 ^ 96) := by
      rw [show k = 2 + (k - 2) by omega, pow_add, Nat.add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hmx (mx_le hz) _)
        (rpow_ge D _)) (pow_nonneg hmx _)
    have hA : |hev a 0 k b g d / S| ≤
        mx b g ^ 2 * ((mmul (imagSum (hrng D a)) (rpow D (k - 2)) : ℝ) / 2 ^ 96) := by
      calc |hev a 0 k b g d / S| ≤ (imagSum (hrng D a) : ℝ) / 2 ^ 96 * mx b g ^ k := ha
        _ ≤ (imagSum (hrng D a) : ℝ) / 2 ^ 96 * (mx b g ^ 2 * ((rpow D (k - 2) : ℝ) / 2 ^ 96)) :=
          mul_le_mul_of_nonneg_left hm (off_nonneg _)
        _ = mx b g ^ 2 * ((imagSum (hrng D a) : ℝ) / 2 ^ 96 * ((rpow D (k - 2) : ℝ) / 2 ^ 96)) := by
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mmul_ge _ _) (pow_nonneg hmx _)
    have ih := eev_mag3 hz E (k + 1) (by omega)
    calc |(hev a 0 k b g d + eev E (k + 1) b g d) / S|
        = |hev a 0 k b g d / S + eev E (k + 1) b g d / S| := by rw [add_div]
      _ ≤ |hev a 0 k b g d / S| + |eev E (k + 1) b g d / S| := abs_add_le _ _
      _ ≤ _ := by rw [add_div, mul_add]; exact add_le_add hA ih

theorem rget_hrng_mem (hz : InBox D b g d) : ∀ (e : Hom) (i : ℕ),
    I.mem (qev (e.getD i []) d / S) (rget (hrng D e) i)
  | [], i => by cases i <;> simpa [hrng, rget] using I.mem_zero
  | c :: e, 0 => by simpa [hrng, rget] using qrng_mem D.wm D.s hz.d1 c
  | c :: e, i + 1 => by simpa [hrng, rget] using rget_hrng_mem hz e i

theorem rrow_erng (E : Ex) (k : ℕ) : rrow (erng D E) k = hrng D (eget E k) := by
  induction E generalizing k with
  | nil => cases k <;> rfl
  | cons a E ih => cases k with
    | zero => rfl
    | succ k => exact ih k

theorem hev_quad (e : Hom) (he : e.length ≤ 3) :
    hev e 0 2 b g d = qev (e.getD 0 []) d * g ^ 2 + qev (e.getD 1 []) d * (b * g) +
      qev (e.getD 2 []) d * b ^ 2 := by
  rcases e with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, e⟩⟩⟩⟩
  · simp
  · simp [hev_cons]
  · simp [hev_cons] <;> ring
  · simp [hev_cons] <;> ring
  · simp only [List.length_cons] at he; omega

theorem mx_sq_le (hb : 0 ≤ b) : mx b g ^ 2 ≤ b ^ 2 + g ^ 2 := by
  unfold mx
  rcases le_total b |g| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith
  · rw [max_eq_left h]; nlinarith

theorem quarter_mem : I.mem (1 / 4 : ℝ) quarterI := by
  have h4 : ((Int.ediv (S : Int) 4 : Int) : ℝ) = (S : ℝ) / 4 := by
    have e : Int.ediv (S : Int) 4 * 4 = (S : Int) := by decide
    generalize Int.ediv (S : Int) 4 = x at e ⊢
    have e' : ((x * 4 : Int) : ℝ) = ((S : Int) : ℝ) := by rw [e]
    push_cast at e'
    linarith
  have hS := S_pos
  have h1 : ((Int.ediv (S : Int) 4 : Int) : ℝ) / S = 1 / 4 := by
    rw [h4, div_right_comm, div_self hS.ne']
  unfold quarterI
  exact ivS_mem (le_of_eq h1) (le_of_eq h1.symm)

/-- **The final test.** -/
theorem finalOK_sound (hM : 2 ≤ D.M) (hz : InBox D b g d) {v : ℝ} {F : TF} {lam : Int}
    (hF : TFEncAt D b g d v F) (hok : finalOK D F lam = true) (hr : 0 < b ^ 2 + g ^ 2) :
    0 < v := by
  unfold finalOK at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hokF, h0⟩, h1⟩, hX⟩, hY⟩, hZ⟩, hL⟩ := hok
  obtain ⟨hw, -, hs, hr0, hH, hh, he⟩ := hF hokF
  have hmx := mx_nonneg hz.b0 (g := g)
  -- the quadratic coefficients
  set A := qev ((eget F.E 2).getD 2 []) d / S
  set B := qev ((eget F.E 2).getD 1 []) d / S
  set C := qev ((eget F.E 2).getD 0 []) d / S
  have hA : I.mem A (fA D F) := by unfold fA; rw [rrow_erng]; exact rget_hrng_mem hz _ 2
  have hB : I.mem B (fB D F) := by unfold fB; rw [rrow_erng]; exact rget_hrng_mem hz _ 1
  have hC : I.mem C (fC D F) := by unfold fC; rw [rrow_erng]; exact rget_hrng_mem hz _ 0
  have hlam : I.mem ((lam : ℝ) / S) (ivS lam lam) := ivS_mem le_rfl le_rfl
  set l := (lam : ℝ) / S
  have pA : 0 < A - l := posI_pos hX (I.mem_sub hA hlam)
  have pC : 0 < C - l := posI_pos hY (I.mem_sub hC hlam)
  have pZ : 0 < (A - l) * (C - l) - B ^ 2 * (1 / 4) :=
    posI_pos hZ (I.mem_sub (I.mem_mul (I.mem_sub hA hlam) (I.mem_sub hC hlam))
      (I.mem_mul (I.mem_sq hB) quarter_mem))
  have hloss : I.mem ((lossF D F : ℝ) / 2 ^ 96) ⟨Nat.add Bb (lossF D F), Nat.add Bb (lossF D F)⟩ := by
    have := off_nonneg (lossF D F)
    refine ⟨?_, ?_⟩ <;> simp only [val_addB'] <;> linarith
  have pL : 0 < l - (lossF D F : ℝ) / 2 ^ 96 := posI_pos hL (I.mem_sub hlam hloss)
  -- the quadratic part
  have hw2 : (eget F.E 2).length ≤ 3 := by
    rcases hE : F.E with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, E⟩⟩⟩
    · simp [eget]
    · simp [eget]
    · simp [eget]
    · rw [hE] at hw; exact hw.2.2.1
  have hq : hev (eget F.E 2) 0 2 b g d / S = A * b ^ 2 + B * (b * g) + C * g ^ 2 := by
    rw [hev_quad _ hw2]; simp only [A, B, C]; ring
  have hquad : l * (b ^ 2 + g ^ 2) ≤ A * b ^ 2 + B * (b * g) + C * g ^ 2 := quad_lower pA pC pZ
  -- the rest
  have hdrop := eev_mag3 hz (F.E.drop 3) 3 le_rfl
  have hT := tev_mag hz (M := D.M) 0 hH
  have hT2 : |tev hs 0 D.M b g| ≤ mx b g ^ 2 *
      ((mmul (imagSum F.H) (rpow D (D.M - 2)) : ℝ) / 2 ^ 96) := by
    have hm : mx b g ^ D.M ≤ mx b g ^ 2 * ((rpow D (D.M - 2) : ℝ) / 2 ^ 96) := by
      rw [show D.M = 2 + (D.M - 2) by omega, pow_add, Nat.add_sub_cancel_left]
      exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hmx (mx_le hz) _)
        (rpow_ge D _)) (pow_nonneg hmx _)
    calc |tev hs 0 D.M b g| ≤ (imagSum F.H : ℝ) / 2 ^ 96 * mx b g ^ D.M := hT
      _ ≤ (imagSum F.H : ℝ) / 2 ^ 96 * (mx b g ^ 2 * ((rpow D (D.M - 2) : ℝ) / 2 ^ 96)) :=
        mul_le_mul_of_nonneg_left hm (off_nonneg _)
      _ = mx b g ^ 2 * ((imagSum F.H : ℝ) / 2 ^ 96 * ((rpow D (D.M - 2) : ℝ) / 2 ^ 96)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mmul_ge _ _) (pow_nonneg hmx _)
  have hR2 : |hr0 * mx b g ^ (D.M + 1)| ≤ mx b g ^ 2 *
      ((mmul F.Hr (rpow D (D.M - 1)) : ℝ) / 2 ^ 96) := by
    have hm : mx b g ^ (D.M + 1) ≤ mx b g ^ 2 * ((rpow D (D.M - 1) : ℝ) / 2 ^ 96) := by
      rw [show D.M + 1 = 2 + (D.M - 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hmx (mx_le hz) _)
        (rpow_ge D _)) (pow_nonneg hmx _)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hmx _)]
    calc |hr0| * mx b g ^ (D.M + 1) ≤ (F.Hr : ℝ) / 2 ^ 96 *
          (mx b g ^ 2 * ((rpow D (D.M - 1) : ℝ) / 2 ^ 96)) :=
        mul_le_mul hh hm (pow_nonneg hmx _) (off_nonneg _)
      _ = mx b g ^ 2 * ((F.Hr : ℝ) / 2 ^ 96 * ((rpow D (D.M - 1) : ℝ) / 2 ^ 96)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mmul_ge _ _) (pow_nonneg hmx _)
  have hloss_eq : (lossF D F : ℝ) = (lossE D 3 (kcomp (erng D (F.E.drop 3))) : ℝ) +
      ((mmul (imagSum F.H) (rpow D (D.M - 2)) : ℝ) + (mmul F.Hr (rpow D (D.M - 1)) : ℝ)) := by
    unfold lossF; rw [cast_add, cast_add, lossE_drop3]
  have hsplit := eev_split3 F.E (b := b) (g := g) (d := d)
  rw [hzero_sound _ h0 0 0, hzero_sound _ h1 0 1, zero_add, zero_add] at hsplit
  have hm2 := mx_sq_le hz.b0 (g := g)
  have key : v = (A * b ^ 2 + B * (b * g) + C * g ^ 2) +
      (eev (F.E.drop 3) 3 b g d / S + tev hs 0 D.M b g + hr0 * mx b g ^ (D.M + 1)) := by
    rw [he, hsplit, add_div, hq]; ring
  have hrest : -(mx b g ^ 2 * ((lossF D F : ℝ) / 2 ^ 96)) ≤
      eev (F.E.drop 3) 3 b g d / S + tev hs 0 D.M b g + hr0 * mx b g ^ (D.M + 1) := by
    rw [hloss_eq]
    have := neg_abs_le (eev (F.E.drop 3) 3 b g d / S)
    have := neg_abs_le (tev hs 0 D.M b g)
    have := neg_abs_le (hr0 * mx b g ^ (D.M + 1))
    have e : mx b g ^ 2 * (((lossE D 3 (kcomp (erng D (F.E.drop 3))) : ℝ) +
        ((mmul (imagSum F.H) (rpow D (D.M - 2)) : ℝ) + (mmul F.Hr (rpow D (D.M - 1)) : ℝ))) / 2 ^ 96) =
        mx b g ^ 2 * ((lossE D 3 (kcomp (erng D (F.E.drop 3))) : ℝ) / 2 ^ 96) +
        mx b g ^ 2 * ((mmul (imagSum F.H) (rpow D (D.M - 2)) : ℝ) / 2 ^ 96) +
        mx b g ^ 2 * ((mmul F.Hr (rpow D (D.M - 1)) : ℝ) / 2 ^ 96) := by ring
    rw [e]
    linarith
  exact final_combine key hquad hrest hm2 (off_nonneg (lossF D F)) pL hr

end final


/-! ## the chart at the corner -/

section chart

/-- the CC constraints of the chart are nonnegative at a point of `𝒞` -/
theorem chG_nonneg {b al ga xi : ℝ} (hb : 0 < b)
    (hC : InC (1 + b * al) b (b * ga) (1 / 2 + b * xi)) :
    ∀ i, 0 ≤ (chSem.G b al ga xi).get i := by
  obtain ⟨G1, G2, G3, G4, G5, G6, -, -⟩ := chart_ids hC
  obtain ⟨-, -, -, -, -, g1, g2, g3, g4, g5, g6⟩ := hC
  intro i
  fin_cases i
  · change 0 ≤ (chGR b al ga xi).x1; rw [G1]; exact div_nonneg g1.le hb.le
  · change 0 ≤ (chGR b al ga xi).x2; rw [G2]; exact div_nonneg g2.le hb.le
  · change 0 ≤ (chGR b al ga xi).x3; rw [G3]; exact div_nonneg g3 hb.le
  · change 0 ≤ (chGR b al ga xi).x4; rw [G4]; exact div_nonneg g4 hb.le
  · change 0 ≤ (chGR b al ga xi).x5; rw [G5]; exact g5
  · change 0 ≤ (chGR b al ga xi).x6; rw [G6]; exact g6

theorem disc_b {b ga : ℝ} (hb : 0 < b) (hr : b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2) :
    b ≤ 1 / 128 := by
  nlinarith [sq_nonneg (ga - 1)]

theorem disc_g {b ga : ℝ} (hr : b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2) :
    |ga - 1| ≤ 1 / 128 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg b]

/-- `a² + a g + g² ≤ 6` and `≥ 0` for `-2 ≤ a ≤ 0`, `|g - 1| ≤ 1/128` -/
theorem quad_alga {al ga : ℝ} (h1 : -2 ≤ al) (h2 : al ≤ 0) (h3 : 0 ≤ ga) (h4 : ga ≤ 1 + 1 / 128) :
    0 ≤ al ^ 2 + al * ga + ga ^ 2 ∧ al ^ 2 + al * ga + ga ^ 2 ≤ 6 := by
  constructor
  · nlinarith [sq_nonneg (al + ga / 2), sq_nonneg ga]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ al + 2) (by linarith : (0 : ℝ) ≤ -al),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -al) h3, mul_le_mul h4 h4 h3 (by norm_num)]

/-- **The `α`-range.**  In the corner disc, `-17/32 ≤ al`: by `h₂ > 0`, `h₃ ≥ 0` and `a > 0`,
`2 al + ga + b (al² + al ga + ga²) > 0`. -/
theorem alpha_range {b al ga xi : ℝ} (hb : 0 < b) (hal : al ≤ 0)
    (hr : b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2)
    (hC : InC (1 + b * al) b (b * ga) (1 / 2 + b * xi)) : -17 / 32 ≤ al := by
  have hb1 := disc_b hb hr
  obtain ⟨hg1, hg2⟩ := abs_le.mp (disc_g hr)
  have hcb := chart_bounds hC (by linarith)
  have ea : (1 + b * al - 1) / b = al := by field_simp; ring
  rw [ea] at hcb
  obtain ⟨G1, G2, G3, G4, G5, G6, -, -⟩ := chart_ids hC
  obtain ⟨ha, -, -, -, -, g1, g2, g3, g4, g5, g6⟩ := hC
  have h2 : 0 < (chGR b al ga xi).x2 := by rw [G2]; exact div_pos g2 hb
  have h3 : 0 ≤ (chGR b al ga xi).x3 := by rw [G3]; exact div_nonneg g3 hb.le
  simp only [chGR, chG, aff, chK, chL, opsReal_ofNat, opsReal_sq] at h2 h3
  push_cast at h2 h3
  have key : 0 < 2 * al + ga + b * (al ^ 2 + al * ga + ga ^ 2) := by
    nlinarith [mul_nonneg ha.le h3]
  obtain ⟨hq0, hq⟩ := quad_alga (ga := ga) hcb.1 hal (by linarith) (by linarith)
  have hbq : b * (al ^ 2 + al * ga + ga ^ 2) ≤ 1 / 128 * 6 := mul_le_mul hb1 hq hq0 (by norm_num)
  linarith

end chart

/-! ## the carrier

The generic carrier of `C4.TFCommon` over `P = Unit`: a real number (`f ()`) with an optional Taylor
form that encloses it at the point `(b, g, d)`. -/

/-- the enclosure at the point `(b, g, d)` -/
def EncAt (D : Dom) (b g d : ℝ) (f : Unit → ℝ) (t : TF) : Prop := TFEncAt D b g d (f ()) t

section carrier
variable {D : Dom} {b g d : ℝ}

/-- **Soundness of the Taylor-form operations** at a point of the box. -/
theorem opsSoundAt (hM : 1 ≤ D.M) (hz : InBox D b g d) :
    @OpsSound Unit TF (tfOps D) (EncAt D b g d) := by
  refine @OpsSound.mk Unit TF (tfOps D) (EncAt D b g d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro f1 f2 x y hx hy
    rcases x with _ | tx <;> rcases y with _ | ty <;> intro tf htf <;>
      try cases htf
    exact add_at (hx _ rfl) (hy _ rfl)
  · intro f1 f2 x y hx hy
    rcases x with _ | tx <;> rcases y with _ | ty <;> intro tf htf <;>
      try cases htf
    exact sub_at (hx _ rfl) (hy _ rfl)
  · intro f1 f2 x y hx hy
    rcases x with _ | tx <;> rcases y with _ | ty <;> intro tf htf <;>
      try cases htf
    exact mul_at hM hz (hx _ rfl) (hy _ rfl)
  · intro f1 f2 x y hx hy
    rcases x with _ | tx <;> rcases y with _ | ty <;> intro tf htf <;>
      try cases htf
    change (TF.inv D ty).map (fun ib => TF.mul D tx ib) = some tf at htf
    rcases hinv : TF.inv D ty with _ | iy
    · rw [hinv] at htf; cases htf
    · rw [hinv] at htf
      obtain rfl := Option.some.inj htf
      change TFEncAt D b g d (f1 () / f2 ()) _
      rw [div_eq_mul_inv]
      exact mul_at hM hz (hx _ rfl) (inv_at hM hz (hy _ rfl) hinv)
  · intro f1 x hx
    rcases x with _ | tx <;> intro tf htf <;> try cases htf
    exact neg_at (hx _ rfl)
  · intro f1 x hx
    rcases x with _ | tx <;> intro tf htf
    · cases htf
    · exact sqrt_at hM hz (hx _ rfl) htf
  · intro f1 x hx
    rcases x with _ | tx <;> intro tf htf <;> try cases htf
    change TFEncAt D b g d (f1 () ^ 2) _
    rw [pow_two]
    exact mul_at hM hz (hx _ rfl) (hx _ rfl)
  · intro n tf htf
    change some (TF.cst D [n * (S : Int)]) = some tf at htf
    obtain rfl := Option.some.inj htf
    have := cst_at D b g d [n * (S : Int)]
    have hS := S_pos
    simp only [qev_cons, qev_nil, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast] at this
    rwa [mul_div_cancel_right₀ _ hS.ne'] at this

end carrier


/-! ## the formulas at generic carriers

For a variable checker instance `Ops (Option T)` nothing can compute, so the checker half of a
formula at carriers is identified with the formula at the checker values structurally. -/

section generic
variable {P T : Type} [Ops (Option T)] {Enc : (P → ℝ) → T → Prop} (hs : OpsSound P T Enc)
  (c0 c1 c2 c3 : Carrier P T Enc)
include hs

theorem chP_carrier :
    OEncG Enc (fun z => chPR (c0.f z) (c1.f z) (c2.f z) (c3.f z)) (chP c0.o c1.o c2.o c3.o) :=
  (@chP _ (carrierOps hs) c0 c1 c2 c3).ok

theorem chYIn_carrier :
    (@chYIn _ (carrierOps hs) c0 c1 c2 c3).map Carrier.o = chYIn c0.o c1.o c2.o c3.o ∧
    ∀ z, (@chYIn _ (carrierOps hs) c0 c1 c2 c3).map (fun c => c.f z) =
      @chYIn ℝ opsReal (c0.f z) (c1.f z) (c2.f z) (c3.f z) :=
  ⟨rfl, fun _ => rfl⟩

omit c0 c1 c2 c3 in
theorem midY_carrier (A : YIn (Carrier P T Enc)) :
    OEncG Enc (fun z => (@YIn.Y ℝ opsReal (A.map (fun c => c.f z))).1) (YIn.Y (A.map Carrier.o)).1 ∧
    OEncG Enc (fun z => (@YIn.Y ℝ opsReal (A.map (fun c => c.f z))).2) (YIn.Y (A.map Carrier.o)).2 :=
  ⟨(@YIn.Y _ (carrierOps hs) A).1.ok, (@YIn.Y _ (carrierOps hs) A).2.ok⟩

theorem chMidN_carrier :
    OEncG Enc (fun z => (@chMidN ℝ opsReal (c0.f z) (c1.f z) (c2.f z) (c3.f z)).det)
      (chMidN c0.o c1.o c2.o c3.o).det ∧
    OEncG Enc (fun z => (@chMidN ℝ opsReal (c0.f z) (c1.f z) (c2.f z) (c3.f z)).tr)
      (chMidN c0.o c1.o c2.o c3.o).tr := by
  obtain ⟨eo, ef⟩ := chYIn_carrier hs c0 c1 c2 c3
  obtain ⟨k1, k2⟩ := midY_carrier hs (@chYIn _ (carrierOps hs) c0 c1 c2 c3)
  rw [eo] at k1 k2
  simp only [ef] at k1 k2
  rw [chMidN_det_eq, chMidN_tr_eq]
  simp only [chMidN_det_eq, chMidN_tr_eq]
  exact ⟨k1, k2⟩

omit hs in
/-- pointwise forms over `P = Unit` with the checker values as variables, so that instances of the
conclusion mention the given checker terms literally (a checker that reduces a projection of
`chMidN` at a concrete checker instance runs the Taylor-form code on symbolic data) -/
theorem chP_carrier_pt {T : Type} [Ops (Option T)] {Enc : (Unit → ℝ) → T → Prop}
    (hs : OpsSound Unit T Enc) {x0 x1 x2 x3 : ℝ} {o0 o1 o2 o3 : Option T}
    (h0 : OEncG Enc (fun _ => x0) o0) (h1 : OEncG Enc (fun _ => x1) o1)
    (h2 : OEncG Enc (fun _ => x2) o2) (h3 : OEncG Enc (fun _ => x3) o3) :
    OEncG Enc (fun _ => chPR x0 x1 x2 x3) (chP o0 o1 o2 o3) :=
  chP_carrier hs ⟨fun _ => x0, o0, h0⟩ ⟨fun _ => x1, o1, h1⟩ ⟨fun _ => x2, o2, h2⟩
    ⟨fun _ => x3, o3, h3⟩

omit hs in
theorem chMidN_carrier_pt {T : Type} [Ops (Option T)] {Enc : (Unit → ℝ) → T → Prop}
    (hs : OpsSound Unit T Enc) {x0 x1 x2 x3 : ℝ} {o0 o1 o2 o3 : Option T}
    (h0 : OEncG Enc (fun _ => x0) o0) (h1 : OEncG Enc (fun _ => x1) o1)
    (h2 : OEncG Enc (fun _ => x2) o2) (h3 : OEncG Enc (fun _ => x3) o3) :
    OEncG Enc (fun _ => (@chMidN ℝ opsReal x0 x1 x2 x3).det) (chMidN o0 o1 o2 o3).det ∧
      OEncG Enc (fun _ => (@chMidN ℝ opsReal x0 x1 x2 x3).tr) (chMidN o0 o1 o2 o3).tr :=
  chMidN_carrier hs ⟨fun _ => x0, o0, h0⟩ ⟨fun _ => x1, o1, h1⟩ ⟨fun _ => x2, o2, h2⟩
    ⟨fun _ => x3, o3, h3⟩

end generic

/-! ## one `α`-box -/

section box

theorem enc_range {D : Dom} {b g d : ℝ} (hz : InBox D b g d) {u : ℝ} {t : TF}
    (h : TFEncAt D b g d u t) (hok : t.ok = true) : I.mem u (t.range D) := by
  obtain ⟨-, -, hs, hr, hH, hh, he⟩ := h hok
  rw [he]; exact (range_mem hz hH hh).1

theorem mult_at {D : Dom} {b g d : ℝ} (hM : 1 ≤ D.M) (hz : InBox D b g d) (p q : Int) :
    TFEncAt D b g d (1 + ((p : ℝ) / S * b + (q : ℝ) / S * g)) (TF.mult D p q) := by
  have h1 := cst_at D b g d [(S : Int)]
  have hp := cst_at D b g d [p]
  have hq := cst_at D b g d [q]
  simp only [qev_cons, qev_nil, mul_zero, add_zero, Int.cast_natCast] at h1 hp hq
  rw [div_self S_pos.ne'] at h1
  exact add_at h1 (add_at (mul_at hM hz hp (varB_at D b g d)) (mul_at hM hz hq (varG_at D b g d)))

theorem midOf_true {h : Hint} {o1 o2 : Option TF} (hm : midOf h o1 o2 = true) :
    ∃ det tr, o1 = some det ∧ o2 = some tr ∧ tr.ok = true ∧ posI (tr.range h.dom) = true ∧
      posI ((TF.mult h.dom h.p h.q).range h.dom) = true ∧
      finalOK h.dom (TF.mul h.dom det (TF.mult h.dom h.p h.q)) h.lam = true := by
  rcases o1 with _ | det <;> rcases o2 with _ | tr
  · change false = true at hm; exact absurd hm Bool.false_ne_true
  · change false = true at hm; exact absurd hm Bool.false_ne_true
  · change false = true at hm; exact absurd hm Bool.false_ne_true
  · unfold midOf at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hm
    exact ⟨det, tr, rfl, rfl, h1, h2, h3, h4⟩

theorem finalOK_ok {D : Dom} {F : TF} {lam : Int} (h : finalOK D F lam = true) : F.ok = true := by
  unfold finalOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

theorem pos_of_mul_pos' {x m : ℝ} (h : 0 < x * m) (hm : 0 < m) : 0 < x := by
  nlinarith

theorem ediv_cast {n m : Int} (hm : (m : ℝ) ≠ 0) (e : Int.ediv n m * m = n) :
    ((Int.ediv n m : Int) : ℝ) = n / m := by
  generalize Int.ediv n m = x at e ⊢
  rw [eq_div_iff hm]; exact_mod_cast e

/-- the box of a hint contains the point -/
theorem boxmem_of {h : Hint} {b al ga : ℝ}
    (hρ : Int.ediv (S : Int) (2 ^ h.rb) * 2 ^ h.rb = S)
    (hw : Int.ediv ((h.wm : Int) * S) (2 ^ h.s) * 2 ^ h.s = h.wm * S)
    (hb : 0 ≤ b) (hb1 : b ≤ 1 / 2 ^ h.rb)
    (hg : |ga - 1| ≤ 1 / 2 ^ h.rb) (hal : |al - h.ac / S| ≤ h.wm / 2 ^ h.s) :
    h.box.mem b al ga := by
  have hS := S_pos
  have eρ : (h.rhoS : ℝ) / S = 1 / 2 ^ h.rb := by
    unfold Hint.rhoS
    rw [ediv_cast (by positivity) hρ]; push_cast; field_simp
  have ew : (h.wS : ℝ) / S = h.wm / 2 ^ h.s := by
    unfold Hint.wS
    rw [ediv_cast (by positivity) hw]; push_cast; field_simp
  rw [abs_le] at hg hal
  change I.mem b (ivS 0 h.rhoS) ∧ I.mem al (ivS (h.ac - h.wS) (h.ac + h.wS)) ∧
    I.mem ga (ivS ((S : Int) - h.rhoS) ((S : Int) + h.rhoS))
  refine ⟨ivS_mem ?_ ?_, ivS_mem ?_ ?_, ivS_mem ?_ ?_⟩
  · rw [Int.cast_zero, zero_div]; exact hb
  · rw [eρ]; exact hb1
  · push_cast; rw [sub_div, ew]; linarith
  · push_cast; rw [add_div, ew]; linarith
  · push_cast; rw [sub_div, eρ, div_self hS.ne']; linarith
  · push_cast; rw [add_div, eρ, div_self hS.ne']; linarith

section staged
variable {s : SHint} {b al ga : ℝ}

/-- the residual of a staged box, by levels -/
theorem staged_P (hv : s.Valid) : @chP _ (tfOps s.h.dom) s.oB s.oA s.oG s.oX = some s.F := by
  rw [← @chPS_eq _ (tfOps s.h.dom)]
  unfold chPS
  rw [hv.cP1, hv.cP2, hv.cP3, hv.cP4]

/-- the inputs of `midY` of a staged box, by levels -/
theorem staged_Y (hv : s.Valid) : @chYInS _ (tfOps s.h.dom) s.oB s.oA s.oG s.oR = s.Y := by
  unfold chYInS
  rw [hv.c1, hv.c2, hv.c3, hv.c4, hv.c5]

/-- `midY` of a staged box, by levels -/
theorem staged_mY (hv : s.Valid) : @midYS _ (tfOps s.h.dom) s.Y = (some s.det, some s.tr) := by
  unfold midYS
  rw [hv.c6, hv.c7, hv.c8]

/-- the test of a staged box at the root, in three steps (one rewrite chain through all levels
gives the kernel needlessly large motives) -/
theorem staged_M (hv : s.Valid) :
    (@chMidN _ (tfOps s.h.dom) s.oB s.oA s.oG s.oR).det = some s.det ∧
      (@chMidN _ (tfOps s.h.dom) s.oB s.oA s.oG s.oR).tr = some s.tr := by
  rw [@chMidN_det_eq _ (tfOps s.h.dom), @chMidN_tr_eq _ (tfOps s.h.dom),
    ← @chYInS_eq _ (tfOps s.h.dom), ← @midYS_eq _ (tfOps s.h.dom), staged_Y hv, staged_mY hv]
  exact ⟨rfl, rfl⟩

theorem staged_cB : ∀ tf, s.oB = some tf → TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) b tf := by
  intro tf htf; obtain rfl := Option.some.inj htf; exact varB_at _ _ _ _

theorem staged_cA : ∀ tf, s.oA = some tf → TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) al tf := by
  intro tf htf; obtain rfl := Option.some.inj htf
  have h0 := cst_at s.h.dom b (ga - 1) (al - s.h.ac / S) [s.h.ac, (S : Int)]
  have e : qev [s.h.ac, (S : Int)] (al - s.h.ac / S) / S = al := by
    have hS := S_pos
    simp only [qev_cons, qev_nil, mul_zero, add_zero, Int.cast_natCast]
    field_simp
    ring
  rwa [e] at h0

theorem staged_cG : ∀ tf, s.oG = some tf → TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) ga tf := by
  intro tf htf; obtain rfl := Option.some.inj htf
  have k1 := cst_at s.h.dom b (ga - 1) (al - s.h.ac / S) [(S : Int)]
  simp only [qev_cons, qev_nil, mul_zero, add_zero, Int.cast_natCast] at k1
  rw [div_self S_pos.ne'] at k1
  have k2 := add_at k1 (varG_at s.h.dom b (ga - 1) (al - s.h.ac / S))
  rwa [add_sub_cancel] at k2

/-- the root polynomial `Ξ` of a staged box encloses... itself, and lies in `XB` -/
theorem staged_cX : ∀ tf, s.oX = some tf → TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S)
    (eev s.h.xi 0 b (ga - 1) (al - s.h.ac / S) / S) tf := by
  intro tf htf; obtain rfl := Option.some.inj htf; exact exact_at s.h.xi

/-- **The root.**  The zero `ξ` of `P̂` in the box is `Ξ - P̂(Ξ)/s`; `rootTF` encloses it. -/
theorem staged_root (hv : s.Valid) (hM : 2 ≤ s.h.M) {xi : ℝ}
    (hz : InBox s.h.dom b (ga - 1) (al - s.h.ac / S)) (hB : s.h.box.mem b al ga)
    (hG : ∀ i, 0 ≤ (chSem.G b al ga xi).get i) (hP : chPR b al ga xi = 0) :
    TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) xi (rootTF s.h s.F s.iS) := by
  have hM1 : 1 ≤ s.h.dom.M := le_trans one_le_two hM
  obtain ⟨hc0, hsl⟩ := hv.c0
  simp only [Bool.and_eq_true] at hc0
  obtain ⟨⟨⟨⟨hloc, hxok⟩, hwin⟩, -⟩, hFz⟩ := hc0
  have hxi := loc_sound hloc hB hG hP
  have cX := staged_cX (s := s) (b := b) (al := al) (ga := ga) s.h.xiTF rfl
  have hXiB := within_mem hwin (enc_range hz cX hxok)
  have hF := @chP_carrier_pt TF (tfOps s.h.dom) _ (opsSoundAt hM1 hz) _ _ _ _ s.oB s.oA s.oG s.oX
    staged_cB staged_cA staged_cG staged_cX
  have hFe : TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S)
      (chPR b al ga (eev s.h.xi 0 b (ga - 1) (al - s.h.ac / S) / S)) s.F := hF s.F (staged_P hv)
  obtain ⟨sl, hs0, hsm, hsr⟩ := slope_rel hsl hB hxi hXiB
  have exi : xi = eev s.h.xi 0 b (ga - 1) (al - s.h.ac / S) / S +
      chPR b al ga (eev s.h.xi 0 b (ga - 1) (al - s.h.ac / S) / S) * (-sl⁻¹) := by
    rw [hP] at hsr
    generalize eev s.h.xi 0 b (ga - 1) (al - s.h.ac / S) / S = Xi at hsr ⊢
    have e1 : chPR b al ga Xi = -(sl * (xi - Xi)) := by linarith
    have e2 : chPR b al ga Xi * sl⁻¹ = -(xi - Xi) := by
      rw [e1, neg_mul, mul_comm sl, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [mul_neg, e2]; ring
  rw [exi]
  exact finish_at (I.mem_neg hsm) hFe hFz (by ring)

end staged

/-- the Taylor forms `s.det`, `s.tr` enclose `det` and `tr` of the test at the root -/
theorem staged_dt {s : SHint} (hv : s.Valid) (hM : 2 ≤ s.h.M) {b al ga xi : ℝ}
    (hz : InBox s.h.dom b (ga - 1) (al - s.h.ac / S))
    (hroot : TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) xi (rootTF s.h s.F s.iS)) :
    TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) (@chMidN ℝ opsReal b al ga xi).det s.det ∧
      TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) (@chMidN ℝ opsReal b al ga xi).tr s.tr := by
  have hM1 : 1 ≤ s.h.dom.M := le_trans one_le_two hM
  obtain ⟨kd, kt⟩ := @chMidN_carrier_pt TF (tfOps s.h.dom) _ (opsSoundAt hM1 hz) _ _ _ _
    s.oB s.oA s.oG s.oR staged_cB staged_cA staged_cG
    (fun tf htf => by obtain rfl := Option.some.inj htf; exact hroot)
  obtain ⟨eD, eT⟩ := staged_M hv
  exact ⟨kd s.det eD, kt s.tr eT⟩

/-- the final tests of a staged box give `0 < X` and `0 < Y` for the values enclosed by `s.det`
and `s.tr` -/
theorem staged_fin {s : SHint} (hv : s.Valid) (hM : 2 ≤ s.h.M) {b al ga X Y : ℝ} (hb : 0 < b)
    (hz : InBox s.h.dom b (ga - 1) (al - s.h.ac / S))
    (hdet : TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) X s.det)
    (htr : TFEncAt s.h.dom b (ga - 1) (al - s.h.ac / S) Y s.tr) : 0 < X ∧ 0 < Y := by
  have hM1 : 1 ≤ s.h.dom.M := le_trans one_le_two hM
  have hM2 : 2 ≤ s.h.dom.M := hM
  obtain ⟨det, tr, hdo, hto, htrok, htrpos, hmpos, hfin⟩ := midOf_true hv.c9
  cases Option.some.inj hdo
  cases Option.some.inj hto
  refine ⟨?_, posI_pos htrpos (enc_range hz htr htrok)⟩
  have hmult := mult_at hM1 hz s.h.p s.h.q
  have hmv := posI_pos hmpos (enc_range hz hmult (mul_ok (finalOK_ok hfin)).2)
  have hr2 : 0 < b ^ 2 + (ga - 1) ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hb 2) (sq_nonneg _)
  exact pos_of_mul_pos' (finalOK_sound hM2 hz (mul_at hM1 hz hdet hmult) hfin hr2) hmv

/-- **One staged box.**  If the certificate conditions of `s` hold, then at every feasible zero of
`P̂` in the box of `s.h` the normalized midpoint test passes. -/
theorem staged_box_sound {s : SHint} (hv : s.Valid) (hM : 2 ≤ s.h.M) {b al ga xi : ℝ}
    (hb : 0 < b) (hz : InBox s.h.dom b (ga - 1) (al - s.h.ac / S)) (hB : s.h.box.mem b al ga)
    (hG : ∀ i, 0 ≤ (chSem.G b al ga xi).get i) (hP : chPR b al ga xi = 0) :
    0 < (@chMidN ℝ opsReal b al ga xi).det ∧ 0 < (@chMidN ℝ opsReal b al ga xi).tr :=
  have hdt := staged_dt hv hM hz (staged_root hv hM hz hB hG hP)
  staged_fin hv hM hb hz hdt.1 hdt.2

/-- one staged box, from real bounds on the point -/
theorem staged_box_cap {s : SHint} (hv : s.Valid) (hM : 2 ≤ s.h.M)
    (hρ : Int.ediv (S : Int) (2 ^ s.h.rb) * 2 ^ s.h.rb = S)
    (hw : Int.ediv ((s.h.wm : Int) * S) (2 ^ s.h.s) * 2 ^ s.h.s = s.h.wm * S)
    {b al ga xi : ℝ} (hb : 0 < b) (hb1 : b ≤ 1 / 2 ^ s.h.rb) (hg : |ga - 1| ≤ 1 / 2 ^ s.h.rb)
    (hal : |al - s.h.ac / S| ≤ s.h.wm / 2 ^ s.h.s)
    (hC : InC (1 + b * al) b (b * ga) (1 / 2 + b * xi)) (hP : chPR b al ga xi = 0) :
    0 < (@chMidN ℝ opsReal b al ga xi).det ∧ 0 < (@chMidN ℝ opsReal b al ga xi).tr :=
  staged_box_sound hv hM hb ⟨hb.le, hb1, hg, hal⟩ (boxmem_of hρ hw hb.le hb1 hg hal)
    (chG_nonneg hb hC) hP

end box

/-! ## the corner theorem -/

theorem ac_val {a n m : Int} {v : ℝ} (hv : (n : ℝ) / m = v) (hm : (m : ℝ) ≠ 0)
    (e : a * m = n * (S : Int)) : (a : ℝ) / S = v := by
  have e' : (a : ℝ) * m = n * S := by exact_mod_cast e
  rw [← hv, div_eq_div_iff S_pos.ne' hm]; exact e'

end

end CTF
end C4
