module

public import C4.SearchSound
public import C4.ModeSound2
public import C4.TFCommon

@[expose] public section

/-!
# Soundness of the sheared replay

`checkBoxH2_sound`: if `checkBoxH2 M fuel B h` succeeds, then over `B` every feasible zero of `P`
(all `g_i ≥ 0`, `P = 0`, and `|x| ≤ 1` if the mode clamps) passes the midpoint test
(`det T > 0` and `tr T > 0` for some shift), or lies in the corner disc of the mode.

The localisation is that of the first-order checker (`xrange_sound`, `locH_sound` on `Mode2.toMode`).  A sheared leaf works
in the coordinates `(z, w)`, `x = x₀(z) + w`: the jet of `x` is `shearJ` (`shearJ_enc`), so the
mode's jets enclose `g`, `P` and the outputs as functions of `(z, w)`; the first-order checker's
`pstepP_sound` then gives the Newton steps, and the ranges of the output jets give the test.  As in
the replay of `C4Check.Search`, every test is
decided with `sel_pos`/`sel_neg` on its (free) condition, never by evaluating it.
-/

namespace C4

noncomputable section

set_option exponentiation.threshold 1024

variable {M : Mode2} {Sm : Sem2}

/-! ## the statement -/

/-- `(b, ·, ga)` lies in the corner disc of `M` -/
def InDisc (M : Mode2) (b ga : ℝ) : Prop :=
  ∃ k, M.disc = some k ∧ 0 ≤ b ∧ b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 4 : ℝ) ^ k

/-- the normalized midpoint test holds at `(z, x)` -/
def TestOK (Sm : Sem2) (z0 z1 z2 x : ℝ) : Prop :=
  0 < (Sm.out z0 z1 z2 x).det ∧ 0 < (Sm.out z0 z1 z2 x).tr

/-- over `B`, every feasible zero of `P` passes the test or lies in the corner disc -/
def AllGood2 (M : Mode2) (Sm : Sem2) (B : Box) : Prop :=
  ∀ z0 z1 z2 x, B.mem z0 z1 z2 → (M.clamp = true → -1 ≤ x ∧ x ≤ 1) →
    (∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) → Sm.P z0 z1 z2 x = 0 →
    TestOK Sm z0 z1 z2 x ∨ InDisc M z0 z2

/-! ## the shear -/

/-- `x₀(z) + w` in the coordinates `(z, w)` of a 4-box with centre `zc` -/
def shearF (zc : P4) (sh : Shear) (z : P4) : ℝ :=
  val sh.X0 + (val sh.J0 * (z 0 - zc 0) + val sh.J1 * (z 1 - zc 1) + val sh.J2 * (z 2 - zc 2)) +
  ((z 0 - zc 0) * (val sh.H00 * (z 0 - zc 0) + val sh.H01 * (z 1 - zc 1) +
      val sh.H02 * (z 2 - zc 2)) +
    (z 1 - zc 1) * (val sh.H11 * (z 1 - zc 1) + val sh.H12 * (z 2 - zc 2)) +
    val sh.H22 * (z 2 - zc 2) ^ 2) + z 3

/-- the slopes of `shearF` at `z` -/
def shSl (zc : P4) (sh : Shear) (z : P4) : Fin 4 → ℝ
  | 0 => val sh.J0 + (val sh.H00 * (z 0 - zc 0) + val sh.H01 * (z 1 - zc 1) +
      val sh.H02 * (z 2 - zc 2))
  | 1 => val sh.J1 + (val sh.H11 * (z 1 - zc 1) + val sh.H12 * (z 2 - zc 2))
  | 2 => val sh.J2 + val sh.H22 * (z 2 - zc 2)
  | 3 => 1

theorem shearJ_enc {S : Set P4} {zc : P4} {R : Rad} (hR : RadOK S zc R) (sh : Shear)
    {W : I} (hc : zc 3 = val (I.ctr W)) :
    JEnc S zc (shearF zc sh) (shearJ R sh W) := by
  have hC : I.mem (val sh.X0 + val (I.ctr W)) ((I.pt sh.X0).add (I.pt (I.ctr W))) :=
    I.mem_add (I.mem_pt sh.X0) (I.mem_pt _)
  have he : ∀ z : P4, shearF zc sh z =
      val sh.X0 + val (I.ctr W) + ∑ i, shSl zc sh z i * (z i - zc i) := by
    intro z
    rw [Fin.sum_univ_four]
    simp only [shearF, shSl, hc]
    ring
  have hs : ∀ z ∈ S, I.mem (shSl zc sh z 0) (widen (I.pt sh.J0)
        (Nat.add (Nat.add (I.eterm (I.pt sh.H00) R.r0) (I.eterm (I.pt sh.H01) R.r1))
          (I.eterm (I.pt sh.H02) R.r2))) ∧
      I.mem (shSl zc sh z 1) (widen (I.pt sh.J1)
        (Nat.add (I.eterm (I.pt sh.H11) R.r1) (I.eterm (I.pt sh.H12) R.r2))) ∧
      I.mem (shSl zc sh z 2) (widen (I.pt sh.J2) (I.eterm (I.pt sh.H22) R.r2)) := by
    intro z hz
    obtain ⟨r0, r1, r2, -⟩ := hR z hz
    have e00 := I.eterm_ge (I.mem_pt sh.H00) r0
    have e01 := I.eterm_ge (I.mem_pt sh.H01) r1
    have e02 := I.eterm_ge (I.mem_pt sh.H02) r2
    have e11 := I.eterm_ge (I.mem_pt sh.H11) r1
    have e12 := I.eterm_ge (I.mem_pt sh.H12) r2
    have e22 := I.eterm_ge (I.mem_pt sh.H22) r2
    refine ⟨I.mem_widen (I.mem_pt sh.J0) ?_, I.mem_widen (I.mem_pt sh.J1) ?_,
      I.mem_widen (I.mem_pt sh.J2) ?_⟩
    · rw [cast_add, cast_add, add_div, add_div]
      calc |val sh.H00 * (z 0 - zc 0) + val sh.H01 * (z 1 - zc 1) + val sh.H02 * (z 2 - zc 2)|
          ≤ |val sh.H00 * (z 0 - zc 0)| + |val sh.H01 * (z 1 - zc 1)| +
            |val sh.H02 * (z 2 - zc 2)| := abs_add_three _ _ _
        _ ≤ _ := by gcongr
    · rw [cast_add, add_div]
      calc |val sh.H11 * (z 1 - zc 1) + val sh.H12 * (z 2 - zc 2)|
          ≤ |val sh.H11 * (z 1 - zc 1)| + |val sh.H12 * (z 2 - zc 2)| := abs_add_le _ _
        _ ≤ _ := by gcongr
    · exact e22
  refine ⟨fun z hz => ?_, ?_, fun z hz => ⟨shSl zc sh z, ?_, ?_⟩⟩
  · obtain ⟨h0, h1, h2⟩ := hs z hz
    rw [he z]
    exact cf_mem hR hz hC _ h0 h1 h2 I.mem_one
  · change I.mem (shearF zc sh zc) ((I.pt sh.X0).add (I.pt (I.ctr W)))
    have e : shearF zc sh zc = val sh.X0 + val (I.ctr W) := by
      simp only [shearF, sub_self, mul_zero, add_zero, hc]
      ring
    rw [e]
    exact hC
  · obtain ⟨h0, h1, h2⟩ := hs z hz
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact I.mem_one
  · rw [he z, he zc]
    have : ∑ i, shSl zc sh zc i * (zc i - zc i) = 0 := by simp
    rw [this]
    ring

theorem x0range_mem (B : Box) (sh : Shear) {z0 z1 z2 : ℝ} (hz : B.mem z0 z1 z2) :
    I.mem (xS sh B z0 z1 z2) (x0range B sh) := by
  have hp : pt4 z0 z1 z2 0 ∈ box4 B I.zero := pt4_mem hz I.mem_zero
  have h := (shearJ_enc (rad_ok B I.zero) sh (W := I.zero) rfl).1 _ hp
  have e : shearF (ctr4 B I.zero) sh (pt4 z0 z1 z2 0) = xS sh B z0 z1 z2 := by
    change val sh.X0 + (val sh.J0 * (z0 - val (I.ctr B.X0)) + val sh.J1 * (z1 - val (I.ctr B.X1)) +
      val sh.J2 * (z2 - val (I.ctr B.X2))) +
      ((z0 - val (I.ctr B.X0)) * (val sh.H00 * (z0 - val (I.ctr B.X0)) +
          val sh.H01 * (z1 - val (I.ctr B.X1)) + val sh.H02 * (z2 - val (I.ctr B.X2))) +
        (z1 - val (I.ctr B.X1)) * (val sh.H11 * (z1 - val (I.ctr B.X1)) +
          val sh.H12 * (z2 - val (I.ctr B.X2))) +
        val sh.H22 * (z2 - val (I.ctr B.X2)) ^ 2) + 0 = _
    rw [add_zero]
    rfl
  rw [e] at h
  exact h

/-- the point `(z, w)` with `x = x₀(z) + w` -/
theorem shearF_pt (B : Box) (W : I) (sh : Shear) (z0 z1 z2 x : ℝ) :
    shearF (ctr4 B W) sh (pt4 z0 z1 z2 (x - xS sh B z0 z1 z2)) = x := by
  change val sh.X0 + (val sh.J0 * (z0 - val (I.ctr B.X0)) + val sh.J1 * (z1 - val (I.ctr B.X1)) +
      val sh.J2 * (z2 - val (I.ctr B.X2))) +
      ((z0 - val (I.ctr B.X0)) * (val sh.H00 * (z0 - val (I.ctr B.X0)) +
          val sh.H01 * (z1 - val (I.ctr B.X1)) + val sh.H02 * (z2 - val (I.ctr B.X2))) +
        (z1 - val (I.ctr B.X1)) * (val sh.H11 * (z1 - val (I.ctr B.X1)) +
          val sh.H12 * (z2 - val (I.ctr B.X2))) +
        val sh.H22 * (z2 - val (I.ctr B.X2)) ^ 2) + (x - xS sh B z0 z1 z2) = x
  simp only [xS]
  ring

/-- a function of `(z, x₀(z) + w)` at the point `(z, x - x₀(z))` -/
theorem val_at {F : ℝ → ℝ → ℝ → ℝ → ℝ} (B : Box) (W : I) (sh : Shear) (z0 z1 z2 x : ℝ) :
    (fun z : P4 => F (z 0) (z 1) (z 2) (shearF (ctr4 B W) sh z))
      (pt4 z0 z1 z2 (x - xS sh B z0 z1 z2)) = F z0 z1 z2 x := by
  change F z0 z1 z2 (shearF (ctr4 B W) sh (pt4 z0 z1 z2 (x - xS sh B z0 z1 z2))) = F z0 z1 z2 x
  rw [shearF_pt]

/-- the range of a jet of `F(z, x₀(z) + w)` on `B × W` holds the value at `(z, x)`, if
`x - x₀(z) ∈ W` -/
theorem range_at {F : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box} {W : I} {sh : Shear} {j : J}
    (hj : JEnc (box4 B W) (ctr4 B W) (fun z => F (z 0) (z 1) (z 2) (shearF (ctr4 B W) sh z)) j)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hw : I.mem (x - xS sh B z0 z1 z2) W) :
    I.mem (F z0 z1 z2 x) (J.range (rad B W) j) := by
  rw [← val_at (F := F) B W sh z0 z1 z2 x]
  exact JEnc.range (rad_ok B W) hj (pt4_mem hz hw)

/-! ## the Newton steps -/

theorem snewton_sound (hM : ModeSound2 M Sm) {B : Box} (sh : Shear) {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0) :
    ∀ (k : Nat) (W E : I), snewton M B sh k W = some E →
      I.mem (x - xS sh B z0 z1 z2) W → I.mem (x - xS sh B z0 z1 z2) E := by
  intro k
  induction k with
  | zero =>
    intro W E h hW
    rw [snewton] at h
    obtain rfl := Option.some.inj h
    exact hW
  | succ k ih =>
    intro W E h hW
    rw [snewton] at h
    obtain ⟨W', hW', hE⟩ := Option.bind_eq_some_iff.mp h
    refine ih W' E hE ?_
    -- one step on `B × W` in the coordinates `(z, w)`
    obtain ⟨e0, e1, e2, -⟩ := jv_enc B W
    have eS := shearJ_enc (rad_ok B W) sh (W := W) rfl
    obtain ⟨hgG, hgP⟩ := hM.gP (box4 B W) (ctr4 B W) (rad B W) (rad_ok B W) _ _ _ _ _ _ _ _
      e0 e1 e2 eS
    rw [sgP, pstepG] at hW'
    by_cases cg : gNeg (rad B W) (M.gP (rad B W) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2)
        (shearJ (rad B W) sh W)).1 = true
    · obtain ⟨i, j, hj, hH⟩ := gNeg_true cg
      have hneg := I.neg_of_mem (range_at (F := fun a b c d => (Sm.G a b c d).get i)
        (hgG i j hj) hz hW) hH
      exact absurd hneg (not_lt.mpr (hG i))
    · rw [sel_neg _ _ cg] at hW'
      exact pstepP_sound (rad_ok B W) hgP rfl hW' (pt4_mem hz hW) hW
        ((val_at (F := fun a b c d => Sm.P a b c d) B W sh z0 z1 z2 x).trans hP)

/-! ## the built-in evaluator -/

theorem posL_true {A : I} (h : posL A = true) : ¬Nat.ble Bb A.L = true := fun hb => by
  rw [posL, sel_pos _ _ hb] at h
  cases h

theorem posJ_true {R : Rad} {o : Option J} (h : posJ R o = true) :
    ∃ j, o = some j ∧ ¬Nat.ble Bb (J.range R j).L = true := by
  cases o with
  | none => cases h
  | some j => exact ⟨j, rfl, posL_true h⟩

theorem both_true {a b : Bool} (h : both a b = true) : a = true ∧ b = true := by
  cases a
  · cases h
  · exact ⟨rfl, h⟩

theorem ifNE_true {E : I} {t : Bool} (h : ifNE E t = true) (hne : ¬I.isEmpty E = true) :
    t = true := by
  rw [ifNE, Bool.eq_false_iff.mpr hne] at h
  exact h

theorem cont_some {b : Bool} {r : Option Nat} {h' : Nat} (h : cont b r = some h') :
    b = true ∧ r = some h' := by
  cases b
  · cases h
  · exact ⟨rfl, h⟩

theorem gsel_some {g : Six (Option J)} {f : Nat} {j : J} (h : gsel g f = some j) :
    ∃ i, g.get i = some j := by
  unfold gsel at h
  by_cases c0 : Nat.beq f 0 = true
  · rw [sel_pos _ _ c0] at h; exact ⟨0, h⟩
  rw [sel_neg _ _ c0] at h
  by_cases c1 : Nat.beq f 1 = true
  · rw [sel_pos _ _ c1] at h; exact ⟨1, h⟩
  rw [sel_neg _ _ c1] at h
  by_cases c2 : Nat.beq f 2 = true
  · rw [sel_pos _ _ c2] at h; exact ⟨2, h⟩
  rw [sel_neg _ _ c2] at h
  by_cases c3 : Nat.beq f 3 = true
  · rw [sel_pos _ _ c3] at h; exact ⟨3, h⟩
  rw [sel_neg _ _ c3] at h
  by_cases c4 : Nat.beq f 4 = true
  · rw [sel_pos _ _ c4] at h; exact ⟨4, h⟩
  rw [sel_neg _ _ c4] at h
  by_cases c5 : Nat.beq f 5 = true
  · rw [sel_pos _ _ c5] at h; exact ⟨5, h⟩
  rw [sel_neg _ _ c5] at h
  cases h

theorem subMu_some {R : Rad} {mu : Nat} {d g : Option J} {j : J} (h : subMu R mu d g = some j) :
    ∃ dj gj, d = some dj ∧ g = some gj ∧ j = dj.sub (J.mul R (J.cst (I.pt mu)) gj) := by
  cases d with
  | none => cases h
  | some dj =>
    cases g with
    | none => cases h
    | some gj => exact ⟨dj, gj, rfl, rfl, (Option.some.inj h).symm⟩

/-- the jet test on `B × E`, for a feasible point whose `w` is in `E` -/
theorem stest_sound (hM : ModeSound2 M Sm) {B : Box} {sh : Shear} {mf f mu : Nat}
    (hmu : 0 ≤ val mu) {E : I} (h : stest (rad B E) mf f mu (sout M B sh E) = true)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i)
    (hw : I.mem (x - xS sh B z0 z1 z2) E) : TestOK Sm z0 z1 z2 x := by
  obtain ⟨e0, e1, e2, -⟩ := jv_enc B E
  have eS := shearJ_enc (rad_ok B E) sh (W := E) rfl
  obtain ⟨hdet, htr, hg⟩ := hM.outJ (box4 B E) (ctr4 B E) (rad B E) (rad_ok B E)
    _ _ _ _ _ _ _ _ e0 e1 e2 eS
  rw [stest] at h
  obtain ⟨h1, h2⟩ := both_true h
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj, hL⟩ := posJ_true h1
    by_cases cm : Nat.beq mf 0 = true
    · rw [sel_pos _ _ cm] at hj
      exact I.pos_of_mem (range_at (F := fun a b c d => (Sm.out a b c d).det)
        (hdet j hj) hz hw) hL
    · rw [sel_neg _ _ cm] at hj
      obtain ⟨d, gj, hd, hgs, rfl⟩ := subMu_some hj
      obtain ⟨i, hi⟩ := gsel_some hgs
      have henc := JEnc.sub (hdet d hd)
        (JEnc.mul (rad_ok B E) (JEnc.cst (S := box4 B E) (zc := ctr4 B E) (I.mem_pt mu))
          (hg i gj hi))
      have hpos := I.pos_of_mem (range_at (F := fun a b c d =>
        (Sm.out a b c d).det - val mu * (Sm.out a b c d).g.get i) henc hz hw) hL
      rw [hM.out_g] at hpos
      have := mul_nonneg hmu (hG i)
      linarith
  · obtain ⟨j, hj, hL⟩ := posJ_true h2
    exact I.pos_of_mem (range_at (F := fun a b c d => (Sm.out a b c d).tr)
      (htr j hj) hz hw) hL

theorem stestE_sound (hM : ModeSound2 M Sm) {B : Box} {sh : Shear} {mf f mu : Nat}
    (hmu : 0 ≤ val mu) {o : Option I} (h : stestE M B sh mf f mu o = true) {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i)
    (hE : ∀ E, o = some E → I.mem (x - xS sh B z0 z1 z2) E) :
    TestOK Sm z0 z1 z2 x := by
  cases o with
  | none => cases h
  | some E =>
    have hw := hE E rfl
    have hne : ¬I.isEmpty E = true := fun ce => I.not_mem_of_isEmpty ce hw
    exact stest_sound hM hmu (ifNE_true h hne) hz hG hw

theorem val_muDec (m : Nat) : 0 ≤ val (muDec m) :=
  le_of_le_of_eq (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))
    (val_addB' (Nat.shiftLeft m 72)).symm

/-- the built-in evaluator is sound -/
theorem evJ1_sound (hM : ModeSound2 M Sm) {B : Box} {sh : Shear} {fl : Nat} {W : I}
    (h : evJ1 M B sh fl W = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0)
    (hw : I.mem (x - xS sh B z0 z1 z2) W) : TestOK Sm z0 z1 z2 x :=
  stestE_sound hM (val_muDec _) h hz hG fun E hE =>
    snewton_sound hM sh hz hG hP (Nat.land fl 3) W E hE hw

theorem sleafF_sound (hM : ModeSound2 M Sm) {B : Box} {Y : I} {sh : Shear} {ev fl : Nat}
    (h : sleafF M B Y sh ev fl = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hcl : M.clamp = true → -1 ≤ x ∧ x ≤ 1) (hxY : I.mem x Y)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0) :
    TestOK Sm z0 z1 z2 x := by
  have hw := I.mem_sub hxY (x0range_mem B sh hz)
  rw [sleafF] at h
  by_cases ce : Nat.beq ev 0 = true
  · rw [sel_pos _ _ ce] at h
    exact evJ1_sound hM h hz hG hP hw
  · rw [sel_neg _ _ ce] at h
    exact hM.ev2 B sh fl _ h z0 z1 z2 x hz hcl hG hP hw

theorem sleafH_sound (hM : ModeSound2 M Sm) {B : Box} {Y : I} {h : Nat}
    (hl : sleafH M B Y h = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hcl : M.clamp = true → -1 ≤ x ∧ x ≤ 1) (hxY : I.mem x Y)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0) :
    TestOK Sm z0 z1 z2 x :=
  sleafF_sound hM hl hz hcl hxY hG hP

theorem sAllH_sound (hM : ModeSound2 M Sm) {B : Box} {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hcl : M.clamp = true → -1 ≤ x ∧ x ≤ 1)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0) :
    ∀ (Ys : List I) (h h' : Nat), sAllH M B Ys h = some h' → ∀ Y ∈ Ys, I.mem x Y →
      TestOK Sm z0 z1 z2 x
  | [], _, _, _, _, hY, _ => absurd hY List.not_mem_nil
  | Y :: rest, h, h', hc, Y', hY', hx => by
    obtain ⟨c, hc'⟩ := cont_some hc
    rcases List.mem_cons.mp hY' with rfl | hY''
    · exact sleafH_sound hM c hz hcl hx hG hP
    · exact sAllH_sound hM hz hcl hG hP rest _ _ hc' Y' hY'' hx

/-! ## the corner disc -/

theorem adiff_ge (X Y : Nat) : (X : ℝ) - Y ≤ (adiff X Y : ℝ) := by
  have h1 := sub_le_cast X Y
  have h2 : (0 : ℝ) ≤ ((Nat.sub Y X : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [adiff, cast_add]
  linarith

theorem two_pow_disc {k : Nat} (hk : k ≤ 96) :
    (2 : ℝ) ^ (Nat.sub 192 (Nat.add k k)) * 4 ^ k = 2 ^ 192 := by
  have e : Nat.sub 192 (Nat.add k k) + 2 * k = 192 := by
    change 192 - (k + k) + 2 * k = 192
    omega
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, e]

theorem discOK_sound {k : Nat} {B : Box} (h : discOK k B = true) {z0 z1 z2 : ℝ}
    (hz : B.mem z0 z1 z2) : 0 ≤ z0 ∧ z0 ^ 2 + (z2 - 1) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
  obtain ⟨⟨hb1, hb2⟩, -, ⟨hg1, hg2⟩⟩ := hz
  unfold discOK at h
  by_cases c1 : Nat.ble B.X0.L Bb = true
  swap
  · rw [sel_neg _ _ c1] at h; cases h
  rw [sel_pos _ _ c1] at h
  by_cases c2 : Nat.ble k 96 = true
  swap
  · rw [sel_neg _ _ c2] at h; cases h
  rw [sel_pos _ _ c2] at h
  have hk : k ≤ 96 := ble_true c2
  have hQ := ble_true h
  have hz0 : 0 ≤ z0 := by
    have := val_nonpos_of_ble c1
    linarith
  refine ⟨hz0, ?_⟩
  -- the three bounds, as offsets over `2^96`
  set bh := Nat.sub B.X0.H Bb with hbh_def
  set g1 := adiff B.X2.H (Nat.add Bb ONE) with hg1_def
  set g2 := adiff (Nat.add B.X2.L ONE) Bb with hg2_def
  set gm := I.mx g1 g2 with hgm_def
  have h96 : (0 : ℝ) < 2 ^ 96 := by positivity
  have hbh : z0 ≤ (bh : ℝ) / 2 ^ 96 := by
    have := sub_le_cast B.X0.H Bb
    rw [cBb] at this
    calc z0 ≤ val B.X0.H := hb2
      _ ≤ (bh : ℝ) / 2 ^ 96 := by unfold val; gcongr
  have hgm1 : (g1 : ℝ) ≤ gm := by rw [hgm_def, mx_eq]; exact_mod_cast le_max_left _ _
  have hgm2 : (g2 : ℝ) ≤ gm := by rw [hgm_def, mx_eq]; exact_mod_cast le_max_right _ _
  have hu : z2 - 1 ≤ (gm : ℝ) / 2 ^ 96 := by
    have := adiff_ge B.X2.H (Nat.add Bb ONE)
    rw [cast_add, cBb, cONE] at this
    have e : val B.X2.H - 1 = ((B.X2.H : ℝ) - (2 ^ 256 + 2 ^ 96)) / 2 ^ 96 := by
      unfold val; field_simp; ring
    have : val B.X2.H - 1 ≤ (g1 : ℝ) / 2 ^ 96 := by rw [e]; gcongr
    have : (g1 : ℝ) / 2 ^ 96 ≤ (gm : ℝ) / 2 ^ 96 := by gcongr
    linarith
  have hl : 1 - z2 ≤ (gm : ℝ) / 2 ^ 96 := by
    have := adiff_ge (Nat.add B.X2.L ONE) Bb
    rw [cast_add, cBb, cONE] at this
    have e : val B.X2.L + 1 = ((B.X2.L : ℝ) + 2 ^ 96 - 2 ^ 256) / 2 ^ 96 := by
      unfold val; field_simp; ring
    have : val B.X2.L + 1 ≤ (g2 : ℝ) / 2 ^ 96 := by rw [e]; gcongr
    have : (g2 : ℝ) / 2 ^ 96 ≤ (gm : ℝ) / 2 ^ 96 := by gcongr
    linarith
  have hsq1 : z0 ^ 2 ≤ ((bh : ℝ) / 2 ^ 96) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hbh hbh hz0 (le_trans hz0 hbh)
  have hsq2 : (z2 - 1) ^ 2 ≤ ((gm : ℝ) / 2 ^ 96) ^ 2 := sq_le_sq' (by linarith) hu
  have hQr : (bh : ℝ) * bh + (gm : ℝ) * gm ≤
      ((Nat.shiftLeft 1 (Nat.sub 192 (Nat.add k k)) : ℕ) : ℝ) := by
    exact_mod_cast hQ
  rw [cast_shl, Nat.cast_one, one_mul] at hQr
  have hpow := two_pow_disc hk
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  -- `(bh² + gm²) / 2^192 ≤ 2^(192 - 2k) / 2^192 = 4^-k`
  have hfin : ((bh : ℝ) / 2 ^ 96) ^ 2 + ((gm : ℝ) / 2 ^ 96) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
    have e1 : ((bh : ℝ) / 2 ^ 96) ^ 2 + ((gm : ℝ) / 2 ^ 96) ^ 2 =
        ((bh : ℝ) * bh + (gm : ℝ) * gm) / 2 ^ 192 := by
      field_simp
    have e2 : (1 / 4 : ℝ) ^ k = (2 : ℝ) ^ (Nat.sub 192 (Nat.add k k)) / 2 ^ 192 := by
      rw [← hpow, one_div_pow]
      field_simp
    rw [e1, e2]
    gcongr
  linarith

theorem discLeaf_sound {B : Box} {h h' : Nat} {o : Option Nat} (hl : discLeaf B h o = some h')
    {z0 z1 z2 : ℝ} (hz : B.mem z0 z1 z2) :
    ∃ k, o = some k ∧ 0 ≤ z0 ∧ z0 ^ 2 + (z2 - 1) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
  cases o with
  | none => cases hl
  | some k => exact ⟨k, rfl, discOK_sound (cont_some hl).1 hz⟩

/-! ## the recursion -/

theorem leafH2_sound (hM : ModeSound2 M Sm) {B : Box} {h h' : Nat} (hl : leafH2 M B h = some h')
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hcl : M.clamp = true → -1 ≤ x ∧ x ≤ 1)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) (hP : Sm.P z0 z1 z2 x = 0) :
    TestOK Sm z0 z1 z2 x := by
  have hM3 := hM.toModeSound
  rw [leafH2] at hl
  obtain ⟨X, hX, hl'⟩ := Option.bind_eq_some_iff.mp hl
  have hxX := xrange_sound (Sm := Sm.toSem) hM3 hX hz hcl hG
  by_cases ce : I.isEmpty X = true
  · exact absurd hxX (I.not_mem_of_isEmpty ce)
  · rw [sel_neg _ _ ce] at hl'
    obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.mp hl'
    obtain ⟨Y, hY, hxY⟩ := locH_sound (Sm := Sm.toSem) hM3 hz ⟨hG, hP⟩ 4096 h [X] [] r hr
      (Or.inl ⟨X, List.mem_singleton_self X, hxX⟩)
    exact sAllH_sound hM hz hcl hG hP r.1 r.2 h' hc Y hY hxY

theorem checkBoxH2_sound (hM : ModeSound2 M Sm) :
    ∀ (fuel : Nat) (B : Box) (h h' : Nat), checkBoxH2 M fuel B h = some h' → AllGood2 M Sm B
  | 0, B, h, h', hc => by
    rw [checkBoxH2] at hc
    cases hc
  | fuel + 1, B, h, h', hc => by
    rw [checkBoxH2] at hc
    by_cases c : Nat.beq (Nat.land h 3) 0 = true
    · rw [sel_pos _ _ c] at hc
      intro z0 z1 z2 x hz hcl hG hP
      by_cases c' : Nat.beq (Nat.land (Nat.shiftRight h 2) 1) 0 = true
      · rw [sel_pos _ _ c'] at hc
        exact Or.inl (leafH2_sound hM hc hz hcl hG hP)
      · rw [sel_neg _ _ c'] at hc
        exact Or.inr (discLeaf_sound hc hz)
    · rw [sel_neg _ _ c] at hc
      obtain ⟨h1, hc1, hc2⟩ := Option.bind_eq_some_iff.mp hc
      have g1 := checkBoxH2_sound hM fuel _ _ _ hc1
      have g2 := checkBoxH2_sound hM fuel _ _ _ hc2
      intro z0 z1 z2 x hz hcl hG hP
      rcases splitBox_mem (Nat.land h 3) hz with hz' | hz'
      · exact g1 z0 z1 z2 x hz' hcl hG hP
      · exact g2 z0 z1 z2 x hz' hcl hG hP

/-- a certified box is good -/
theorem Certified2.good (hM : ModeSound2 M Sm) {B : Box} (h : Certified2 M B) :
    AllGood2 M Sm B := by
  induction h with
  | leaf h hc =>
    obtain ⟨h', hh⟩ := Option.isSome_iff_exists.mp hc
    exact checkBoxH2_sound hM depth _ h h' hh
  | split s _ _ g1 g2 =>
    intro z0 z1 z2 x hz hcl hG hP
    rcases splitBox_mem s hz with hz' | hz'
    · exact g1 z0 z1 z2 x hz' hcl hG hP
    · exact g2 z0 z1 z2 x hz' hcl hG hP

/-! ## the Taylor-model leaf

`TFSoundK K Enc` collects what the Taylor-model leaf needs from a model type of `C4Check.TF` (the
lemmas of `C4/TFSound.lean`).  A point `t ∈ [-1, 1]⁴` of a model is the point
`z_i = z̄_i + r_i t_i`, `x = x₀(z) + e t₃` of the box and the band, so the models of `P` and of
the test enclose them there (`tfAt_*`), and the root and test phases are sound (`tfRoot_sound`,
`tfTest_sound`).  Given the four model types (`TFKits`), `dirModeTF` and `chModeTF k` are sound
(`dirModeTF_sound`, `chModeTF_sound`). -/

section TFLeaf

variable {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop}

/-- what the soundness of the Taylor-model leaf needs from a model type -/
structure TFSoundK (K : TFKit T) (Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop) : Prop where
  ops : OpsSound (Fin 4 → ℝ) T Enc
  var0 : ∀ x r : ℕ, Enc (fun t => val x + (r : ℝ) / 2 ^ 96 * t 0) (K.var0 x r)
  var1 : ∀ x r : ℕ, Enc (fun t => val x + (r : ℝ) / 2 ^ 96 * t 1) (K.var1 x r)
  var2 : ∀ x r : ℕ, Enc (fun t => val x + (r : ℝ) / 2 ^ 96 * t 2) (K.var2 x r)
  var3 : ∀ x r : ℕ, Enc (fun t => val x + (r : ℝ) / 2 ^ 96 * t 3) (K.var3 x r)
  ptB : ∀ x : ℕ, Enc (fun _ => val x) (K.ptB x)
  posT : ∀ (f : (Fin 4 → ℝ) → ℝ) (o : Option T), OEncG Enc f o → K.posT o = true →
    ∀ t : Fin 4 → ℝ, (∀ i, |t i| ≤ 1) → 0 < f t
  newtOK : ∀ (f : (Fin 4 → ℝ) → ℝ) (o : Option T) (rho : ℕ), OEncG Enc f o →
    K.newtOK rho o = true → ∀ t : Fin 4 → ℝ, (∀ i, |t i| ≤ 1) → f t = 0 →
    |t 3| ≤ (rho : ℝ) / 2 ^ 96

/-- the coordinate `z̄₀ + r₀ t₀` of the model box -/
def tz0 (B : Box) (t : Fin 4 → ℝ) : ℝ :=
  val (I.ctr B.X0) + (I.radAt B.X0 (I.ctr B.X0) : ℝ) / 2 ^ 96 * t 0
/-- the coordinate `z̄₁ + r₁ t₁` of the model box -/
def tz1 (B : Box) (t : Fin 4 → ℝ) : ℝ :=
  val (I.ctr B.X1) + (I.radAt B.X1 (I.ctr B.X1) : ℝ) / 2 ^ 96 * t 1
/-- the coordinate `z̄₂ + r₂ t₂` of the model box -/
def tz2 (B : Box) (t : Fin 4 → ℝ) : ℝ :=
  val (I.ctr B.X2) + (I.radAt B.X2 (I.ctr B.X2) : ℝ) / 2 ^ 96 * t 2
/-- the dependent coordinate `x₀(z(t)) + e t₃` of the model box, as `shearX` computes it -/
def tx (B : Box) (sh : Shear) (e : ℕ) (t : Fin 4 → ℝ) : ℝ :=
  @shearX ℝ opsReal (val sh.X0) (val sh.J0) (val sh.J1) (val sh.J2) (val sh.H00) (val sh.H01)
    (val sh.H02) (val sh.H11) (val sh.H12) (val sh.H22)
    (val Bb + (I.radAt B.X0 (I.ctr B.X0) : ℝ) / 2 ^ 96 * t 0)
    (val Bb + (I.radAt B.X1 (I.ctr B.X1) : ℝ) / 2 ^ 96 * t 1)
    (val Bb + (I.radAt B.X2 (I.ctr B.X2) : ℝ) / 2 ^ 96 * t 2) (val Bb + (e : ℝ) / 2 ^ 96 * t 3)

/-- the carriers of the model box: the coordinates -/
def cz (S : TFSoundK K Enc) (B : Box) : Carrier (Fin 4 → ℝ) T Enc × Carrier (Fin 4 → ℝ) T Enc ×
    Carrier (Fin 4 → ℝ) T Enc :=
  (Carrier.of (S.var0 (I.ctr B.X0) (I.radAt B.X0 (I.ctr B.X0))),
    Carrier.of (S.var1 (I.ctr B.X1) (I.radAt B.X1 (I.ctr B.X1))),
    Carrier.of (S.var2 (I.ctr B.X2) (I.radAt B.X2 (I.ctr B.X2))))

/-- the carrier of the model box: the dependent coordinate -/
def cx (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) : Carrier (Fin 4 → ℝ) T Enc :=
  @shearX _ (carrierOps S.ops) (Carrier.of (S.ptB sh.X0)) (Carrier.of (S.ptB sh.J0))
    (Carrier.of (S.ptB sh.J1)) (Carrier.of (S.ptB sh.J2)) (Carrier.of (S.ptB sh.H00))
    (Carrier.of (S.ptB sh.H01)) (Carrier.of (S.ptB sh.H02)) (Carrier.of (S.ptB sh.H11))
    (Carrier.of (S.ptB sh.H12)) (Carrier.of (S.ptB sh.H22))
    (Carrier.of (S.var0 Bb (I.radAt B.X0 (I.ctr B.X0))))
    (Carrier.of (S.var1 Bb (I.radAt B.X1 (I.ctr B.X1))))
    (Carrier.of (S.var2 Bb (I.radAt B.X2 (I.ctr B.X2)))) (Carrier.of (S.var3 Bb e))

/-- the carrier evaluation of `midY` encloses the real one (first output) -/
theorem YIn_Y1_tf (S : TFSoundK K Enc) (A : YIn (Carrier (Fin 4 → ℝ) T Enc)) :
    OEncG Enc (fun t => (@YIn.Y ℝ opsReal (A.map (fun c => c.f t))).1)
      (@YIn.Y (Option T) _ (A.map Carrier.o)).1 :=
  (@YIn.Y _ (carrierOps S.ops) A).1.ok

/-- the carrier evaluation of `midY` encloses the real one (second output) -/
theorem YIn_Y2_tf (S : TFSoundK K Enc) (A : YIn (Carrier (Fin 4 → ℝ) T Enc)) :
    OEncG Enc (fun t => (@YIn.Y ℝ opsReal (A.map (fun c => c.f t))).2)
      (@YIn.Y (Option T) _ (A.map Carrier.o)).2 :=
  (@YIn.Y _ (carrierOps S.ops) A).2.ok

theorem tfAt_dirP2 (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => @dirP2 ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
      (tfAt K dirP2 B sh e) :=
  (@dirP2 _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).ok

-- (the elaborator meets the constants `2^352`, `2^512` of `I.mul` through the literal `1/2`)
set_option exponentiation.threshold 512 in
theorem tfAt_chP2 (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => @chP2 ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
      (tfAt K chP2 B sh e) :=
  (@chP2 _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).ok

theorem tfAt_dirMidN_det (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => (@dirMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det)
      (tfAt K dirMidN B sh e).det := by
  simp only [tfAt, dirMidN_det_eq]
  exact YIn_Y1_tf S (@dirYIn _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2
    (cx S B sh e))

theorem tfAt_dirMidN_tr (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => (@dirMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr)
      (tfAt K dirMidN B sh e).tr := by
  simp only [tfAt, dirMidN_tr_eq]
  exact YIn_Y2_tf S (@dirYIn _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2
    (cx S B sh e))

theorem tfAt_dirMidN_g (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) (i : Fin 6) :
    OEncG Enc (fun t => (@dirMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
      ((tfAt K dirMidN B sh e).g.get i) := by
  fin_cases i
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x1.ok
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x2.ok
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x3.ok
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x4.ok
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x5.ok
  · exact (@dirG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x6.ok

set_option exponentiation.threshold 512 in
theorem tfAt_chMidN_det (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => (@chMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det)
      (tfAt K chMidN B sh e).det := by
  simp only [tfAt, chMidN_det_eq]
  exact YIn_Y1_tf S (@chYIn _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2
    (cx S B sh e))

set_option exponentiation.threshold 512 in
theorem tfAt_chMidN_tr (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) :
    OEncG Enc (fun t => (@chMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr)
      (tfAt K chMidN B sh e).tr := by
  simp only [tfAt, chMidN_tr_eq]
  exact YIn_Y2_tf S (@chYIn _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2
    (cx S B sh e))

set_option exponentiation.threshold 512 in
theorem tfAt_chMidN_g (S : TFSoundK K Enc) (B : Box) (sh : Shear) (e : ℕ) (i : Fin 6) :
    OEncG Enc (fun t => (@chMidN ℝ opsReal (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
      ((tfAt K chMidN B sh e).g.get i) := by
  fin_cases i
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x1.ok
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x2.ok
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x3.ok
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x4.ok
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x5.ok
  · exact (@chG _ (carrierOps S.ops) (cz S B).1 (cz S B).2.1 (cz S B).2.2 (cx S B sh e)).x6.ok

end TFLeaf

/-! ### the root and test phases -/

section TFPhases

variable {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop}

/-- a coordinate within `r / 2^96` of `val c` is `val c + (r / 2^96) s` with `|s| ≤ 1` -/
theorem coord_of {v : ℝ} {c r : ℕ} (h : |v - val c| * 2 ^ 96 ≤ r) :
    ∃ s : ℝ, |s| ≤ 1 ∧ val c + (r : ℝ) / 2 ^ 96 * s = v := by
  have h96 : (0 : ℝ) < 2 ^ 96 := by positivity
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Nat.cast_zero] at h
    have h0 : |v - val c| = 0 := by
      have := abs_nonneg (v - val c)
      nlinarith
    rw [abs_eq_zero, sub_eq_zero] at h0
    refine ⟨0, by rw [abs_zero]; exact zero_le_one, ?_⟩
    rw [Nat.cast_zero, zero_div, zero_mul, add_zero]
    exact h0.symm
  · have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    refine ⟨(v - val c) * 2 ^ 96 / r, ?_, ?_⟩
    · rw [abs_div, abs_mul, abs_of_pos h96, abs_of_pos hr', div_le_one hr']
      exact h
    · field_simp
      ring

/-- a point of the box and a `w` within `e` is a point `t ∈ [-1, 1]⁴` of the models -/
theorem tpoint (B : Box) (sh : Shear) (e : ℕ) {z0 z1 z2 w : ℝ} (hz : B.mem z0 z1 z2)
    (hw : |w| * 2 ^ 96 ≤ e) :
    ∃ t : Fin 4 → ℝ, (∀ i, |t i| ≤ 1) ∧ tz0 B t = z0 ∧ tz1 B t = z1 ∧ tz2 B t = z2 ∧
      (e : ℝ) / 2 ^ 96 * t 3 = w ∧ tx B sh e t = xS sh B z0 z1 z2 + w := by
  obtain ⟨h0, h1, h2⟩ := hz
  obtain ⟨s0, hs0, e0⟩ := coord_of (I.abs_sub_le_radAt (I.ctr B.X0) h0)
  obtain ⟨s1, hs1, e1⟩ := coord_of (I.abs_sub_le_radAt (I.ctr B.X1) h1)
  obtain ⟨s2, hs2, e2⟩ := coord_of (I.abs_sub_le_radAt (I.ctr B.X2) h2)
  obtain ⟨s3, hs3, e3⟩ := coord_of (c := Bb) (v := w) (r := e) (by rw [val_Bb, sub_zero]; exact hw)
  rw [val_Bb, zero_add] at e3
  refine ⟨![s0, s1, s2, s3], ?_, e0, e1, e2, e3, ?_⟩
  · intro i
    fin_cases i
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  · have d0 : (I.radAt B.X0 (I.ctr B.X0) : ℝ) / 2 ^ 96 * s0 = z0 - val (I.ctr B.X0) := by linarith
    have d1 : (I.radAt B.X1 (I.ctr B.X1) : ℝ) / 2 ^ 96 * s1 = z1 - val (I.ctr B.X1) := by linarith
    have d2 : (I.radAt B.X2 (I.ctr B.X2) : ℝ) / 2 ^ 96 * s2 = z2 - val (I.ctr B.X2) := by linarith
    change @shearX ℝ opsReal (val sh.X0) (val sh.J0) (val sh.J1) (val sh.J2) (val sh.H00)
      (val sh.H01) (val sh.H02) (val sh.H11) (val sh.H12) (val sh.H22)
      (val Bb + (I.radAt B.X0 (I.ctr B.X0) : ℝ) / 2 ^ 96 * s0)
      (val Bb + (I.radAt B.X1 (I.ctr B.X1) : ℝ) / 2 ^ 96 * s1)
      (val Bb + (I.radAt B.X2 (I.ctr B.X2) : ℝ) / 2 ^ 96 * s2) (val Bb + (e : ℝ) / 2 ^ 96 * s3) = _
    rw [val_Bb, zero_add, zero_add, zero_add, zero_add, d0, d1, d2, e3]
    simp only [shearX, xS, opsReal_sq]

/-- one localisation step -/
theorem tfStep_sound (S : TFSoundK K Enc) {PF : ∀ {α : Type} [Ops α], α → α → α → α → α}
    {PR : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box} {sh : Shear}
    (hPF : ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
      (tfAt K PF B sh e))
    {rho e e' : ℕ} (h : tfStep K PF B sh rho e = some e') {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hP : PR z0 z1 z2 x = 0)
    (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e) :
    |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e' := by
  rw [tfStep] at h
  obtain ⟨hn, he'⟩ := cont_some h
  obtain rfl := Option.some.inj he'
  obtain ⟨t, ht, e0, e1, e2, e3, ex⟩ := tpoint B sh e hz hw
  have hf : PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t) = 0 := by
    rw [e0, e1, e2, ex, add_sub_cancel]
    exact hP
  have h3 := S.newtOK _ _ rho (hPF e) hn t ht hf
  have hw' : |x - xS sh B z0 z1 z2| * 2 ^ 96 = (e : ℝ) * |t 3| := by
    rw [← e3, abs_mul, abs_of_nonneg (by positivity)]
    field_simp
  have hup := up_ge (Nat.mul rho e)
  rw [cast_mul] at hup
  rw [hw']
  calc (e : ℝ) * |t 3| ≤ (e : ℝ) * ((rho : ℝ) / 2 ^ 96) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = (rho : ℝ) * e / 2 ^ 96 := by ring
    _ ≤ (I.up (Nat.mul rho e) : ℝ) := hup

/-- the step of code `c` (none for `0`) -/
theorem tfStep2_sound (S : TFSoundK K Enc) {PF : ∀ {α : Type} [Ops α], α → α → α → α → α}
    {PR : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box} {sh : Shear}
    (hPF : ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
      (tfAt K PF B sh e))
    {c e e' : ℕ} (h : tfStep2 K PF B sh c e = some e') {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hP : PR z0 z1 z2 x = 0)
    (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e) :
    |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e' := by
  rw [tfStep2] at h
  by_cases c0 : Nat.beq c 0 = true
  · rw [sel_pos _ _ c0] at h
    obtain rfl := Option.some.inj h
    exact hw
  · rw [sel_neg _ _ c0] at h
    exact tfStep_sound S hPF h hz hP hw

/-- the root phase -/
theorem tfRoot_sound (S : TFSoundK K Enc) {PF : ∀ {α : Type} [Ops α], α → α → α → α → α}
    {PR : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box} {sh : Shear}
    (hPF : ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
      (tfAt K PF B sh e))
    {e0 c1 c2 e2 : ℕ} (h : tfRoot K PF B sh e0 c1 c2 = some e2) {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hP : PR z0 z1 z2 x = 0)
    (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e0) :
    |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e2 := by
  rw [tfRoot] at h
  obtain ⟨e1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact tfStep2_sound S hPF h2 hz hP (tfStep2_sound S hPF h1 hz hP hw)

omit [Ops (Option T)] in
/-- the constraint chosen by `gselG` encloses one of the six constraints -/
theorem gselG_enc {g : Six (Option T)} {G : Fin 6 → (Fin 4 → ℝ) → ℝ}
    (hG : ∀ i, OEncG Enc (G i) (g.get i)) (f : ℕ) : ∃ i, OEncG Enc (G i) (gselG g f) := by
  unfold gselG
  by_cases c0 : Nat.beq f 0 = true
  · rw [sel_pos _ _ c0]; exact ⟨0, hG 0⟩
  rw [sel_neg _ _ c0]
  by_cases c1 : Nat.beq f 1 = true
  · rw [sel_pos _ _ c1]; exact ⟨1, hG 1⟩
  rw [sel_neg _ _ c1]
  by_cases c2 : Nat.beq f 2 = true
  · rw [sel_pos _ _ c2]; exact ⟨2, hG 2⟩
  rw [sel_neg _ _ c2]
  by_cases c3 : Nat.beq f 3 = true
  · rw [sel_pos _ _ c3]; exact ⟨3, hG 3⟩
  rw [sel_neg _ _ c3]
  by_cases c4 : Nat.beq f 4 = true
  · rw [sel_pos _ _ c4]; exact ⟨4, hG 4⟩
  rw [sel_neg _ _ c4]
  by_cases c5 : Nat.beq f 5 = true
  · rw [sel_pos _ _ c5]; exact ⟨5, hG 5⟩
  rw [sel_neg _ _ c5]
  exact ⟨0, OEncG.none⟩

/-- the test phase -/
theorem tfTest_sound (S : TFSoundK K Enc) {OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α}
    {OR : ℝ → ℝ → ℝ → ℝ → Out ℝ} {B : Box} {sh : Shear}
    (hdet : ∀ e, OEncG Enc (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det)
      (tfAt K OF B sh e).det)
    (htr : ∀ e, OEncG Enc (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr)
      (tfAt K OF B sh e).tr)
    (hg : ∀ e i, OEncG Enc (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
      ((tfAt K OF B sh e).g.get i))
    {e mf f mu : ℕ} (hmu : 0 ≤ val mu) (h : tfTest K OF B sh e mf f mu = true)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e)
    (hG : ∀ i, 0 ≤ (OR z0 z1 z2 x).g.get i) :
    0 < (OR z0 z1 z2 x).det ∧ 0 < (OR z0 z1 z2 x).tr := by
  obtain ⟨t, ht, e0, e1, e2, -, ex⟩ := tpoint B sh e hz hw
  have hx : tx B sh e t = x := by rw [ex, add_sub_cancel]
  rw [tfTest, tftest] at h
  obtain ⟨h1, h2⟩ := both_true h
  refine ⟨?_, ?_⟩
  · by_cases cm : Nat.beq mf 0 = true
    · rw [sel_pos _ _ cm] at h1
      have := S.posT _ _ (hdet e) h1 t ht
      simp only [e0, e1, e2, hx] at this
      exact this
    · rw [sel_neg _ _ cm] at h1
      obtain ⟨i, hi⟩ := gselG_enc (hg e) f
      have henc := S.ops.sub _ _ _ _ (hdet e) (S.ops.mul _ _ _ _ (OEncG.of_some (S.ptB mu)) hi)
      have := S.posT _ _ henc h1 t ht
      simp only [e0, e1, e2, hx] at this
      have := mul_nonneg hmu (hG i)
      linarith
  · have := S.posT _ _ (htr e) h2 t ht
    simp only [e0, e1, e2, hx] at this
    exact this

end TFPhases


/-! ### the Taylor-model modes -/

section TFModes

variable {E4 : ((Fin 4 → ℝ) → ℝ) → TF.W4.T → Prop} {EF4 : ((Fin 4 → ℝ) → ℝ) → TF.F4.T → Prop}
  {EW5 : ((Fin 4 → ℝ) → ℝ) → TF.W5.T → Prop} {EF3 : ((Fin 4 → ℝ) → ℝ) → TF.F3.T → Prop}

/-- the soundness of the four model types -/
structure TFKits (E4 : ((Fin 4 → ℝ) → ℝ) → TF.W4.T → Prop)
    (EF4 : ((Fin 4 → ℝ) → ℝ) → TF.F4.T → Prop) (EW5 : ((Fin 4 → ℝ) → ℝ) → TF.W5.T → Prop)
    (EF3 : ((Fin 4 → ℝ) → ℝ) → TF.F3.T → Prop) : Prop where
  w4 : TFSoundK kitW4 E4
  f4 : TFSoundK kitF4 EF4
  w5 : TFSoundK kitW5 EW5
  f3 : TFSoundK kitF3 EF3

/-- the root phase in any of the four models -/
theorem rootSel_sound (KS : TFKits E4 EF4 EW5 EF3)
    {PF : ∀ {α : Type} [Ops α], α → α → α → α → α} {PR : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box}
    {sh : Shear}
    (hPF : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
        (tfAt K PF B sh e))
    {m e0 c1 c2 e2 : ℕ} (h : rootSel PF B sh m e0 c1 c2 = some e2) {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hP : PR z0 z1 z2 x = 0)
    (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e0) :
    |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e2 := by
  unfold rootSel at h
  by_cases c0 : Nat.beq m 0 = true
  · rw [sel_pos _ _ c0] at h
    exact tfRoot_sound KS.w4 (hPF KS.w4) h hz hP hw
  rw [sel_neg _ _ c0] at h
  by_cases c1' : Nat.beq m 1 = true
  · rw [sel_pos _ _ c1'] at h
    exact tfRoot_sound KS.f4 (hPF KS.f4) h hz hP hw
  rw [sel_neg _ _ c1'] at h
  by_cases c2' : Nat.beq m 2 = true
  · rw [sel_pos _ _ c2'] at h
    exact tfRoot_sound KS.w5 (hPF KS.w5) h hz hP hw
  rw [sel_neg _ _ c2'] at h
  exact tfRoot_sound KS.f3 (hPF KS.f3) h hz hP hw

/-- the test phase in any of the four models -/
theorem testSel_sound (KS : TFKits E4 EF4 EW5 EF3)
    {OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α} {OR : ℝ → ℝ → ℝ → ℝ → Out ℝ} {B : Box}
    {sh : Shear}
    (hdet : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det) (tfAt K OF B sh e).det)
    (htr : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr) (tfAt K OF B sh e).tr)
    (hg : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e i, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
        ((tfAt K OF B sh e).g.get i))
    {m e mf f mu : ℕ} (hmu : 0 ≤ val mu) (h : testSel OF B sh m e mf f mu = true)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e)
    (hG : ∀ i, 0 ≤ (OR z0 z1 z2 x).g.get i) :
    0 < (OR z0 z1 z2 x).det ∧ 0 < (OR z0 z1 z2 x).tr := by
  unfold testSel at h
  by_cases c0 : Nat.beq m 0 = true
  · rw [sel_pos _ _ c0] at h
    exact tfTest_sound KS.w4 (hdet KS.w4) (htr KS.w4) (hg KS.w4) hmu h hz hw hG
  rw [sel_neg _ _ c0] at h
  by_cases c1 : Nat.beq m 1 = true
  · rw [sel_pos _ _ c1] at h
    exact tfTest_sound KS.f4 (hdet KS.f4) (htr KS.f4) (hg KS.f4) hmu h hz hw hG
  rw [sel_neg _ _ c1] at h
  by_cases c2 : Nat.beq m 2 = true
  · rw [sel_pos _ _ c2] at h
    exact tfTest_sound KS.w5 (hdet KS.w5) (htr KS.w5) (hg KS.w5) hmu h hz hw hG
  rw [sel_neg _ _ c2] at h
  exact tfTest_sound KS.f3 (hdet KS.f3) (htr KS.f3) (hg KS.f3) hmu h hz hw hG

/-- the starting band holds every `w` of `W` -/
theorem band_of_mem {w : ℝ} {W : I} (hw : I.mem w W) :
    |w| * 2 ^ 96 ≤ (I.mx (Nat.sub W.L Bb) (Nat.sub W.H Bb) : ℝ) := by
  obtain ⟨h1, h2⟩ := hw
  have eL := sub_le_cast W.L Bb
  have eH := sub_le_cast W.H Bb
  rw [cBb] at eL eH
  rw [mx_eq, Nat.cast_max]
  unfold val at h1 h2
  rw [le_div_iff₀ (by positivity)] at h1 h2
  rcases abs_cases w with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_trans (by linarith) (le_max_left _ _)

theorem afterRoot_true {k : ℕ → Bool} {o : Option ℕ} (h : afterRoot k o = true) :
    ∃ e, o = some e ∧ k e = true := by
  cases o with
  | none => cases h
  | some e => exact ⟨e, rfl, h⟩

theorem val_mu24 (m : ℕ) : 0 ≤ val (Nat.add Bb (Nat.shiftLeft m 80)) :=
  le_of_le_of_eq (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))
    (val_addB' (Nat.shiftLeft m 80)).symm

/-- the Taylor-model leaf is sound -/
theorem evTF_sound (KS : TFKits E4 EF4 EW5 EF3)
    {PF : ∀ {α : Type} [Ops α], α → α → α → α → α} {PR : ℝ → ℝ → ℝ → ℝ → ℝ}
    {OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α} {OR : ℝ → ℝ → ℝ → ℝ → Out ℝ}
    {B : Box} {sh : Shear}
    (hPF : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
        (tfAt K PF B sh e))
    (hdet : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det) (tfAt K OF B sh e).det)
    (htr : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr) (tfAt K OF B sh e).tr)
    (hg : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e i, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
        ((tfAt K OF B sh e).g.get i))
    {fl : ℕ} {W : I} (h : evTF PF OF B sh fl W = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hP : PR z0 z1 z2 x = 0) (hG : ∀ i, 0 ≤ (OR z0 z1 z2 x).g.get i)
    (hw : I.mem (x - xS sh B z0 z1 z2) W) :
    0 < (OR z0 z1 z2 x).det ∧ 0 < (OR z0 z1 z2 x).tr := by
  rw [evTF] at h
  obtain ⟨e2, he2, ht⟩ := afterRoot_true h
  have hw2 := rootSel_sound KS hPF he2 hz hP (band_of_mem hw)
  exact testSel_sound KS hdet htr hg (val_mu24 _) ht hz hw2 hG

/-- the direct chart with the Taylor-model leaf is sound, given the four model types -/
theorem dirModeTF_sound (KS : TFKits E4 EF4 EW5 EF3) : ModeSound2 dirModeTF dirSem2 where
  kl := dirMode2_sound.kl
  gP := dirMode2_sound.gP
  outJ := dirMode2_sound.outJ
  out_g := dirMode2_sound.out_g
  ev2 B sh _ _ h _ _ _ _ hz _ hG hP hw :=
    evTF_sound KS (fun S e => tfAt_dirP2 S B sh e) (fun S e => tfAt_dirMidN_det S B sh e)
      (fun S e => tfAt_dirMidN_tr S B sh e) (fun S e i => tfAt_dirMidN_g S B sh e i) h hz hP hG
      hw

/-- the blow-up chart with the Taylor-model leaf is sound, given the four model types -/
theorem chModeTF_sound (k : ℕ) (KS : TFKits E4 EF4 EW5 EF3) :
    ModeSound2 (chModeTF k) chSem2 where
  kl := (chMode2_sound k).kl
  gP := (chMode2_sound k).gP
  outJ := (chMode2_sound k).outJ
  out_g := (chMode2_sound k).out_g
  ev2 B sh _ _ h _ _ _ _ hz _ hG hP hw :=
    evTF_sound KS (fun S e => tfAt_chP2 S B sh e) (fun S e => tfAt_chMidN_det S B sh e)
      (fun S e => tfAt_chMidN_tr S B sh e) (fun S e i => tfAt_chMidN_g S B sh e i) h hz hP hG
      hw

/-! ### the minimal model set: `W4` and `F4` -/

/-- the soundness of the models `W4` and `F4` -/
structure TFKitsM (E4 : ((Fin 4 → ℝ) → ℝ) → TF.W4.T → Prop)
    (EF4 : ((Fin 4 → ℝ) → ℝ) → TF.F4.T → Prop) : Prop where
  w4 : TFSoundK kitW4 E4
  f4 : TFSoundK kitF4 EF4

/-- the root phase in `W4` or `F4` -/
theorem rootSelM_sound (KS : TFKitsM E4 EF4)
    {PF : ∀ {α : Type} [Ops α], α → α → α → α → α} {PR : ℝ → ℝ → ℝ → ℝ → ℝ} {B : Box}
    {sh : Shear}
    (hPF : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
        (tfAt K PF B sh e))
    {m e0 c1 c2 e2 : ℕ} (h : rootSelM PF B sh m e0 c1 c2 = some e2) {z0 z1 z2 x : ℝ}
    (hz : B.mem z0 z1 z2) (hP : PR z0 z1 z2 x = 0)
    (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e0) :
    |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e2 := by
  unfold rootSelM at h
  by_cases c0 : Nat.beq m 0 = true
  · rw [sel_pos _ _ c0] at h
    exact tfRoot_sound KS.w4 (hPF KS.w4) h hz hP hw
  rw [sel_neg _ _ c0] at h
  by_cases c1' : Nat.beq m 1 = true
  · rw [sel_pos _ _ c1'] at h
    exact tfRoot_sound KS.f4 (hPF KS.f4) h hz hP hw
  rw [sel_neg _ _ c1'] at h
  cases h

/-- the test phase in `W4` or `F4` -/
theorem testSelM_sound (KS : TFKitsM E4 EF4)
    {OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α} {OR : ℝ → ℝ → ℝ → ℝ → Out ℝ} {B : Box}
    {sh : Shear}
    (hdet : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det) (tfAt K OF B sh e).det)
    (htr : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr) (tfAt K OF B sh e).tr)
    (hg : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e i, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
        ((tfAt K OF B sh e).g.get i))
    {m e mf f mu : ℕ} (hmu : 0 ≤ val mu) (h : testSelM OF B sh m e mf f mu = true)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hw : |x - xS sh B z0 z1 z2| * 2 ^ 96 ≤ e)
    (hG : ∀ i, 0 ≤ (OR z0 z1 z2 x).g.get i) :
    0 < (OR z0 z1 z2 x).det ∧ 0 < (OR z0 z1 z2 x).tr := by
  unfold testSelM at h
  by_cases c0 : Nat.beq m 0 = true
  · rw [sel_pos _ _ c0] at h
    exact tfTest_sound KS.w4 (hdet KS.w4) (htr KS.w4) (hg KS.w4) hmu h hz hw hG
  rw [sel_neg _ _ c0] at h
  by_cases c1 : Nat.beq m 1 = true
  · rw [sel_pos _ _ c1] at h
    exact tfTest_sound KS.f4 (hdet KS.f4) (htr KS.f4) (hg KS.f4) hmu h hz hw hG
  rw [sel_neg _ _ c1] at h
  cases h

/-- the `W4`/`F4` Taylor-model leaf is sound -/
theorem evTFM_sound (KS : TFKitsM E4 EF4)
    {PF : ∀ {α : Type} [Ops α], α → α → α → α → α} {PR : ℝ → ℝ → ℝ → ℝ → ℝ}
    {OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α} {OR : ℝ → ℝ → ℝ → ℝ → Out ℝ}
    {B : Box} {sh : Shear}
    (hPF : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc (fun t => PR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t))
        (tfAt K PF B sh e))
    (hdet : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).det) (tfAt K OF B sh e).det)
    (htr : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).tr) (tfAt K OF B sh e).tr)
    (hg : ∀ {T : Type} [Ops (Option T)] {K : TFKit T} {Enc : ((Fin 4 → ℝ) → ℝ) → T → Prop},
      TFSoundK K Enc → ∀ e i, OEncG Enc
        (fun t => (OR (tz0 B t) (tz1 B t) (tz2 B t) (tx B sh e t)).g.get i)
        ((tfAt K OF B sh e).g.get i))
    {fl : ℕ} {W : I} (h : evTFM PF OF B sh fl W = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2)
    (hP : PR z0 z1 z2 x = 0) (hG : ∀ i, 0 ≤ (OR z0 z1 z2 x).g.get i)
    (hw : I.mem (x - xS sh B z0 z1 z2) W) :
    0 < (OR z0 z1 z2 x).det ∧ 0 < (OR z0 z1 z2 x).tr := by
  rw [evTFM] at h
  obtain ⟨e2, he2, ht⟩ := afterRoot_true h
  have hw2 := rootSelM_sound KS hPF he2 hz hP (band_of_mem hw)
  exact testSelM_sound KS hdet htr hg (val_mu24 _) ht hz hw2 hG

/-- the direct chart with the `W4`/`F4` leaf is sound, given the two model types -/
theorem dirModeTFM_sound (KS : TFKitsM E4 EF4) : ModeSound2 dirModeTFM dirSem2 where
  kl := dirMode2_sound.kl
  gP := dirMode2_sound.gP
  outJ := dirMode2_sound.outJ
  out_g := dirMode2_sound.out_g
  ev2 B sh _ _ h _ _ _ _ hz _ hG hP hw :=
    evTFM_sound KS (fun S e => tfAt_dirP2 S B sh e) (fun S e => tfAt_dirMidN_det S B sh e)
      (fun S e => tfAt_dirMidN_tr S B sh e) (fun S e i => tfAt_dirMidN_g S B sh e i) h hz hP hG
      hw

/-- the blow-up chart with the `W4`/`F4` leaf is sound, given the two model types -/
theorem chModeTFM_sound (k : ℕ) (KS : TFKitsM E4 EF4) :
    ModeSound2 (chModeTFM k) chSem2 where
  kl := (chMode2_sound k).kl
  gP := (chMode2_sound k).gP
  outJ := (chMode2_sound k).outJ
  out_g := (chMode2_sound k).out_g
  ev2 B sh _ _ h _ _ _ _ hz _ hG hP hw :=
    evTFM_sound KS (fun S e => tfAt_chP2 S B sh e) (fun S e => tfAt_chMidN_det S B sh e)
      (fun S e => tfAt_chMidN_tr S B sh e) (fun S e i => tfAt_chMidN_g S B sh e i) h hz hP hG
      hw

end TFModes

end

end C4
