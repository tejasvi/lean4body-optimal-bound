module

public import C4.SearchSound
public import C4Check.Grid2

@[expose] public section

/-!
# Soundness of the two modes of the sheared replay

`Sem2`: the real semantics of a chart (`k`, `l` with `g = k + l x`, `P`, and the outputs of the
midpoint test).  `ModeSound2 M Sm`: every checker component of `M` encloses the corresponding real
quantity of `Sm`, for jets of *any* functions as arguments (the sheared leaf passes the jet of
`x = x₀(z) + w`).  As for the first-order checker (`C4Check.Search`), the checker components are, by `rfl`, the evaluations of the generic
formulas at the carriers `EI` and `EJ`.
-/

namespace C4

noncomputable section

/-! ## real semantics -/

abbrev dirP2R (a b c x : ℝ) : ℝ := @dirP2 ℝ opsReal a b c x
abbrev chP2R (b al ga xi : ℝ) : ℝ := @chP2 ℝ opsReal b al ga xi

/-- the real semantics of a chart for the sheared replay -/
structure Sem2 where
  K : ℝ → ℝ → ℝ → Six ℝ
  L : ℝ → ℝ → ℝ → Six ℝ
  P : ℝ → ℝ → ℝ → ℝ → ℝ
  out : ℝ → ℝ → ℝ → ℝ → Out ℝ

/-- the constraints `g = k + l x` -/
abbrev Sem2.G (Sm : Sem2) (z0 z1 z2 x : ℝ) : Six ℝ :=
  @aff ℝ opsReal (Sm.K z0 z1 z2) (Sm.L z0 z1 z2) x

/-- the direct chart, with the normalized test -/
def dirSem2 : Sem2 :=
  ⟨dirKR, dirLR, dirP2R, fun a b c x => @dirMidN ℝ opsReal a b c x⟩

/-- the blow-up chart, with the normalized test -/
def chSem2 : Sem2 :=
  ⟨chKR, chLR, chP2R, fun b al ga xi => @chMidN ℝ opsReal b al ga xi⟩

/-- zero certificate data (the semantics `Sem2.toSem` of the first-order checker never looks at it) -/
def certZeroR : Cert ℝ :=
  ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩

/-- the semantics of the first-order checker (`C4Check.Search`) with the same constraints and `P`,
for `Mode2.toMode` -/
def Sem2.toSem (Sm : Sem2) : Sem := ⟨Sm.K, Sm.L, Sm.P, fun _ _ _ _ => certZeroR⟩

/-- the shear `x₀(z) = X₀ + Σ J_i δ_i + Σ_{i≤j} H_ij δ_i δ_j`, `δ_i = z_i - z̄_i`, `z̄` the centre
of `B` -/
def xS (sh : Shear) (B : Box) (z0 z1 z2 : ℝ) : ℝ :=
  val sh.X0 + (val sh.J0 * (z0 - val (I.ctr B.X0)) + val sh.J1 * (z1 - val (I.ctr B.X1)) +
    val sh.J2 * (z2 - val (I.ctr B.X2))) +
  ((z0 - val (I.ctr B.X0)) * (val sh.H00 * (z0 - val (I.ctr B.X0)) +
      val sh.H01 * (z1 - val (I.ctr B.X1)) + val sh.H02 * (z2 - val (I.ctr B.X2))) +
    (z1 - val (I.ctr B.X1)) * (val sh.H11 * (z1 - val (I.ctr B.X1)) +
      val sh.H12 * (z2 - val (I.ctr B.X2))) +
    val sh.H22 * (z2 - val (I.ctr B.X2)) ^ 2)

structure ModeSound2 (M : Mode2) (Sm : Sem2) : Prop where
  kl : ∀ (A B C : I) (a b c : ℝ), I.mem a A → I.mem b B → I.mem c C →
    (∀ i, OEnc ((Sm.K a b c).get i) ((M.kl A B C).1.get i)) ∧
    (∀ i, OEnc ((Sm.L a b c).get i) ((M.kl A B C).2.get i))
  gP : ∀ (S : Set P4) (zc : P4) (R : Rad), RadOK S zc R →
    ∀ (f0 f1 f2 f3 : P4 → ℝ) (z0 z1 z2 z3 : J), JEnc S zc f0 z0 → JEnc S zc f1 z1 →
    JEnc S zc f2 z2 → JEnc S zc f3 z3 →
    (∀ i, OJEnc S zc (fun z => (Sm.G (f0 z) (f1 z) (f2 z) (f3 z)).get i)
      ((M.gP R z0 z1 z2 z3).1.get i)) ∧
    OJEnc S zc (fun z => Sm.P (f0 z) (f1 z) (f2 z) (f3 z)) (M.gP R z0 z1 z2 z3).2
  outJ : ∀ (S : Set P4) (zc : P4) (R : Rad), RadOK S zc R →
    ∀ (f0 f1 f2 f3 : P4 → ℝ) (z0 z1 z2 z3 : J), JEnc S zc f0 z0 → JEnc S zc f1 z1 →
    JEnc S zc f2 z2 → JEnc S zc f3 z3 →
    OJEnc S zc (fun z => (Sm.out (f0 z) (f1 z) (f2 z) (f3 z)).det)
      (M.outJ R z0 z1 z2 z3).det ∧
    OJEnc S zc (fun z => (Sm.out (f0 z) (f1 z) (f2 z) (f3 z)).tr)
      (M.outJ R z0 z1 z2 z3).tr ∧
    ∀ i, OJEnc S zc (fun z => (Sm.out (f0 z) (f1 z) (f2 z) (f3 z)).g.get i)
      ((M.outJ R z0 z1 z2 z3).g.get i)
  out_g : ∀ z0 z1 z2 x, (Sm.out z0 z1 z2 x).g = Sm.G z0 z1 z2 x
  /-- the mode's own evaluator certifies the test at every feasible zero whose `w` lies in `W` -/
  ev2 : ∀ (B : Box) (sh : Shear) (fl : Nat) (W : I), M.ev2 B sh fl W = true →
    ∀ z0 z1 z2 x, B.mem z0 z1 z2 → (M.clamp = true → -1 ≤ x ∧ x ≤ 1) →
    (∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) → Sm.P z0 z1 z2 x = 0 →
    I.mem (x - xS sh B z0 z1 z2) W → 0 < (Sm.out z0 z1 z2 x).det ∧ 0 < (Sm.out z0 z1 z2 x).tr

/-- a sound sheared mode gives a sound mode of the first-order checker (`C4Check.Search`), for its
`xrange` and `locH` -/
theorem ModeSound2.toModeSound {M : Mode2} {Sm : Sem2} (hM : ModeSound2 M Sm) :
    ModeSound M.toMode Sm.toSem where
  kl := hM.kl
  gP S zc R hR z0 z1 z2 z3 h0 h1 h2 h3 := hM.gP S zc R hR _ _ _ _ z0 z1 z2 z3 h0 h1 h2 h3
  trJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := fun _ h => by cases h

/-! ## the formulas at carriers with variable leaves -/

section
variable {S : Set P4} {zc : P4} {R : Rad} (hR : RadOK S zc R) {f0 f1 f2 f3 : P4 → ℝ}
  {o0 o1 o2 o3 : Option J}
  (h0 : OJEnc S zc f0 o0) (h1 : OJEnc S zc f1 o1) (h2 : OJEnc S zc f2 o2) (h3 : OJEnc S zc f3 o3)
include hR h0 h1 h2 h3

theorem dirG_enc2 (i : Fin 6) :
    OJEnc S zc (fun z => (dirGR (f0 z) (f1 z) (f2 z) (f3 z)).get i)
      ((@dirG _ (jetOps R) o0 o1 o2 o3).get i) := by
  fin_cases i
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x1.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x2.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x3.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x4.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x5.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x6.ok

theorem chG_enc2 (i : Fin 6) :
    OJEnc S zc (fun z => (chGR (f0 z) (f1 z) (f2 z) (f3 z)).get i)
      ((@chG _ (jetOps R) o0 o1 o2 o3).get i) := by
  fin_cases i
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x1.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x2.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x3.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x4.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x5.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).x6.ok

theorem dirP2_enc :
    OJEnc S zc (fun z => dirP2R (f0 z) (f1 z) (f2 z) (f3 z)) (@dirP2 _ (jetOps R) o0 o1 o2 o3) :=
  (@dirP2 (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).ok

-- (the elaborator meets the constants `2^352`, `2^512` of `I.mul` through the literal `1/2`)
set_option exponentiation.threshold 512 in
theorem chP2_enc :
    OJEnc S zc (fun z => chP2R (f0 z) (f1 z) (f2 z) (f3 z)) (@chP2 _ (jetOps R) o0 o1 o2 o3) :=
  (@chP2 (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩ ⟨f3, o3, h3⟩).ok

theorem dirMidN_g_enc (i : Fin 6) :
    OJEnc S zc (fun z => (@dirMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).g.get i)
      ((@dirMidN _ (jetOps R) o0 o1 o2 o3).g.get i) :=
  dirG_enc2 hR h0 h1 h2 h3 i

theorem chMidN_g_enc (i : Fin 6) :
    OJEnc S zc (fun z => (@chMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).g.get i)
      ((@chMidN _ (jetOps R) o0 o1 o2 o3).g.get i) :=
  chG_enc2 hR h0 h1 h2 h3 i

omit h0 h1 h2 h3 in
/-- the carrier evaluation of `midY` encloses the real one (first output) -/
theorem YIn_Y1_enc (A : YIn (EJ S zc)) :
    OJEnc S zc (fun z => (@YIn.Y ℝ opsReal (A.map (fun e => e.f z))).1)
      (@YIn.Y _ (jetOps R) (A.map EJ.j)).1 :=
  (@YIn.Y (EJ S zc) (ejOps R hR) A).1.ok

omit h0 h1 h2 h3 in
/-- the carrier evaluation of `midY` encloses the real one (second output) -/
theorem YIn_Y2_enc (A : YIn (EJ S zc)) :
    OJEnc S zc (fun z => (@YIn.Y ℝ opsReal (A.map (fun e => e.f z))).2)
      (@YIn.Y _ (jetOps R) (A.map EJ.j)).2 :=
  (@YIn.Y (EJ S zc) (ejOps R hR) A).2.ok

theorem dirMidN_det_enc :
    OJEnc S zc (fun z => (@dirMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).det)
      (@dirMidN _ (jetOps R) o0 o1 o2 o3).det := by
  simp only [dirMidN_det_eq]
  exact YIn_Y1_enc hR (@dirYIn (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩
    ⟨f3, o3, h3⟩)

theorem dirMidN_tr_enc :
    OJEnc S zc (fun z => (@dirMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).tr)
      (@dirMidN _ (jetOps R) o0 o1 o2 o3).tr := by
  simp only [dirMidN_tr_eq]
  exact YIn_Y2_enc hR (@dirYIn (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩
    ⟨f3, o3, h3⟩)

-- (the elaborator meets the constants `2^352`, `2^512` of `I.mul` through the literal `1/2`)
set_option exponentiation.threshold 512 in
theorem chMidN_det_enc :
    OJEnc S zc (fun z => (@chMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).det)
      (@chMidN _ (jetOps R) o0 o1 o2 o3).det := by
  simp only [chMidN_det_eq]
  exact YIn_Y1_enc hR (@chYIn (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩
    ⟨f3, o3, h3⟩)

set_option exponentiation.threshold 512 in
theorem chMidN_tr_enc :
    OJEnc S zc (fun z => (@chMidN ℝ opsReal (f0 z) (f1 z) (f2 z) (f3 z)).tr)
      (@chMidN _ (jetOps R) o0 o1 o2 o3).tr := by
  simp only [chMidN_tr_eq]
  exact YIn_Y2_enc hR (@chYIn (EJ S zc) (ejOps R hR) ⟨f0, o0, h0⟩ ⟨f1, o1, h1⟩ ⟨f2, o2, h2⟩
    ⟨f3, o3, h3⟩)

end

/-! ## the two modes -/

theorem dirMode2_sound : ModeSound2 dirMode2 dirSem2 where
  kl A B C a b c ha hb hc := by
    dsimp only [dirMode2]
    exact ⟨dirK_enc (.some ha) (.some hb) (.some hc), dirL_enc (.some ha) (.some hb) (.some hc)⟩
  gP S zc R hR f0 f1 f2 f3 z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [dirMode2]
    exact ⟨dirG_enc2 hR (.some h0) (.some h1) (.some h2) (.some h3),
      dirP2_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  outJ S zc R hR f0 f1 f2 f3 z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [dirMode2]
    exact ⟨dirMidN_det_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      dirMidN_tr_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      dirMidN_g_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  out_g _ _ _ _ := rfl
  ev2 _ _ _ _ h := by cases h

theorem chMode2_sound (k : Nat) : ModeSound2 (chMode2 k) chSem2 where
  kl A B C a b c ha hb hc := by
    dsimp only [chMode2]
    exact ⟨chK_enc (.some ha) (.some hb) (.some hc), chL_enc (.some ha) (.some hb) (.some hc)⟩
  gP S zc R hR f0 f1 f2 f3 z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [chMode2]
    exact ⟨chG_enc2 hR (.some h0) (.some h1) (.some h2) (.some h3),
      chP2_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  outJ S zc R hR f0 f1 f2 f3 z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [chMode2]
    exact ⟨chMidN_det_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      chMidN_tr_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      chMidN_g_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  out_g _ _ _ _ := rfl
  ev2 _ _ _ _ h := by cases h

end

end C4
