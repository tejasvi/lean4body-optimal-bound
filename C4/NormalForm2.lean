module

public import C4.Midpoint
public import C4.NormalForm
public import C4.Dziobek
public import C4Check.Formulas2

@[expose] public section

/-!
# The normalized midpoint test at a normal-form central configuration

`dirMidN a b c x` computes `det Y` and `tr Y` of the `2 × 2` matrix `Y = diag(1, s²) - X / F` of
`C4Check.Formulas2` (`s² = 1 - x²`).  This file shows that at a point of `𝒞` that carries Dziobek's
relations with `σ < 0`, `det Y > 0` and `tr Y > 0` give `T ≻ 0` for the geometric quadratic form
`Tform` of `C4.Midpoint`, with the weights `d_e = D_e τ_e²` of the configuration `qd a b c x`.

* `nf2_weights`: `d_e = λ d'_e` edge by edge, with `λ = s² / (12 den) > 0`, where `d'_e` are the
  weights of `dirMid` and `dirMidN` (`dirArgs` mirrors `dirMid`'s let-chain);
* `dirP2_eq`: `dirP2 = dirP` at `ℝ`;
* `midY_pos`: `det Y > 0` and `tr Y > 0` give `Y[z] > 0` for `z ≠ 0`, for the inputs `YIn` of
  `midY` (`dirYIn` computes those of `dirMidN`, `C4Check.Formulas2`);
* `QY_eq`: `Y[w]` through a vector `w` with `⟨A v, w⟩ = κ ⟨v, z⟩`;
* `nfN_Tform_pos`: `T[u] = 3 λ² den W Y[k N (u₁, s u₂)]`, so `T ≻ 0`.

The helper lemmas `n2_*` up to `n2_Dgeo` are copies of the private lemmas `nf_*` of
`C4.NormalForm`, which is kept verbatim.
-/

namespace C4

/-! ## the inputs of `midT` in `dirMid` -/

/-- the twenty inputs of `midT` -/
structure MidArgs (α : Type) where
  G : α
  Kxx : α
  Kxe : α
  Kee : α
  d12 : α
  d13 : α
  d14 : α
  d23 : α
  d24 : α
  d34 : α
  u12x : α
  u13x : α
  u14x : α
  u23x : α
  u24x : α
  u34x : α
  u12e : α
  u13e : α
  u14e : α
  u24e : α

section
variable {α : Type} [Ops α]

/-- the inputs of `midT` in `dirMid`, by the same let-chain -/
def dirArgs (vx ve a b c x : α) : MidArgs α :=
  let g := dirG a b c x
  let R12 := 1 + a * a - 2 * a * x
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R34 := b * b + c * c - 2 * b * c * x
  let r12 := Ops.sqrt R12
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let r34 := Ops.sqrt R34
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let d12_23 := r13 * g.x4
  let Dl13 := g.x1 * hdr R12 r12 R13 r13
  let Dl24 := g.x2 * hdr R12 r12 R24 r24
  let E34 := (d12_23 + r24 * g.x5) * hdr R34 r34 R12 r12
  let E14 := r24 * g.x3 * hdr R14 r14 R12 r12
  let E23 := d12_23 * hdr R23 r23 R12 r12
  let den := Dl13 + E34 + Dl24
  let P12 := Dl13 * Dl24
  let k := r13 * r24
  let X2 := a * x
  let X4 := c * x
  let p := a * c
  let px := p * x
  ⟨den * Ops.sq k, Ops.sq (b - px * x) + Ops.sq px * (1 - Ops.sq x), px * (p - b), Ops.sq p,
    P12 * (b * c * k) * (Ops.sq R12 * r12),
    Dl13 * (E34 + Dl13) * (b * R24) * (Ops.sq R13 * r13),
    (den * E14 + P12) * (a * b * k) * (Ops.sq R14 * r14),
    (den * E23 + P12) * (c * k) * (Ops.sq R23 * r23),
    Dl24 * (E34 + Dl24) * (a * c * R13) * (Ops.sq R24 * r24),
    (E34 + Dl13) * (E34 + Dl24) * (a * k) * (Ops.sq R34 * r34),
    1 + X2 - vx, 1 - b - vx, 1 - X4 - vx, X2 - b - vx, X2 - X4 - vx, -b - X4 - vx,
    a - ve, -ve, -c - ve, a - c - ve⟩

end

noncomputable section

private lemma n2_s_pos {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) : 0 < Real.sqrt (1 - x ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith)

private lemma n2_s_sq {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (by nlinarith)

private lemma n2_qd0 (a b c x : ℝ) : qd a b c x 0 = (1, 0) := rfl
private lemma n2_qd1 (a b c x : ℝ) : qd a b c x 1 = (a * x, a * Real.sqrt (1 - x ^ 2)) := rfl
private lemma n2_qd2 (a b c x : ℝ) : qd a b c x 2 = (-b, 0) := rfl
private lemma n2_qd3 (a b c x : ℝ) :
    qd a b c x 3 = (-(c * x), -(c * Real.sqrt (1 - x ^ 2))) := rfl

private lemma n2_area0 (a b c x : ℝ) :
    area (qd a b c x) 0 = b * (a + c) * Real.sqrt (1 - x ^ 2) / 2 := by
  change cross (qd a b c x 2 - qd a b c x 1) (qd a b c x 3 - qd a b c x 1) / 2 = _
  rw [n2_qd1, n2_qd2, n2_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma n2_area1 (a b c x : ℝ) :
    area (qd a b c x) 1 = -(c * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 := by
  change -(cross (qd a b c x 2 - qd a b c x 0) (qd a b c x 3 - qd a b c x 0) / 2) = _
  rw [n2_qd0, n2_qd2, n2_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma n2_area2 (a b c x : ℝ) :
    area (qd a b c x) 2 = (a + c) * Real.sqrt (1 - x ^ 2) / 2 := by
  change cross (qd a b c x 1 - qd a b c x 0) (qd a b c x 3 - qd a b c x 0) / 2 = _
  rw [n2_qd0, n2_qd1, n2_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma n2_area3 (a b c x : ℝ) :
    area (qd a b c x) 3 = -(a * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 := by
  change -(cross (qd a b c x 1 - qd a b c x 0) (qd a b c x 2 - qd a b c x 0) / 2) = _
  rw [n2_qd0, n2_qd1, n2_qd2]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma n2_Rs_comm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma n2_R02 (a b c x : ℝ) : Rs (qd a b c x) 0 2 = (1 + b) ^ 2 := by
  rw [Rs, n2_qd0, n2_qd2]; simp only [dot, Prod.mk_sub_mk]; ring

section
variable {a b c x : ℝ} (hx1 : -1 < x) (hx2 : x < 1)
include hx1 hx2

private lemma n2_R01 : Rs (qd a b c x) 0 1 = 1 + a * a - 2 * a * x := by
  rw [Rs, n2_qd0, n2_qd1]; simp only [dot, Prod.mk_sub_mk]
  linear_combination a ^ 2 * n2_s_sq hx1 hx2

private lemma n2_R03 : Rs (qd a b c x) 0 3 = 1 + c * c + 2 * c * x := by
  rw [Rs, n2_qd0, n2_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination c ^ 2 * n2_s_sq hx1 hx2

private lemma n2_R12 : Rs (qd a b c x) 1 2 = a * a + b * b + 2 * a * b * x := by
  rw [Rs, n2_qd1, n2_qd2]; simp only [dot, Prod.mk_sub_mk]
  linear_combination a ^ 2 * n2_s_sq hx1 hx2

private lemma n2_R13 : Rs (qd a b c x) 1 3 = (a + c) ^ 2 := by
  rw [Rs, n2_qd1, n2_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination (a + c) ^ 2 * n2_s_sq hx1 hx2

private lemma n2_R23 : Rs (qd a b c x) 2 3 = b * b + c * c - 2 * b * c * x := by
  rw [Rs, n2_qd2, n2_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination c ^ 2 * n2_s_sq hx1 hx2

private lemma n2_P01 : 0 < 1 + a * a - 2 * a * x := by nlinarith [sq_nonneg (a - x)]

private lemma n2_P03 : 0 < 1 + c * c + 2 * c * x := by nlinarith [sq_nonneg (c + x)]

private lemma n2_P12 (hb : 0 < b) : 0 < a * a + b * b + 2 * a * b * x := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith
  nlinarith [sq_nonneg (a + b * x), mul_pos (mul_pos hb hb) h1x]

private lemma n2_P23 (hc : 0 < c) : 0 < b * b + c * c - 2 * b * c * x := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith
  nlinarith [sq_nonneg (b - c * x), mul_pos (mul_pos hc hc) h1x]

end

private lemma n2_wsub (m : Masses) (q : Conf) (i j k l : Fin 4) :
    wgeo m q i j - wgeo m q k l = ss q i j - ss q k l := by
  simp only [wgeo]; ring

private lemma n2_pos_of_mul {mi mj w S : ℝ} (hmi : 0 < mi) (hmj : 0 < mj) (h : mi * mj * w = S)
    (hS : 0 < S) : 0 < w := by
  by_contra hw
  have : mi * mj * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hmi hmj).le (not_lt.mp hw)
  linarith

private lemma n2_neg_of_mul {mi mj w S : ℝ} (hmi : 0 < mi) (hmj : 0 < mj) (h : mi * mj * w = S)
    (hS : S < 0) : w < 0 := by
  by_contra hw
  have : 0 ≤ mi * mj * w := mul_nonneg (mul_pos hmi hmj).le (not_lt.mp hw)
  linarith

/-- the signs `w_12, w_14, w_23, w_34 > 0 > w_13, w_24` and `w_12 w_34 = w_14 w_23 = w_13 w_24` -/
private lemma n2_dz (m : Masses) (hm : ∀ i, 0 < m i) {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1) {σ : ℝ} (hσ : σ < 0)
    (hD : DziobekRel m (qd a b c x) σ) :
    0 < wgeo m (qd a b c x) 0 1 ∧ wgeo m (qd a b c x) 0 2 < 0 ∧
      0 < wgeo m (qd a b c x) 0 3 ∧ 0 < wgeo m (qd a b c x) 1 2 ∧
      wgeo m (qd a b c x) 1 3 < 0 ∧ 0 < wgeo m (qd a b c x) 2 3 ∧
      wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 =
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2 ∧
      wgeo m (qd a b c x) 0 2 * wgeo m (qd a b c x) 1 3 =
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2 := by
  have hs := n2_s_pos hx1 hx2
  have hA0 : 0 < area (qd a b c x) 0 := by rw [n2_area0]; positivity
  have hA1 : area (qd a b c x) 1 < 0 := by
    rw [n2_area1]
    have : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    linarith
  have hA2 : 0 < area (qd a b c x) 2 := by rw [n2_area2]; positivity
  have hA3 : area (qd a b c x) 3 < 0 := by
    rw [n2_area3]
    have : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    linarith
  have e01 := hD 0 1 (by decide)
  have e02 := hD 0 2 (by decide)
  have e03 := hD 0 3 (by decide)
  have e12 := hD 1 2 (by decide)
  have e13 := hD 1 3 (by decide)
  have e23 := hD 2 3 (by decide)
  have hM : 0 < m 0 * m 1 * m 2 * m 3 :=
    mul_pos (mul_pos (mul_pos (hm 0) (hm 1)) (hm 2)) (hm 3)
  refine ⟨n2_pos_of_mul (hm 0) (hm 1) e01
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA0) hA1),
    n2_neg_of_mul (hm 0) (hm 2) e02 (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hσ hA0) hA2),
    n2_pos_of_mul (hm 0) (hm 3) e03
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA0) hA3),
    n2_pos_of_mul (hm 1) (hm 2) e12 (mul_pos (mul_pos_of_neg_of_neg hσ hA1) hA2),
    n2_neg_of_mul (hm 1) (hm 3) e13 (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hσ hA1) hA3),
    n2_pos_of_mul (hm 2) (hm 3) e23
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA2) hA3), ?_, ?_⟩
  · have h : (m 0 * m 1 * m 2 * m 3) * (wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 -
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2) = 0 := by
      linear_combination (m 2 * m 3 * wgeo m (qd a b c x) 2 3) * e01 +
        (σ * area (qd a b c x) 0 * area (qd a b c x) 1) * e23 -
        (m 1 * m 2 * wgeo m (qd a b c x) 1 2) * e03 -
        (σ * area (qd a b c x) 0 * area (qd a b c x) 3) * e12
    have := (mul_eq_zero.mp h).resolve_left hM.ne'
    linarith
  · have h : (m 0 * m 1 * m 2 * m 3) * (wgeo m (qd a b c x) 0 2 * wgeo m (qd a b c x) 1 3 -
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2) = 0 := by
      linear_combination (m 1 * m 3 * wgeo m (qd a b c x) 1 3) * e02 +
        (σ * area (qd a b c x) 0 * area (qd a b c x) 2) * e13 -
        (m 1 * m 2 * wgeo m (qd a b c x) 1 2) * e03 -
        (σ * area (qd a b c x) 0 * area (qd a b c x) 3) * e12
    have := (mul_eq_zero.mp h).resolve_left hM.ne'
    linarith

/-! ## `hd` and the differences of the `w_ij` -/

private lemma n2_hd {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    @hd ℝ opsReal X Y * (X - Y) = 1 / (Y * Real.sqrt Y) - 1 / (X * Real.sqrt X) := by
  obtain ⟨sx, hsx, rfl⟩ : ∃ s, 0 < s ∧ X = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hX, (Real.sq_sqrt hX.le).symm⟩
  obtain ⟨sy, hsy, rfl⟩ : ∃ s, 0 < s ∧ Y = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hY, (Real.sq_sqrt hY.le).symm⟩
  simp only [hd, opsReal_sqrt, Real.sqrt_sq hsx.le, Real.sqrt_sq hsy.le]
  field_simp
  ring

private lemma n2_hDl13 (m : Masses) (a b c x : ℝ) (hb : 0 < b) (hx1 : -1 < x) (hx2 : x < 1) :
    (b * b + 2 * b - a * a + 2 * a * x) * @hd ℝ opsReal (1 + a * a - 2 * a * x) ((1 + b) ^ 2) =
      wgeo m (qd a b c x) 0 1 - wgeo m (qd a b c x) 0 2 := by
  have hY : (0 : ℝ) < (1 + b) ^ 2 := by positivity
  rw [n2_wsub, ss, ss, rr, rr, n2_R01 hx1 hx2, n2_R02]
  linear_combination -(n2_hd (n2_P01 (a := a) hx1 hx2) hY)

private lemma n2_hDl24 (m : Masses) (a b c x : ℝ) (ha : 0 < a) (hc : 0 < c) (hx1 : -1 < x)
    (hx2 : x < 1) :
    (c * c + 2 * a * c - 1 + 2 * a * x) * @hd ℝ opsReal (1 + a * a - 2 * a * x) ((a + c) ^ 2) =
      wgeo m (qd a b c x) 0 1 - wgeo m (qd a b c x) 1 3 := by
  have hY : (0 : ℝ) < (a + c) ^ 2 := by positivity
  rw [n2_wsub, ss, ss, rr, rr, n2_R01 hx1 hx2, n2_R13 hx1 hx2]
  linear_combination -(n2_hd (n2_P01 (a := a) hx1 hx2) hY)

private lemma n2_hE34 (m : Masses) (a b c x : ℝ) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1) :
    ((1 + b) * (1 - b + -(2 * a) * x) + (a + c) * (a - c + 2 * b * x)) *
        @hd ℝ opsReal (b * b + c * c - 2 * b * c * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 2 3 - wgeo m (qd a b c x) 0 1 := by
  rw [n2_wsub, ss, ss, rr, rr, n2_R23 hx1 hx2, n2_R01 hx1 hx2]
  linear_combination -(n2_hd (n2_P23 (b := b) hx1 hx2 hc) (n2_P01 (a := a) hx1 hx2))

private lemma n2_hE14 (m : Masses) (a b c x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    (a + c) * (a - c + -2 * x) *
        @hd ℝ opsReal (1 + c * c + 2 * c * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 0 3 - wgeo m (qd a b c x) 0 1 := by
  rw [n2_wsub, ss, ss, rr, rr, n2_R03 hx1 hx2, n2_R01 hx1 hx2]
  linear_combination -(n2_hd (n2_P03 (c := c) hx1 hx2) (n2_P01 (a := a) hx1 hx2))

private lemma n2_hE23 (m : Masses) (a b c x : ℝ) (hb : 0 < b) (hx1 : -1 < x) (hx2 : x < 1) :
    (1 + b) * (1 - b + -(2 * a) * x) *
        @hd ℝ opsReal (a * a + b * b + 2 * a * b * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 1 2 - wgeo m (qd a b c x) 0 1 := by
  rw [n2_wsub, ss, ss, rr, rr, n2_R12 hx1 hx2, n2_R01 hx1 hx2]
  linear_combination -(n2_hd (n2_P12 (a := a) hx1 hx2 hb) (n2_P01 (a := a) hx1 hx2))

/-! ## the algebra of the `w_ij` under Dziobek's relations -/

private lemma n2_walg {W01 W02 W03 W12 W13 W23 : ℝ} (h01 : 0 < W01) (h02 : W02 < 0)
    (h13 : W13 < 0) (hp1 : W01 * W23 = W03 * W12) (hp2 : W02 * W13 = W03 * W12) :
    (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W01 ∧
    (W23 - W01 + (W01 - W02)) * (W23 - W01 + (W01 - W13)) /
      (W01 - W02 + (W23 - W01) + (W01 - W13)) = W23 ∧
    -((W01 - W02) * (W23 - W01 + (W01 - W02))) / (W01 - W02 + (W23 - W01) + (W01 - W13)) =
      W02 ∧
    -((W01 - W13) * (W23 - W01 + (W01 - W13))) / (W01 - W02 + (W23 - W01) + (W01 - W13)) =
      W13 ∧
    W03 - W01 + (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W03 ∧
    W12 - W01 + (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W12 := by
  have key : (W01 - W02) * (W01 - W13) = W01 * (W01 - W02 + (W23 - W01) + (W01 - W13)) := by
    linear_combination hp2 - hp1
  have hden : W01 - W02 + (W23 - W01) + (W01 - W13) ≠ 0 := by
    intro h
    rw [h, mul_zero] at key
    have : 0 < (W01 - W02) * (W01 - W13) := mul_pos (by linarith) (by linarith)
    linarith
  have q12 : (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W01 := by
    rw [div_eq_iff hden]; linear_combination hp2 - hp1
  refine ⟨q12, ?_, ?_, ?_, by rw [q12]; ring, by rw [q12]; ring⟩ <;>
    rw [div_eq_iff hden] <;> linear_combination hp2 - hp1

/-! ## the certificate quantities of a configuration, edge by edge -/

private lemma n2_Dgeo (m : Masses) (q : Conf) (i j : Fin 4) :
    Dgeo m q i j = -(wgeo m q i j * Rs q i j * rr q i j) / (3 * (area q i * area q j)) := by
  rw [Dgeo, ss, show 3 * (1 / (Rs q i j * rr q i j)) * area q i * area q j =
    3 * (area q i * area q j) / (Rs q i j * rr q i j) by ring, div_div_eq_mul_div]
  ring

/-! ## the weights `d_e = D_e τ_e²` and `|M₂ u|²` -/

/-- `D_e τ_e² = -w_e A_i A_j R_e² r_e / 3` -/
private lemma n2_dtau (m : Masses) (q : Conf) (i j : Fin 4) (hA : area q i * area q j ≠ 0) :
    Dgeo m q i j * taugeo q i j ^ 2 =
      -(wgeo m q i j * (area q i * area q j) * Rs q i j ^ 2 * rr q i j) / 3 := by
  have hR : 0 ≤ Rs q i j := by
    unfold Rs dot
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hr : rr q i j ^ 2 = Rs q i j := Real.sq_sqrt hR
  rw [n2_Dgeo]
  unfold taugeo
  rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero three_ne_zero hA) three_ne_zero]
  linear_combination (-3 * wgeo m q i j * (area q i * area q j) ^ 2 * Rs q i j * rr q i j) * hr

/-- **The weights at a central configuration.**  At a point of `𝒞` with Dziobek's relations and
`σ < 0`, the weights `d_e = D_e τ_e²` of `qd a b c x` are `λ` times the weights `d'_e` of `dirMid`
(and of `dirMidN`), with `λ = s² / (12 den) > 0`, `s = √(1 - x²)`, `den > 0`. -/
theorem nf2_weights (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ) (hC : InC a b c x) (σ : ℝ)
    (hσ : σ < 0) (hD : DziobekRel m (qd a b c x) σ) (vx ve : ℝ) :
    ∃ lam den : ℝ, 0 < lam ∧ 0 < den ∧ Real.sqrt (1 - x ^ 2) ^ 2 = 12 * lam * den ∧
      (@dirArgs ℝ opsReal vx ve a b c x).G = den * ((1 + b) * (a + c)) ^ 2 ∧
      Dgeo m (qd a b c x) 0 1 * taugeo (qd a b c x) 0 1 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d12 ∧
      Dgeo m (qd a b c x) 0 2 * taugeo (qd a b c x) 0 2 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d13 ∧
      Dgeo m (qd a b c x) 0 3 * taugeo (qd a b c x) 0 3 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d14 ∧
      Dgeo m (qd a b c x) 1 2 * taugeo (qd a b c x) 1 2 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d23 ∧
      Dgeo m (qd a b c x) 1 3 * taugeo (qd a b c x) 1 3 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d24 ∧
      Dgeo m (qd a b c x) 2 3 * taugeo (qd a b c x) 2 3 ^ 2 =
        lam * (@dirArgs ℝ opsReal vx ve a b c x).d34 := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := hC
  have hs := n2_s_pos hx1 hx2
  have hs2 := n2_s_sq hx1 hx2
  obtain ⟨hw01, hw02, hw03, hw12, hw13, hw23, hp1, hp2⟩ := n2_dz m hm ha hb hc hx1 hx2 hσ hD
  have hDl13 := n2_hDl13 m a b c x hb hx1 hx2
  have hDl24 := n2_hDl24 m a b c x ha hc hx1 hx2
  have hE34 := n2_hE34 m a b c x hc hx1 hx2
  have hE14 := n2_hE14 m a b c x hx1 hx2
  have hE23 := n2_hE23 m a b c x hb hx1 hx2
  -- `hd` as `hdr` with the roots of `dirMid`, exact for `R₁₃ = (1 + b)²`, `R₂₄ = (a + c)²`
  have e13 : Real.sqrt ((1 + b) ^ 2) = 1 + b := Real.sqrt_sq (by linarith)
  have e24 : Real.sqrt ((a + c) ^ 2) = a + c := Real.sqrt_sq (by linarith)
  rw [show @hd ℝ opsReal (1 + a * a - 2 * a * x) ((1 + b) ^ 2) =
      @hdr ℝ opsReal (1 + a * a - 2 * a * x) (Real.sqrt (1 + a * a - 2 * a * x)) ((1 + b) ^ 2)
        (1 + b) by simp only [hd, hdr, opsReal_sqrt, e13]] at hDl13
  rw [show @hd ℝ opsReal (1 + a * a - 2 * a * x) ((a + c) ^ 2) =
      @hdr ℝ opsReal (1 + a * a - 2 * a * x) (Real.sqrt (1 + a * a - 2 * a * x)) ((a + c) ^ 2)
        (a + c) by simp only [hd, hdr, opsReal_sqrt, e24]] at hDl24
  rw [show @hd ℝ opsReal (b * b + c * c - 2 * b * c * x) (1 + a * a - 2 * a * x) =
      @hdr ℝ opsReal (b * b + c * c - 2 * b * c * x) (Real.sqrt (b * b + c * c - 2 * b * c * x))
        (1 + a * a - 2 * a * x) (Real.sqrt (1 + a * a - 2 * a * x)) from rfl] at hE34
  rw [show @hd ℝ opsReal (1 + c * c + 2 * c * x) (1 + a * a - 2 * a * x) =
      @hdr ℝ opsReal (1 + c * c + 2 * c * x) (Real.sqrt (1 + c * c + 2 * c * x))
        (1 + a * a - 2 * a * x) (Real.sqrt (1 + a * a - 2 * a * x)) from rfl] at hE14
  rw [show @hd ℝ opsReal (a * a + b * b + 2 * a * b * x) (1 + a * a - 2 * a * x) =
      @hdr ℝ opsReal (a * a + b * b + 2 * a * b * x) (Real.sqrt (a * a + b * b + 2 * a * b * x))
        (1 + a * a - 2 * a * x) (Real.sqrt (1 + a * a - 2 * a * x)) from rfl] at hE23
  -- the areas
  have hA0 : area (qd a b c x) 0 ≠ 0 := by rw [n2_area0]; positivity
  have hA1 : area (qd a b c x) 1 ≠ 0 := by
    rw [n2_area1]
    have : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    intro h; linarith
  have hA2 : area (qd a b c x) 2 ≠ 0 := by rw [n2_area2]; positivity
  have hA3 : area (qd a b c x) 3 ≠ 0 := by
    rw [n2_area3]
    have : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    intro h; linarith
  have t01 := n2_dtau m (qd a b c x) 0 1 (mul_ne_zero hA0 hA1)
  have t02 := n2_dtau m (qd a b c x) 0 2 (mul_ne_zero hA0 hA2)
  have t03 := n2_dtau m (qd a b c x) 0 3 (mul_ne_zero hA0 hA3)
  have t12 := n2_dtau m (qd a b c x) 1 2 (mul_ne_zero hA1 hA2)
  have t13 := n2_dtau m (qd a b c x) 1 3 (mul_ne_zero hA1 hA3)
  have t23 := n2_dtau m (qd a b c x) 2 3 (mul_ne_zero hA2 hA3)
  rw [rr, n2_R01 hx1 hx2, n2_area0, n2_area1] at t01
  rw [rr, n2_R02, e13, n2_area0, n2_area2] at t02
  rw [rr, n2_R03 hx1 hx2, n2_area0, n2_area3] at t03
  rw [rr, n2_R12 hx1 hx2, n2_area1, n2_area2] at t12
  rw [rr, n2_R13 hx1 hx2, e24, n2_area1, n2_area3] at t13
  rw [rr, n2_R23 hx1 hx2, n2_area2, n2_area3] at t23
  -- name the `w_e` and `s`
  generalize wgeo m (qd a b c x) 0 1 = W01 at *
  generalize wgeo m (qd a b c x) 0 2 = W02 at *
  generalize wgeo m (qd a b c x) 0 3 = W03 at *
  generalize wgeo m (qd a b c x) 1 2 = W12 at *
  generalize wgeo m (qd a b c x) 1 3 = W13 at *
  generalize wgeo m (qd a b c x) 2 3 = W23 at *
  -- Dziobek's relations: `den w_e` is the polynomial of `dirMid` in the `hd`-blocks
  have hden : 0 < W01 - W02 + (W23 - W01) + (W01 - W13) := by linarith
  have w12 : (W01 - W02) * (W01 - W13) = (W01 - W02 + (W23 - W01) + (W01 - W13)) * W01 := by
    linear_combination hp2 - hp1
  have w34 : (W23 - W01 + (W01 - W02)) * (W23 - W01 + (W01 - W13)) =
      (W01 - W02 + (W23 - W01) + (W01 - W13)) * W23 := by
    linear_combination hp2 - hp1
  have w13 : (W01 - W02) * (W23 - W01 + (W01 - W02)) =
      -((W01 - W02 + (W23 - W01) + (W01 - W13)) * W02) := by
    linear_combination hp1 - hp2
  have w24 : (W01 - W13) * (W23 - W01 + (W01 - W13)) =
      -((W01 - W02 + (W23 - W01) + (W01 - W13)) * W13) := by
    linear_combination hp1 - hp2
  have w14 : (W01 - W02 + (W23 - W01) + (W01 - W13)) * (W03 - W01) + (W01 - W02) * (W01 - W13) =
      (W01 - W02 + (W23 - W01) + (W01 - W13)) * W03 := by
    linear_combination hp2 - hp1
  have w23 : (W01 - W02 + (W23 - W01) + (W01 - W13)) * (W12 - W01) + (W01 - W02) * (W01 - W13) =
      (W01 - W02 + (W23 - W01) + (W01 - W13)) * W12 := by
    linear_combination hp2 - hp1
  generalize hden_def : W01 - W02 + (W23 - W01) + (W01 - W13) = den at *
  -- the inputs of `midT`
  set A := @dirArgs ℝ opsReal vx ve a b c x with hA
  have fG : A.G = den * ((1 + b) * (a + c)) ^ 2 := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hDl24, hE34, hden_def]
  have fd12 : A.d12 = (W01 - W02) * (W01 - W13) * (b * c * ((1 + b) * (a + c))) *
      ((1 + a * a - 2 * a * x) ^ 2 * Real.sqrt (1 + a * a - 2 * a * x)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hDl24]
  have fd13 : A.d13 = (W01 - W02) * (W23 - W01 + (W01 - W02)) * (b * (a + c) ^ 2) *
      (((1 + b) ^ 2) ^ 2 * (1 + b)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hE34]
  have fd14 : A.d14 = (den * (W03 - W01) + (W01 - W02) * (W01 - W13)) *
      (a * b * ((1 + b) * (a + c))) *
      ((1 + c * c + 2 * c * x) ^ 2 * Real.sqrt (1 + c * c + 2 * c * x)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hDl24, hE34, hE14, hden_def]
  have fd23 : A.d23 = (den * (W12 - W01) + (W01 - W02) * (W01 - W13)) *
      (c * ((1 + b) * (a + c))) *
      ((a * a + b * b + 2 * a * b * x) ^ 2 * Real.sqrt (a * a + b * b + 2 * a * b * x)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hDl24, hE34, hE23, hden_def]
  have fd24 : A.d24 = (W01 - W13) * (W23 - W01 + (W01 - W13)) * (a * c * (1 + b) ^ 2) *
      (((a + c) ^ 2) ^ 2 * (a + c)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl24, hE34]
  have fd34 : A.d34 = (W23 - W01 + (W01 - W02)) * (W23 - W01 + (W01 - W13)) *
      (a * ((1 + b) * (a + c))) *
      ((b * b + c * c - 2 * b * c * x) ^ 2 * Real.sqrt (b * b + c * c - 2 * b * c * x)) := by
    simp only [hA, dirArgs, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
    push_cast
    rw [hDl13, hDl24, hE34]
  -- `λ = s² / (12 den)`
  generalize hs_def : Real.sqrt (1 - x ^ 2) = s at *
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = s ^ 2 / (12 * den) := ⟨_, rfl⟩
  have hlam' : s ^ 2 = 12 * lam * den := by
    rw [hlam]
    field_simp
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have s01 : Dgeo m (qd a b c x) 0 1 * taugeo (qd a b c x) 0 1 ^ 2 = lam * A.d12 := by
    rw [t01, fd12, w12]
    linear_combination (W01 * (b * c * ((1 + b) * (a + c))) *
      ((1 + a * a - 2 * a * x) ^ 2 * Real.sqrt (1 + a * a - 2 * a * x)) / 12) * hlam'
  have s02 : Dgeo m (qd a b c x) 0 2 * taugeo (qd a b c x) 0 2 ^ 2 = lam * A.d13 := by
    rw [t02, fd13, w13]
    linear_combination (-(W02 * (b * (a + c) ^ 2) * (((1 + b) ^ 2) ^ 2 * (1 + b))) / 12) * hlam'
  have s03 : Dgeo m (qd a b c x) 0 3 * taugeo (qd a b c x) 0 3 ^ 2 = lam * A.d14 := by
    rw [t03, fd14, w14]
    linear_combination (W03 * (a * b * ((1 + b) * (a + c))) *
      ((1 + c * c + 2 * c * x) ^ 2 * Real.sqrt (1 + c * c + 2 * c * x)) / 12) * hlam'
  have s12 : Dgeo m (qd a b c x) 1 2 * taugeo (qd a b c x) 1 2 ^ 2 = lam * A.d23 := by
    rw [t12, fd23, w23]
    linear_combination (W12 * (c * ((1 + b) * (a + c))) *
      ((a * a + b * b + 2 * a * b * x) ^ 2 * Real.sqrt (a * a + b * b + 2 * a * b * x)) / 12) *
      hlam'
  have s13 : Dgeo m (qd a b c x) 1 3 * taugeo (qd a b c x) 1 3 ^ 2 = lam * A.d24 := by
    rw [t13, fd24, w24]
    linear_combination (-(W13 * (a * c * (1 + b) ^ 2) * (((a + c) ^ 2) ^ 2 * (a + c))) / 12) * hlam'
  have s23 : Dgeo m (qd a b c x) 2 3 * taugeo (qd a b c x) 2 3 ^ 2 = lam * A.d34 := by
    rw [t23, fd34, w34]
    linear_combination (W23 * (a * ((1 + b) * (a + c))) *
      ((b * b + c * c - 2 * b * c * x) ^ 2 * Real.sqrt (b * b + c * c - 2 * b * c * x)) / 12) *
      hlam'
  exact ⟨lam, den, hlam0, hden, hlam', fG, s01, s02, s03, s12, s13, s23⟩

/-! ## `P` with shared roots -/

/-- `hd X Y = hdr X √X Y √Y` -/
theorem hd_eq_hdr (X Y : ℝ) :
    @hd ℝ opsReal X Y = @hdr ℝ opsReal X (Real.sqrt X) Y (Real.sqrt Y) := rfl

/-- `dirP2 = dirP` at `ℝ`: `dirP2` takes the roots `r₁₃ = 1 + b` and `r₂₄ = a + c` exactly -/
theorem dirP2_eq {a b c x : ℝ} (hb : 0 ≤ 1 + b) (hac : 0 ≤ a + c) :
    @dirP2 ℝ opsReal a b c x = dirPR a b c x := by
  have e13 : Real.sqrt ((1 + b) ^ 2) = 1 + b := Real.sqrt_sq hb
  have e24 : Real.sqrt ((a + c) ^ 2) = a + c := Real.sqrt_sq hac
  simp only [dirP2, dirPR, dirP, hd_eq_hdr, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
  push_cast
  simp only [e13, e24]

end

/-! ## the normalized test `dirMidN` -/

noncomputable section

/-- the quadratic form `Y[z] = z₁² + s2 z₂² - Σ_e d_e ⟨A (u_e - ū), z⟩² / F` of the inputs, with
`ū = Σ_e d_e u_e / Σ_e d_e` -/
def YIn.QY (A : YIn ℝ) (z1 z2 : ℝ) : ℝ :=
  let iW := 1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)
  let mx := (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x +
    A.d24 * A.u24x + A.d34 * A.u34x) * iW
  let me := ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e +
    A.d24 * A.u24e) * iW
  let y := fun ux ue : ℝ =>
    (A.Axx * (ux - mx) + A.Axe * (ue - me)) * z1 + (A.Axe * (ux - mx) + A.Aee * (ue - me)) * z2
  z1 ^ 2 + A.s2 * z2 ^ 2 -
    (A.d12 * y A.u12x A.u12e ^ 2 + A.d13 * y A.u13x A.u13e ^ 2 + A.d14 * y A.u14x A.u14e ^ 2 +
      A.d23 * y A.u23x A.u12e ^ 2 + A.d24 * y A.u24x A.u24e ^ 2 + A.d34 * y A.u34x A.u14e ^ 2) *
      (1 / A.F)

/-- `det Y > 0` and `tr Y > 0` give `Y[z] > 0` for `z ≠ 0` -/
theorem midY_pos (A : YIn ℝ) (h1 : 0 < (@YIn.Y ℝ opsReal A).1)
    (h2 : 0 < (@YIn.Y ℝ opsReal A).2) {z1 z2 : ℝ} (hz : z1 ≠ 0 ∨ z2 ≠ 0) :
    0 < A.QY z1 z2 := by
  simp only [YIn.Y, midY, zz, opsReal_sq, opsReal_ofNat] at h1 h2
  push_cast at h1 h2
  have hz' : z1 ≠ 0 ∨ -z2 ≠ 0 := hz.imp id fun h => neg_ne_zero.mpr h
  have h := quad_pos h1 h2 hz'
  convert h using 1
  simp only [YIn.QY]
  ring

/-- the quadratic form through a vector `w` with `⟨A v, w⟩ = κ ⟨v, z⟩`:
`W Y[w] = W (w₁² + s2 w₂²) - (κ² / F) (W Σ_e d_e ⟨u_e, z⟩² - (Σ_e d_e ⟨u_e, z⟩)²)` -/
theorem QY_eq (A : YIn ℝ) (z1 z2 w1 w2 κ : ℝ)
    (hW : A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34 ≠ 0)
    (hAw : ∀ v1 v2 : ℝ, (A.Axx * v1 + A.Axe * v2) * w1 + (A.Axe * v1 + A.Aee * v2) * w2 =
      κ * (v1 * z1 + v2 * z2)) :
    (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) * A.QY w1 w2 =
      (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) * (w1 ^ 2 + A.s2 * w2 ^ 2) -
        κ ^ 2 * (1 / A.F) *
          ((A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) *
              (A.d12 * (A.u12x * z1 + A.u12e * z2) ^ 2 + A.d13 * (A.u13x * z1 + A.u13e * z2) ^ 2 +
                A.d14 * (A.u14x * z1 + A.u14e * z2) ^ 2 + A.d23 * (A.u23x * z1 + A.u12e * z2) ^ 2 +
                A.d24 * (A.u24x * z1 + A.u24e * z2) ^ 2 + A.d34 * (A.u34x * z1 + A.u14e * z2) ^ 2) -
            (A.d12 * (A.u12x * z1 + A.u12e * z2) + A.d13 * (A.u13x * z1 + A.u13e * z2) +
                A.d14 * (A.u14x * z1 + A.u14e * z2) + A.d23 * (A.u23x * z1 + A.u12e * z2) +
                A.d24 * (A.u24x * z1 + A.u24e * z2) + A.d34 * (A.u34x * z1 + A.u14e * z2)) ^ 2) :=
                    by
  simp only [YIn.QY, hAw]
  field_simp
  ring

/-- `|M₂ u|² = (s² / 4) (w₁² + s² w₂²)` with `w = k N (u₁, s u₂)` -/
private lemma n2_M2sqN (a b c x : ℝ) (u : V2) :
    dot (M2mul (qd a b c x) u) (M2mul (qd a b c x) u) =
      Real.sqrt (1 - x ^ 2) ^ 2 / 4 *
        (((1 + b) * (a + c) * ((b - a * c * x * x) * u.1 -
            a * c * x * (Real.sqrt (1 - x ^ 2) * u.2))) ^ 2 +
          Real.sqrt (1 - x ^ 2) ^ 2 * ((1 + b) * (a + c) * (-(a * c * x) * u.1 -
            a * c * (Real.sqrt (1 - x ^ 2) * u.2))) ^ 2) := by
  simp only [dot, M2mul, M2a, M2b, M2c, Fin.sum_univ_four, n2_qd0, n2_qd1, n2_qd2, n2_qd3,
    n2_area0, n2_area1, n2_area2, n2_area3]
  ring

/-- **The normalized direct test.**  At a point of `𝒞` with Dziobek's relations and `σ < 0`,
`det Y > 0` and `tr Y > 0` (from `dirMidN`) give `T ≻ 0` for the weights `d_e = D_e τ_e²` of
`qd a b c x`: `T[u] = 3 λ² den W Y[k N (u₁, s u₂)]`. -/
theorem nfN_Tform_pos (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ) (hC : InC a b c x) (σ : ℝ)
    (hσ : σ < 0) (hD : DziobekRel m (qd a b c x) σ)
    (hdet : 0 < (@dirMidN ℝ opsReal a b c x).det) (htr : 0 < (@dirMidN ℝ opsReal a b c x).tr)
    (u : V2) (hu : u ≠ 0) :
    0 < Tform (qd a b c x) (fun i j => Dgeo m (qd a b c x) i j * taugeo (qd a b c x) i j ^ 2)
      u := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  have hs := n2_s_pos hx1 hx2
  have hs2 := n2_s_sq hx1 hx2
  obtain ⟨hcf, hconv, -⟩ := qd_props a b c x ha hb hc hx1 hx2
  have hA := convex_area_ne _ hconv
  obtain ⟨lam, den, hlam0, hden, hlam', fG, s01, s02, s03, s12, s13, s23⟩ :=
    nf2_weights m hm a b c x hC σ hσ hD 0 0
  -- the inputs of `midY`; the weights are those of `dirMid`
  set A := @dirYIn ℝ opsReal a b c x with hA_def
  have e12 : (@dirArgs ℝ opsReal 0 0 a b c x).d12 = A.d12 := rfl
  have e13 : (@dirArgs ℝ opsReal 0 0 a b c x).d13 = A.d13 := rfl
  have e14 : (@dirArgs ℝ opsReal 0 0 a b c x).d14 = A.d14 := rfl
  have e23 : (@dirArgs ℝ opsReal 0 0 a b c x).d23 = A.d23 := rfl
  have e24 : (@dirArgs ℝ opsReal 0 0 a b c x).d24 = A.d24 := rfl
  have e34 : (@dirArgs ℝ opsReal 0 0 a b c x).d34 = A.d34 := rfl
  rw [e12] at s01
  rw [e13] at s02
  rw [e14] at s03
  rw [e23] at s12
  rw [e24] at s13
  rw [e34] at s23
  have fF : A.F = den * (-((1 + b) * (a + c) * (a * c) * b)) ^ 2 := by
    have h : A.F = (@dirArgs ℝ opsReal 0 0 a b c x).G * (a * c * b) ^ 2 := by
      simp only [hA_def, dirYIn, dirArgs, opsReal_sq]
      ring
    rw [h, fG]
    ring
  have fs2 : A.s2 = 1 - x ^ 2 := by
    simp only [hA_def, dirYIn, opsReal_sq, opsReal_ofNat]
    push_cast
    ring
  have fA1 : A.Axx = -(a * c) := by simp only [hA_def, dirYIn]
  have fA2 : A.Axe = a * c * x := by simp only [hA_def, dirYIn]
  have fA3 : A.Aee = b - a * c * x * x := by simp only [hA_def, dirYIn]
  have fu1 : A.u12x = 1 + a * x := by simp only [hA_def, dirYIn, opsReal_ofNat]; push_cast; ring
  have fu2 : A.u13x = 1 - b := by simp only [hA_def, dirYIn, opsReal_ofNat]; push_cast; ring
  have fu3 : A.u14x = 1 - c * x := by simp only [hA_def, dirYIn, opsReal_ofNat]; push_cast; ring
  have fu4 : A.u23x = a * x - b := by simp only [hA_def, dirYIn]
  have fu5 : A.u24x = a * x - c * x := by simp only [hA_def, dirYIn]
  have fu6 : A.u34x = -b - c * x := by simp only [hA_def, dirYIn]
  have fu7 : A.u12e = a := by simp only [hA_def, dirYIn]
  have fu8 : A.u13e = 0 := by simp only [hA_def, dirYIn, opsReal_ofNat]; push_cast; ring
  have fu9 : A.u14e = -c := by simp only [hA_def, dirYIn]
  have fu10 : A.u24e = a - c := by simp only [hA_def, dirYIn]
  -- the weights are positive
  have hpos : ∀ i j : Fin 4, i ≠ j → 0 < Dgeo m (qd a b c x) i j * taugeo (qd a b c x) i j ^ 2 :=
    fun i j h => mul_pos (Dgeo_pos m hm _ hcf σ hσ hD hA h) (by
      have := taugeo_ne _ hcf hA h
      positivity)
  have hd12 : 0 < A.d12 := pos_of_mul_pos_right (s01 ▸ hpos 0 1 (by decide)) hlam0.le
  have hd13 : 0 < A.d13 := pos_of_mul_pos_right (s02 ▸ hpos 0 2 (by decide)) hlam0.le
  have hd14 : 0 < A.d14 := pos_of_mul_pos_right (s03 ▸ hpos 0 3 (by decide)) hlam0.le
  have hd23 : 0 < A.d23 := pos_of_mul_pos_right (s12 ▸ hpos 1 2 (by decide)) hlam0.le
  have hd24 : 0 < A.d24 := pos_of_mul_pos_right (s13 ▸ hpos 1 3 (by decide)) hlam0.le
  have hd34 : 0 < A.d34 := pos_of_mul_pos_right (s23 ▸ hpos 2 3 (by decide)) hlam0.le
  have hW : 0 < A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34 := by linarith
  -- the vector `w = k N (u₁, s u₂)`
  have hM := n2_M2sqN a b c x u
  generalize hs_def : Real.sqrt (1 - x ^ 2) = s at *
  have hkpb : (1 + b) * (a + c) * (a * c) * b ≠ 0 := by positivity
  have hw : (1 + b) * (a + c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2)) ≠ 0 ∨
      (1 + b) * (a + c) * (-(a * c * x) * u.1 - a * c * (s * u.2)) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have hk : (1 + b) * (a + c) ≠ 0 := by positivity
    have h1' := (mul_eq_zero.mp h.1).resolve_left hk
    have h2' := (mul_eq_zero.mp h.2).resolve_left hk
    have hu1 : u.1 = 0 := by
      have : b * u.1 = 0 := by linear_combination h1' - x * h2'
      exact (mul_eq_zero.mp this).resolve_left hb.ne'
    have hu2 : u.2 = 0 := by
      have : a * c * s * u.2 = 0 := by linear_combination -h2' - a * c * x * hu1
      exact (mul_eq_zero.mp this).resolve_left (by positivity)
    exact hu (Prod.ext hu1 hu2)
  have hQY := midY_pos A (hdet.trans_eq (@dirMidN_det_eq ℝ opsReal a b c x))
    (htr.trans_eq (@dirMidN_tr_eq ℝ opsReal a b c x)) hw
  have hAw : ∀ v1 v2 : ℝ, (A.Axx * v1 + A.Axe * v2) *
        ((1 + b) * (a + c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2))) +
      (A.Axe * v1 + A.Aee * v2) * ((1 + b) * (a + c) * (-(a * c * x) * u.1 - a * c * (s * u.2))) =
      -((1 + b) * (a + c) * (a * c) * b) * (v1 * u.1 + v2 * (s * u.2)) := by
    intro v1 v2
    rw [fA1, fA2, fA3]
    ring
  have hQYW := QY_eq A u.1 (s * u.2) _ _ _ hW.ne' hAw
  -- `den W Y[w] = den W (w₁² + s2 w₂²) - (W Σ d ⟨u_e, z⟩² - (Σ d ⟨u_e, z⟩)²)`
  have hdQ : den * ((A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) *
        A.QY ((1 + b) * (a + c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2)))
          ((1 + b) * (a + c) * (-(a * c * x) * u.1 - a * c * (s * u.2)))) =
      den * ((A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) *
        (((1 + b) * (a + c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2))) ^ 2 +
          (1 - x ^ 2) * ((1 + b) * (a + c) * (-(a * c * x) * u.1 - a * c * (s * u.2))) ^ 2)) -
      ((A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) *
          (A.d12 * ((1 + a * x) * u.1 + a * (s * u.2)) ^ 2 + A.d13 * ((1 - b) * u.1 + 0 * (s * u.2))
              ^ 2 +
            A.d14 * ((1 - c * x) * u.1 + -c * (s * u.2)) ^ 2 +
            A.d23 * ((a * x - b) * u.1 + a * (s * u.2)) ^ 2 +
            A.d24 * ((a * x - c * x) * u.1 + (a - c) * (s * u.2)) ^ 2 +
            A.d34 * ((-b - c * x) * u.1 + -c * (s * u.2)) ^ 2) -
        (A.d12 * ((1 + a * x) * u.1 + a * (s * u.2)) + A.d13 * ((1 - b) * u.1 + 0 * (s * u.2)) +
            A.d14 * ((1 - c * x) * u.1 + -c * (s * u.2)) +
            A.d23 * ((a * x - b) * u.1 + a * (s * u.2)) +
            A.d24 * ((a * x - c * x) * u.1 + (a - c) * (s * u.2)) +
            A.d34 * ((-b - c * x) * u.1 + -c * (s * u.2))) ^ 2) := by
    rw [hQYW, fF, fs2, fu1, fu2, fu3, fu4, fu5, fu6, fu7, fu8, fu9, fu10]
    field_simp
  -- `T[u] = 3 λ² (den W Y[w])`
  have key : Tform (qd a b c x)
      (fun i j => Dgeo m (qd a b c x) i j * taugeo (qd a b c x) i j ^ 2) u =
      3 * lam ^ 2 * (den * ((A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) * A.QY ((1 + b) * (a +
          c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2))) ((1 + b) * (a + c) * (-(a * c *
          x) * u.1 - a * c * (s * u.2))))) := by
    rw [hdQ]
    simp only [Tform, esum]
    rw [s01, s02, s03, s12, s13, s23, hM]
    simp only [dot, Prod.fst_add, Prod.snd_add, n2_qd0, n2_qd1, n2_qd2, n2_qd3, hs_def]
    linear_combination (lam * (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) / 4 * (((1 + b) * (a +
        c) * ((b - a * c * x * x) * u.1 - a * c * x * (s * u.2))) ^ 2 + s ^ 2 * ((1 + b) * (a + c) *
        (-(a * c * x) * u.1 - a * c * (s * u.2))) ^ 2)) * hlam' +
      (3 * lam ^ 2 * den * (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) * ((1 + b) * (a + c) *
          (-(a * c * x) * u.1 - a * c * (s * u.2))) ^ 2) * hs2
  rw [key]
  exact mul_pos (by positivity) (mul_pos hden (mul_pos hW hQY))

end

end C4
