module

public import C4.NormalForm2

@[expose] public section

/-!
# The normalized midpoint test in the blow-up chart

In the blow-up coordinates `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi` (`b > 0`), the inputs of
`midY` in `chMidN b al ga xi` are those of `dirMidN a b c x` rescaled: the weights by `b`, the
    matrix
`A = adj N` and the scale `F` by `1/b`, with the same `s²` and `u_e`.  Every power of `b` cancels in
`X / F`, so `det Y` and `tr Y` agree exactly (`ch2N_eq`, `ch2N_eq_inC`).

The weights are compared through their atom-level forms `dWOf` and `cWOf`, whose arguments are the
square roots and the `hd`-blocks (`dDl13`, …, `cE34h`): `chYIn` and `dirYIn` reduce to them by
`rfl`, the forms are related by `wOf_rel` (a short polynomial identity), and the blocks by
`c2_bDl13`, …, `c2_bE34` (`h_i = g_i / b`, and `E34h = b³ E34` from
`hd X Y (X - Y) = Y^(-3/2) - X^(-3/2)` with `R₃₄ = b² ρ²`).

* `YIn.ent`: the entries of `Y` as computed by `midY` (`YIn.Y_ent`, `rfl`), for the inputs
  `chYIn`, `dirYIn` of `chMidN`, `dirMidN` (`C4Check.Formulas2`);
* `ent_scale`: the entries do not change under `d ↦ b d`, `A ↦ A / b`, `F ↦ F / b`;
* `ch2N_eq`, `ch2N_eq_inC`: `chMidN` at the chart point has the `det` and `tr` of `dirMidN`;
* `chP2_eq`: `chP2 = chP` at `ℝ`.
-/

namespace C4

section
variable {α : Type} [Ops α]

/-- the entries `(Y₁₁, X₁₂, Y₂₂)` computed by `midY` (`Y₁₂ = -X₁₂`) -/
def YIn.ent (A : YIn α) : α × α × α :=
  let iW := 1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)
  let mx := (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x +
    A.d24 * A.u24x + A.d34 * A.u34x) * iW
  let me := ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e +
    A.d24 * A.u24e) * iW
  let z12 := zz A.Axx A.Axe A.Aee A.d12 (A.u12x - mx) (A.u12e - me)
  let z13 := zz A.Axx A.Axe A.Aee A.d13 (A.u13x - mx) (A.u13e - me)
  let z14 := zz A.Axx A.Axe A.Aee A.d14 (A.u14x - mx) (A.u14e - me)
  let z23 := zz A.Axx A.Axe A.Aee A.d23 (A.u23x - mx) (A.u12e - me)
  let z24 := zz A.Axx A.Axe A.Aee A.d24 (A.u24x - mx) (A.u24e - me)
  let z34 := zz A.Axx A.Axe A.Aee A.d34 (A.u34x - mx) (A.u14e - me)
  let iF := 1 / A.F
  (1 - (z12.1 + z13.1 + z14.1 + z23.1 + z24.1 + z34.1) * iF,
    (z12.2.1 + z13.2.1 + z14.2.1 + z23.2.1 + z24.2.1 + z34.2.1) * iF,
    A.s2 - (z12.2.2 + z13.2.2 + z14.2.2 + z23.2.2 + z24.2.2 + z34.2.2) * iF)

theorem YIn.Y_ent (A : YIn α) :
    A.Y = (A.ent.1 * A.ent.2.2 - Ops.sq A.ent.2.1, A.ent.1 + A.ent.2.2) := rfl

/-! The square roots and the `hd`-blocks of `dirMidN` (`d…`) and `chMidN` (`c…`). -/

def dr12 (a x : α) : α := Ops.sqrt (1 + a * a - 2 * a * x)
def dr14 (c x : α) : α := Ops.sqrt (1 + c * c + 2 * c * x)
def dr23 (a b x : α) : α := Ops.sqrt (a * a + b * b + 2 * a * b * x)
def dr34 (b c x : α) : α := Ops.sqrt (b * b + c * c - 2 * b * c * x)
def cr12 (b al xi : α) : α := Ops.sqrt (1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi)))
def cr14 (b ga xi : α) : α := Ops.sqrt (1 + b * (ga * (b * ga + 2 * (1 / 2 + b * xi))))
def cr23 (b al xi : α) : α :=
  Ops.sqrt (1 + b * (2 * al + b * Ops.sq al + 2 * (1 / 2 + b * xi) * (1 + b * al) + b))
def crho (b ga xi : α) : α := Ops.sqrt (1 - 2 * ga * (1 / 2 + b * xi) + Ops.sq ga)

def dDl13 (a b c x : α) : α :=
  (dirG a b c x).x1 * hdr (1 + a * a - 2 * a * x) (dr12 a x) (Ops.sq (1 + b)) (1 + b)
def dDl24 (a b c x : α) : α :=
  (dirG a b c x).x2 * hdr (1 + a * a - 2 * a * x) (dr12 a x) (Ops.sq (a + c)) (a + c)
def dE34 (a b c x : α) : α :=
  ((1 + b) * (dirG a b c x).x4 + (a + c) * (dirG a b c x).x5) *
    hdr (b * b + c * c - 2 * b * c * x) (dr34 b c x) (1 + a * a - 2 * a * x) (dr12 a x)
def dE14 (a b c x : α) : α :=
  (a + c) * (dirG a b c x).x3 * hdr (1 + c * c + 2 * c * x) (dr14 c x) (1 + a * a - 2 * a * x)
    (dr12 a x)
def dE23 (a b c x : α) : α :=
  (1 + b) * (dirG a b c x).x4 * hdr (a * a + b * b + 2 * a * b * x) (dr23 a b x)
    (1 + a * a - 2 * a * x) (dr12 a x)

def cDl13 (b al ga xi : α) : α :=
  (chG b al ga xi).x1 * hdr (1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi)))
    (cr12 b al xi) (Ops.sq (1 + b)) (1 + b)
def cDl24 (b al ga xi : α) : α :=
  (chG b al ga xi).x2 * hdr (1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi)))
    (cr12 b al xi) (Ops.sq (1 + b * al + b * ga)) (1 + b * al + b * ga)
def cE14 (b al ga xi : α) : α :=
  (1 + b * al + b * ga) * (chG b al ga xi).x3 *
    hdr (1 + b * (ga * (b * ga + 2 * (1 / 2 + b * xi)))) (cr14 b ga xi)
      (1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))) (cr12 b al xi)
def cE23 (b al ga xi : α) : α :=
  (1 + b) * (chG b al ga xi).x4 *
    hdr (1 + b * (2 * al + b * Ops.sq al + 2 * (1 / 2 + b * xi) * (1 + b * al) + b))
      (cr23 b al xi) (1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))) (cr12 b al xi)
def cE34h (b al ga xi : α) : α :=
  1 / ((1 - 2 * ga * (1 / 2 + b * xi) + Ops.sq ga) * crho b ga xi) -
    b * b * b / ((1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))) * cr12 b al xi)

/-- the six weights of `dirMidN` in terms of the roots and the `hd`-blocks -/
def dWOf (a b c x r12 r14 r23 r34 Dl13 Dl24 E34 E14 E23 : α) : Six α :=
  let R12 := 1 + a * a - 2 * a * x
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R34 := b * b + c * c - 2 * b * c * x
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let den := Dl13 + E34 + Dl24
  let P12 := Dl13 * Dl24
  let k := r13 * r24
  ⟨P12 * (b * c * k) * (Ops.sq R12 * r12),
    Dl13 * (E34 + Dl13) * (b * R24) * (Ops.sq R13 * r13),
    (den * E14 + P12) * (a * b * k) * (Ops.sq R14 * r14),
    (den * E23 + P12) * (c * k) * (Ops.sq R23 * r23),
    Dl24 * (E34 + Dl24) * (a * c * R13) * (Ops.sq R24 * r24),
    (E34 + Dl13) * (E34 + Dl24) * (a * k) * (Ops.sq R34 * r34)⟩

/-- the six weights of `chMidN` in terms of the roots and the `hd`-blocks -/
def cWOf (b al ga xi r12 r14 r23 rho Dl13 Dl24 E14 E23 E34h : α) : Six α :=
  let x := 1 / 2 + b * xi
  let a := 1 + b * al
  let c := b * ga
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let b4 := Ops.sq (Ops.sq b)
  let denh := E34h + b4 * (Dl13 + Dl24)
  let P12 := Dl13 * Dl24
  let D1 := E34h + b4 * Dl13
  let D2 := E34h + b4 * Dl24
  let k := r13 * r24
  ⟨b4 * b * P12 * (ga * k) * (Ops.sq R12 * r12),
    Dl13 * D1 * R24 * (Ops.sq R13 * r13),
    (denh * E14 + b4 * P12) * (a * k) * (Ops.sq R14 * r14),
    (denh * E23 + b4 * P12) * (ga * k) * (Ops.sq R23 * r23),
    Dl24 * D2 * (a * ga * R13) * (Ops.sq R24 * r24),
    D1 * D2 * (a * k) * (Ops.sq rho2 * rho)⟩

/-- the scale `F` of `dirMidN` in terms of the `hd`-blocks -/
def dFOf (a b c Dl13 Dl24 E34 : α) : α :=
  (Dl13 + E34 + Dl24) * Ops.sq ((1 + b) * (a + c) * (a * c) * b)

/-- the scale `F` of `chMidN` in terms of the `hd`-blocks -/
def cFOf (b al ga Dl13 Dl24 E34h : α) : α :=
  (E34h + Ops.sq (Ops.sq b) * (Dl13 + Dl24)) *
    Ops.sq ((1 + b) * (1 + b * al + b * ga) * ((1 + b * al) * ga))

theorem dirYIn_w (a b c x : α) :
    (dirYIn a b c x).d12 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x1 ∧
    (dirYIn a b c x).d13 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x2 ∧
    (dirYIn a b c x).d14 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x3 ∧
    (dirYIn a b c x).d23 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x4 ∧
    (dirYIn a b c x).d24 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x5 ∧
    (dirYIn a b c x).d34 = (dWOf a b c x (dr12 a x) (dr14 c x) (dr23 a b x) (dr34 b c x) (dDl13 a b
        c x) (dDl24 a b c x) (dE34 a b c x) (dE14 a b c x) (dE23 a b c x)).x6 ∧
    (dirYIn a b c x).F = dFOf a b c (dDl13 a b c x) (dDl24 a b c x) (dE34 a b c x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem chYIn_w (b al ga xi : α) :
    (chYIn b al ga xi).d12 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x1 ∧
    (chYIn b al ga xi).d13 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x2 ∧
    (chYIn b al ga xi).d14 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x3 ∧
    (chYIn b al ga xi).d23 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x4 ∧
    (chYIn b al ga xi).d24 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x5 ∧
    (chYIn b al ga xi).d34 = (cWOf b al ga xi (cr12 b al xi) (cr14 b ga xi) (cr23 b al xi) (crho b
        ga xi) (cDl13 b al ga xi) (cDl24 b al ga xi) (cE14 b al ga xi) (cE23 b al ga xi) (cE34h b al
        ga xi)).x6 ∧
    (chYIn b al ga xi).F =
      cFOf b al ga (cDl13 b al ga xi) (cDl24 b al ga xi) (cE34h b al ga xi) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

noncomputable section

/-! The point `(1 + b al, b, b ga, 1/2 + b xi)`: its squared distances and two constraints, as they
appear after unfolding (`ᵈ` direct, `ᶜ` chart).  The notations are unhygienic: `b`, `al`, `ga`, `xi`
are the variables in scope. -/

set_option hygiene false in
local notation "R₁₂ᵈ" => (1 + (1 + b * al) * (1 + b * al) - 2 * (1 + b * al) * (1 / 2 + b * xi))

set_option hygiene false in
local notation "R₁₄ᵈ" => (1 + b * ga * (b * ga) + 2 * (b * ga) * (1 / 2 + b * xi))

set_option hygiene false in
local notation "R₂₃ᵈ" => ((1 + b * al) * (1 + b * al) + b * b + 2 * (1 + b * al) * b * (1 / 2 + b *
    xi))

set_option hygiene false in
local notation "R₃₄ᵈ" => (b * b + b * ga * (b * ga) - 2 * b * (b * ga) * (1 / 2 + b * xi))

set_option hygiene false in
local notation "R₁₂ᶜ" => (1 + b * (al - 2 * xi + b * (al ^ 2 - 2 * al * xi)))

set_option hygiene false in
local notation "R₁₄ᶜ" => (1 + b * (ga * (b * ga + 2 * (1 / 2 + b * xi))))

set_option hygiene false in
local notation "R₂₃ᶜ" => (1 + b * (2 * al + b * al ^ 2 + 2 * (1 / 2 + b * xi) * (1 + b * al) + b))

set_option hygiene false in
local notation "ρ₂ᶜ" => (1 - 2 * ga * (1 / 2 + b * xi) + ga ^ 2)

set_option hygiene false in
local notation "g₄ᵈ" => (1 - b + -(2 * (1 + b * al)) * (1 / 2 + b * xi))

set_option hygiene false in
local notation "g₅ᵈ" => (1 + b * al - b * ga + 2 * b * (1 / 2 + b * xi))

/-! ## the atom-level relations -/

/-- the weights of `chMidN` are `b` times those of `dirMidN`, in terms of the blocks -/
theorem wOf_rel {b : ℝ} (hb : b ≠ 0) (al ga xi r12 r14 r23 rho Dl13 Dl24 E34 E14 E23 : ℝ) :
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x1 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x1 ∧
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x2 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x2 ∧
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x3 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x3 ∧
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x4 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x4 ∧
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x5 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x5 ∧
    (@cWOf ℝ opsReal b al ga xi r12 r14 r23 rho (Dl13 / b) (Dl24 / b) (E14 / b) (E23 / b) (b ^ 3 *
        E34)).x6 = b * (@dWOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) r12 r14 r23 (b *
        rho) Dl13 Dl24 E34 E14 E23).x6 := by
  simp only [cWOf, dWOf, opsReal_sq, opsReal_ofNat]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- the scale of `chMidN` is that of `dirMidN` divided by `b`, in terms of the blocks -/
theorem fOf_rel {b : ℝ} (hb : b ≠ 0) (al ga Dl13 Dl24 E34 : ℝ) :
    @cFOf ℝ opsReal b al ga (Dl13 / b) (Dl24 / b) (b ^ 3 * E34) =
      @dFOf ℝ opsReal (1 + b * al) b (b * ga) Dl13 Dl24 E34 / b := by
  simp only [cFOf, dFOf, opsReal_sq, opsReal_ofNat]
  push_cast
  field_simp
  ring

/-! ## the roots and the blocks at a point of the chart -/

private lemma c2_e12 {b al xi : ℝ} : R₁₂ᶜ = R₁₂ᵈ := by ring
private lemma c2_e14 {b ga xi : ℝ} : R₁₄ᶜ = R₁₄ᵈ := by ring
private lemma c2_e23 {b al xi : ℝ} : R₂₃ᶜ = R₂₃ᵈ := by ring

theorem c2_roots (b al ga xi : ℝ) (hb : 0 ≤ b) :
    @cr12 ℝ opsReal b al xi = @dr12 ℝ opsReal (1 + b * al) (1 / 2 + b * xi) ∧
      @cr14 ℝ opsReal b ga xi = @dr14 ℝ opsReal (b * ga) (1 / 2 + b * xi) ∧
      @cr23 ℝ opsReal b al xi = @dr23 ℝ opsReal (1 + b * al) b (1 / 2 + b * xi) ∧
      @dr34 ℝ opsReal b (b * ga) (1 / 2 + b * xi) = b * @crho ℝ opsReal b ga xi := by
  simp only [cr12, dr12, cr14, dr14, cr23, dr23, dr34, crho, opsReal_sqrt, opsReal_sq,
    opsReal_ofNat]
  push_cast
  refine ⟨by rw [c2_e12], by rw [c2_e14], by rw [c2_e23], ?_⟩
  rw [show R₃₄ᵈ = b ^ 2 * (ρ₂ᶜ) by ring, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]

private lemma c2_hd {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    @hdr ℝ opsReal X (Real.sqrt X) Y (Real.sqrt Y) * (X - Y) =
      1 / (Y * Real.sqrt Y) - 1 / (X * Real.sqrt X) := by
  obtain ⟨sx, hsx, rfl⟩ : ∃ s, 0 < s ∧ X = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hX, (Real.sq_sqrt hX.le).symm⟩
  obtain ⟨sy, hsy, rfl⟩ : ∃ s, 0 < s ∧ Y = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hY, (Real.sq_sqrt hY.le).symm⟩
  simp only [hdr, Real.sqrt_sq hsx.le, Real.sqrt_sq hsy.le]
  field_simp
  ring

/-- `1/(ρ³) - b³/(R^(3/2)) = b³ (R - b² ρ²) hd(b² ρ², R)` -/
private lemma c2_E34_core {b R r : ℝ} (hb : 0 < b) (hR : 0 < R) (hr : 0 < r) :
    1 / (r * Real.sqrt r) - b * b * b / (R * Real.sqrt R) =
      b ^ 3 * ((R - b ^ 2 * r) *
        @hdr ℝ opsReal (b ^ 2 * r) (Real.sqrt (b ^ 2 * r)) R (Real.sqrt R)) := by
  have h34 : 0 < b ^ 2 * r := by positivity
  have key := c2_hd h34 hR
  have hs34 : Real.sqrt (b ^ 2 * r) = b * Real.sqrt r := by
    rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  rw [show (R - b ^ 2 * r) * @hdr ℝ opsReal (b ^ 2 * r) (Real.sqrt (b ^ 2 * r)) R (Real.sqrt R) =
      -(@hdr ℝ opsReal (b ^ 2 * r) (Real.sqrt (b ^ 2 * r)) R (Real.sqrt R) * (b ^ 2 * r - R)) by
    ring, key, hs34]
  have hsR := Real.sqrt_pos.2 hR
  have hsr := Real.sqrt_pos.2 hr
  generalize Real.sqrt R = sR at hsR ⊢
  generalize Real.sqrt r = sr at hsr ⊢
  field_simp
  ring

section
variable {b al ga xi : ℝ} (hb : 0 < b) (h12 : 0 < R₁₂ᵈ) (h34 : 0 < R₃₄ᵈ)
include hb h12 h34

/-- `E34h = b³ E34` -/
theorem c2_bE34 : @cE34h ℝ opsReal b al ga xi = b ^ 3 * @dE34 ℝ opsReal (1 + b * al) b (b * ga) (1 /
    2 + b * xi) := by
  have e34 : R₃₄ᵈ = b ^ 2 * (ρ₂ᶜ) := by ring
  have hpoly : (1 + b) * (g₄ᵈ) + (1 + b * al + b * ga) * (g₅ᵈ) = (R₁₂ᵈ) - (R₃₄ᵈ) := by ring
  have hr : 0 < ρ₂ᶜ := by
    rw [e34] at h34
    exact pos_of_mul_pos_right h34 (sq_nonneg b)
  simp only [cE34h, dE34, cr12, dr12, crho, dr34, dirG, aff, dirK, dirL, opsReal_sq,
    opsReal_sqrt, opsReal_ofNat]
  push_cast
  rw [c2_e12, hpoly, e34]
  exact c2_E34_core hb h12 hr

end

theorem c2_bDl13 {b : ℝ} (hb : b ≠ 0) (al ga xi : ℝ) :
    @cDl13 ℝ opsReal b al ga xi = @dDl13 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b :=
        by
  simp only [cDl13, dDl13, cr12, dr12, chG, aff, chK, chL, dirG, dirK, dirL, opsReal_sq,
    opsReal_ofNat]
  push_cast
  rw [c2_e12, eq_div_iff hb]
  ring

theorem c2_bDl24 {b : ℝ} (hb : b ≠ 0) (al ga xi : ℝ) :
    @cDl24 ℝ opsReal b al ga xi = @dDl24 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b :=
        by
  simp only [cDl24, dDl24, cr12, dr12, chG, aff, chK, chL, dirG, dirK, dirL, opsReal_sq,
    opsReal_ofNat]
  push_cast
  rw [c2_e12, eq_div_iff hb]
  ring

theorem c2_bE14 {b : ℝ} (hb : b ≠ 0) (al ga xi : ℝ) :
    @cE14 ℝ opsReal b al ga xi = @dE14 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  simp only [cE14, dE14, cr12, dr12, cr14, dr14, chG, aff, chK, chL, dirG, dirK, dirL,
    opsReal_sq, opsReal_ofNat]
  push_cast
  rw [c2_e12, c2_e14, eq_div_iff hb]
  ring

theorem c2_bE23 {b : ℝ} (hb : b ≠ 0) (al ga xi : ℝ) :
    @cE23 ℝ opsReal b al ga xi = @dE23 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  simp only [cE23, dE23, cr12, dr12, cr23, dr23, chG, aff, chK, chL, dirG, dirK, dirL,
    opsReal_sq, opsReal_ofNat]
  push_cast
  rw [c2_e12, c2_e23, eq_div_iff hb]
  ring

/-! ## the inputs of `chMidN` are those of `dirMidN`, rescaled -/

section
variable {b al ga xi : ℝ} (hb : 0 < b) (h12 : 0 < R₁₂ᵈ) (h34 : 0 < R₃₄ᵈ)
include hb h12 h34

/-- the weights of `chMidN` are `b` times those of `dirMidN` -/
theorem ch2N_weights :
    (@chYIn ℝ opsReal b al ga xi).d12 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d12 ∧
    (@chYIn ℝ opsReal b al ga xi).d13 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d13 ∧
    (@chYIn ℝ opsReal b al ga xi).d14 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d14 ∧
    (@chYIn ℝ opsReal b al ga xi).d23 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d23 ∧
    (@chYIn ℝ opsReal b al ga xi).d24 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d24 ∧
    (@chYIn ℝ opsReal b al ga xi).d34 = b * (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b *
        xi)).d34 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := @chYIn_w ℝ opsReal b al ga xi
  obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ := @dirYIn_w ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)
  obtain ⟨r1, r2, r3, r4⟩ := c2_roots b al ga xi hb.le
  rw [c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, c2_bDl13 hb.ne', c2_bDl24 hb.ne',
    c2_bE14 hb.ne', c2_bE23 hb.ne', c2_bE34 hb h12 h34, r1, r2, r3, r4]
  exact wOf_rel hb.ne' al ga xi _ _ _ _ _ _ _ _ _

/-- the scale of `chMidN` is that of `dirMidN` divided by `b` -/
theorem c2N_F : (@chYIn ℝ opsReal b al ga xi).F = (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2
    + b * xi)).F / b := by
  obtain ⟨-, -, -, -, -, -, hc⟩ := @chYIn_w ℝ opsReal b al ga xi
  obtain ⟨-, -, -, -, -, -, hd⟩ := @dirYIn_w ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)
  rw [hc, hd, c2_bDl13 hb.ne', c2_bDl24 hb.ne', c2_bE34 hb h12 h34]
  exact fOf_rel hb.ne' al ga _ _ _

end
/-- the entries of `midY` do not change when the weights are multiplied by `b ≠ 0` and `A`, `F`
divided by `b` -/
theorem ent_scale (A A' : YIn ℝ) {b : ℝ} (hb : b ≠ 0) (hs2 : A'.s2 = A.s2)
    (hA1 : A'.Axx = A.Axx / b) (hA2 : A'.Axe = A.Axe / b) (hA3 : A'.Aee = A.Aee / b)
    (hF : A'.F = A.F / b)
    (h12 : A'.d12 = b * A.d12) (h13 : A'.d13 = b * A.d13) (h14 : A'.d14 = b * A.d14)
    (h23 : A'.d23 = b * A.d23) (h24 : A'.d24 = b * A.d24) (h34 : A'.d34 = b * A.d34)
    (k1 : A'.u12x = A.u12x) (k2 : A'.u13x = A.u13x) (k3 : A'.u14x = A.u14x)
    (k4 : A'.u23x = A.u23x) (k5 : A'.u24x = A.u24x) (k6 : A'.u34x = A.u34x)
    (k7 : A'.u12e = A.u12e) (k8 : A'.u13e = A.u13e) (k9 : A'.u14e = A.u14e)
    (k10 : A'.u24e = A.u24e) :
    @YIn.ent ℝ opsReal A' = @YIn.ent ℝ opsReal A := by
  simp only [YIn.ent, zz, opsReal_ofNat]
  push_cast
  rw [hs2, hA1, hA2, hA3, hF, h12, h13, h14, h23, h24, h34, k1, k2, k3, k4, k5, k6, k7, k8, k9,
    k10]
  have hmx : (b * A.d12 * A.u12x + b * A.d13 * A.u13x + b * A.d14 * A.u14x +
        b * A.d23 * A.u23x + b * A.d24 * A.u24x + b * A.d34 * A.u34x) *
        (1 / (b * A.d12 + b * A.d13 + b * A.d14 + b * A.d23 + b * A.d24 + b * A.d34)) =
      (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x + A.d24 * A.u24x +
        A.d34 * A.u34x) * (1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)) := by
    rw [show b * A.d12 * A.u12x + b * A.d13 * A.u13x + b * A.d14 * A.u14x +
        b * A.d23 * A.u23x + b * A.d24 * A.u24x + b * A.d34 * A.u34x =
        b * (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x +
          A.d24 * A.u24x + A.d34 * A.u34x) by ring,
      show b * A.d12 + b * A.d13 + b * A.d14 + b * A.d23 + b * A.d24 + b * A.d34 =
        b * (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) by ring,
      mul_one_div, mul_one_div, mul_div_mul_left _ _ hb]
  have hme : ((b * A.d12 + b * A.d23) * A.u12e + b * A.d13 * A.u13e +
        (b * A.d14 + b * A.d34) * A.u14e + b * A.d24 * A.u24e) *
        (1 / (b * A.d12 + b * A.d13 + b * A.d14 + b * A.d23 + b * A.d24 + b * A.d34)) =
      ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e +
        A.d24 * A.u24e) * (1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)) := by
    rw [show (b * A.d12 + b * A.d23) * A.u12e + b * A.d13 * A.u13e +
        (b * A.d14 + b * A.d34) * A.u14e + b * A.d24 * A.u24e =
        b * ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e +
          A.d24 * A.u24e) by ring,
      show b * A.d12 + b * A.d13 + b * A.d14 + b * A.d23 + b * A.d24 + b * A.d34 =
        b * (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34) by ring,
      mul_one_div, mul_one_div, mul_div_mul_left _ _ hb]
  rw [hmx, hme]
  generalize (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x +
    A.d24 * A.u24x + A.d34 * A.u34x) * (1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)) = mx
  generalize ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e +
    A.d24 * A.u24e) * (1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)) = me
  rw [one_div_div]
  by_cases hF0 : A.F = 0
  · simp [hF0]
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> field_simp

private lemma c2N_s2 (b al ga xi : ℝ) : (@chYIn ℝ opsReal b al ga xi).s2 =
    (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).s2 := by
  simp only [chYIn, dirYIn, opsReal_sq, opsReal_ofNat]
  push_cast
  ring

private lemma c2N_A {b : ℝ} (hb : b ≠ 0) (al ga xi : ℝ) :
    (@chYIn ℝ opsReal b al ga xi).Axx =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).Axx / b ∧
      (@chYIn ℝ opsReal b al ga xi).Axe =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).Axe / b ∧
      (@chYIn ℝ opsReal b al ga xi).Aee =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).Aee / b := by
  simp only [chYIn, dirYIn, opsReal_ofNat]
  push_cast
  refine ⟨?_, ?_, ?_⟩ <;> rw [eq_div_iff hb] <;> ring

private lemma c2N_u (b al ga xi : ℝ) :
    (@chYIn ℝ opsReal b al ga xi).u12x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u12x ∧
      (@chYIn ℝ opsReal b al ga xi).u13x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u13x ∧
      (@chYIn ℝ opsReal b al ga xi).u14x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u14x ∧
      (@chYIn ℝ opsReal b al ga xi).u23x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u23x ∧
      (@chYIn ℝ opsReal b al ga xi).u24x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u24x ∧
      (@chYIn ℝ opsReal b al ga xi).u34x =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u34x ∧
      (@chYIn ℝ opsReal b al ga xi).u12e =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u12e ∧
      (@chYIn ℝ opsReal b al ga xi).u13e =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u13e ∧
      (@chYIn ℝ opsReal b al ga xi).u14e =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u14e ∧
      (@chYIn ℝ opsReal b al ga xi).u24e =
        (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).u24e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [chYIn, dirYIn, opsReal_ofNat] <;> (try push_cast) <;> (try ring)

section
variable {b al ga xi : ℝ} (hb : 0 < b) (h12 : 0 < R₁₂ᵈ) (h34 : 0 < R₃₄ᵈ)
include hb h12 h34

/-- **`chMidN = dirMidN`.**  At `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi` (`b > 0`), `det Y`
and `tr Y` of `chMidN` equal those of `dirMidN`. -/
theorem ch2N_eq :
    (@chMidN ℝ opsReal b al ga xi).det =
        (@dirMidN ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).det ∧
      (@chMidN ℝ opsReal b al ga xi).tr =
        (@dirMidN ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).tr := by
  obtain ⟨a1, a2, a3⟩ := c2N_A hb.ne' al ga xi
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩ := c2N_u b al ga xi
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := ch2N_weights hb h12 h34
  have he := ent_scale (@dirYIn ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi))
    (@chYIn ℝ opsReal b al ga xi) hb.ne' (c2N_s2 b al ga xi) a1 a2 a3 (c2N_F hb h12 h34) w1 w2 w3
    w4 w5 w6 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
  rw [@chMidN_det_eq ℝ opsReal, @chMidN_tr_eq ℝ opsReal, @dirMidN_det_eq ℝ opsReal,
    @dirMidN_tr_eq ℝ opsReal, @YIn.Y_ent ℝ opsReal, @YIn.Y_ent ℝ opsReal, he]
  exact ⟨rfl, rfl⟩

end

/-- **`chMidN = dirMidN`**, at a point of `𝒞`: `det Y` and `tr Y` of `chMidN` at
`(b, (a - 1)/b, c/b, (x - 1/2)/b)` equal those of `dirMidN` at `(a, b, c, x)`. -/
theorem ch2N_eq_inC {a b c x : ℝ} (hC : InC a b c x) :
    (@chMidN ℝ opsReal b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).det =
        (@dirMidN ℝ opsReal a b c x).det ∧
      (@chMidN ℝ opsReal b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).tr =
        (@dirMidN ℝ opsReal a b c x).tr := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  have ea : 1 + b * ((a - 1) / b) = a := by field_simp; ring
  have ec : b * (c / b) = c := by field_simp
  have ex : 1 / 2 + b * ((x - 1 / 2) / b) = x := by field_simp; ring
  have hx : 0 < (1 + x) * (1 - x) := mul_pos (by linarith) (by linarith)
  have h12 : 0 < 1 + (1 + b * ((a - 1) / b)) * (1 + b * ((a - 1) / b)) -
      2 * (1 + b * ((a - 1) / b)) * (1 / 2 + b * ((x - 1 / 2) / b)) := by
    rw [ea, ex]; nlinarith [sq_nonneg (a - x)]
  have h34 : 0 < b * b + b * (c / b) * (b * (c / b)) -
      2 * b * (b * (c / b)) * (1 / 2 + b * ((x - 1 / 2) / b)) := by
    rw [ec, ex]; nlinarith [sq_nonneg (b - c * x), mul_pos (mul_pos hc hc) hx]
  have h := ch2N_eq (al := (a - 1) / b) (ga := c / b) (xi := (x - 1 / 2) / b) hb h12 h34
  rw [ea, ec, ex] at h
  exact h

/-- `chP2 = chP` at `ℝ`: `chP2` takes the roots `r₁₃ = 1 + b` and `r₂₄ = 1 + b (al + ga)`
exactly -/
theorem chP2_eq {b al ga xi : ℝ} (hb : 0 ≤ 1 + b) (h24 : 0 ≤ 1 + b * (al + ga)) :
    @chP2 ℝ opsReal b al ga xi = chPR b al ga xi := by
  have e13 : Real.sqrt ((1 + b) ^ 2) = 1 + b := Real.sqrt_sq hb
  have e24 : Real.sqrt ((1 + b * (al + ga)) ^ 2) = 1 + b * (al + ga) := Real.sqrt_sq h24
  have f13 : 1 + b * (2 + b) = (1 + b) ^ 2 := by ring
  have f24 : 1 + b * (2 * (al + ga) + b * (al + ga) ^ 2) = (1 + b * (al + ga)) ^ 2 := by ring
  simp only [chP2, chPR, chP, hd_eq_hdr, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
  push_cast
  rw [f13, f24, e13, e24]
  ring

end

end C4
