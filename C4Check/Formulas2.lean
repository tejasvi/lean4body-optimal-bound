module

public import C4Check.Formulas

@[expose] public section

/-!
# The midpoint test, written once for every `[Ops α]`

`λ_max(S(y)) < 1/3` for the best `y` is equivalent to `T ≻ 0`, where (with `d_e = D_e τ_e²`, `m_e`
the midpoint of edge `e`, `M₂ = Σ_l A_l q_l q_lᵀ`, `W = Σ d_e`, `t = Σ d_e m_e`)
`T = W M₂² - 12 (W Σ d_e m_e m_eᵀ - t tᵀ)`.

**Direct chart** `(a, b, c, x)`, `q₁ = (1, 0)`, `q₂ = a (x, s)`, `q₃ = (-b, 0)`, `q₄ = -c (x, s)`,
`s² = 1 - x²`.  In the frame `diag(1, s)` the points become `q̃₂ = (a x, a)`, `q̃₄ = -(c x, c)`, and
`A_l = s Â_l / 2` with the doubled areas `Â = (b (a + c), -c (1 + b), a + c, -a (1 + b))`.  Then
`T = s⁴ diag(1, s) T' diag(1, s)` up to a positive constant factor and `den⁻²`, where
`T' = den W K - (W Σ d_e u_e u_eᵀ - t tᵀ)` with
* `d_e = -(den w_e) Â_i Â_j r_e⁵` (`den w_e` is a polynomial in the `hd`-block, and
  `D_e τ_e² = -w_e A_i A_j r_e⁵ / 3`), so `W = Σ d_e`, `t = Σ d_e u_e`;
* `u_e = q̃_i + q̃_j - v`, for any constant `v = (vx, ve)` (the scatter `W Σ d u uᵀ - t tᵀ` does not
  depend on `v`; a `v` near the weighted centroid avoids cancellation in interval arithmetic);
* `K = k² N D² N = k² [[(b - p x²)² + p² x² s², p x (p - b)], [p x (p - b), p²]]`, `p = a c`,
  `k = (1 + b) (a + c)`, where `Σ Â_l q̃_l q̃_lᵀ = k N`, `N = [[b - p x², -p x], [-p x, -p]]`.

So `T ≻ 0 ⟺ det T' > 0 ∧ tr T' > 0`.  No square root of `1 - x²` occurs; the roots of
`R₁₃ = (1 + b)²` and `R₂₄ = (a + c)²` are taken exactly; each other root is computed once.

**Blow-up chart** `(b, al, ga, xi)`, `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi`.  With the
quantities of `chP` (`Dl13 = g₁ hd / b`, …, `E34h = b³ E34`, `denh = b³ den`) every `d_e` is
`d̂_e / b` and `K = b² k² N̂`, `N̂ = [[(1 - p̂ x²)² + p̂² x² s², p̂ x (p̂ - 1)], [p̂ x (p̂ - 1), p̂²]]`,
`p̂ = a ga`, so `T̂ = denh Ŵ k² N̂ - (Ŵ Σ d̂_e u_e u_eᵀ - t̂ t̂ᵀ) = b² T'`.  Every quantity is smooth
at `b = 0`.  At the corner (`b = 0`, `ga = 1`) every divisor (`hd`'s, `ρ³`, `R₁₂ r₁₂`, `2`) has an
`al`-free value (`2`, `1`, `1`, `2`) and every square root is taken of a quantity whose value is `1`.
-/

namespace C4

/-- the outputs of one evaluation: `P` (`P̂ = b P` in the chart), `det T'`, `tr T'` (`T̂` in the
chart) and the six constraints `g` (`h` in the chart) -/
structure Out (α : Type) where
  P : α
  det : α
  tr : α
  g : Six α

section
variable {α : Type} [Ops α]

/-- `hd X Y` with the square roots `sx = √X`, `sy = √Y` supplied -/
def hdr (X sx Y sy : α) : α := (X + sx * sy + Y) / ((sx + sy) * X * sx * Y * sy)

/-- `(det T, tr T)` for `T = G W K₀ - (W Σ d_e u_e u_eᵀ - t tᵀ)`, `W = Σ d_e`, `t = Σ d_e u_e`,
`K₀ = [[Kxx, Kxe], [Kxe, Kee]]`, from the weights `d_e` and the shifted doubled midpoints `u_e`
(`u₂₃` has the `y`-entry of `u₁₂`, and `u₃₄` that of `u₁₄`) -/
def midT (G Kxx Kxe Kee d12 d13 d14 d23 d24 d34 u12x u13x u14x u23x u24x u34x u12e u13e u14e
    u24e : α) : α × α :=
  let W := d12 + d13 + d14 + d23 + d24 + d34
  let tx := d12 * u12x + d13 * u13x + d14 * u14x + d23 * u23x + d24 * u24x + d34 * u34x
  let te := (d12 + d23) * u12e + d13 * u13e + (d14 + d34) * u14e + d24 * u24e
  let Sxx := d12 * Ops.sq u12x + d13 * Ops.sq u13x + d14 * Ops.sq u14x + d23 * Ops.sq u23x +
    d24 * Ops.sq u24x + d34 * Ops.sq u34x
  let Sxe := (d12 * u12x + d23 * u23x) * u12e + d13 * u13x * u13e +
    (d14 * u14x + d34 * u34x) * u14e + d24 * u24x * u24e
  let See := (d12 + d23) * Ops.sq u12e + d13 * Ops.sq u13e + (d14 + d34) * Ops.sq u14e +
    d24 * Ops.sq u24e
  let GW := G * W
  let Txx := GW * Kxx - (W * Sxx - Ops.sq tx)
  let Txe := GW * Kxe - (W * Sxe - tx * te)
  let Tee := GW * Kee - (W * See - Ops.sq te)
  (Txx * Tee - Ops.sq Txe, Txx + Tee)

/-! ## direct chart -/

/-- `P`, `det T'`, `tr T'` and `g` in the direct chart, for the shift `(vx, ve)` -/
def dirMid (vx ve a b c x : α) : Out α :=
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
  let T := midT (den * Ops.sq k)
    (Ops.sq (b - px * x) + Ops.sq px * (1 - Ops.sq x)) (px * (p - b)) (Ops.sq p)
    (P12 * (b * c * k) * (Ops.sq R12 * r12))
    (Dl13 * (E34 + Dl13) * (b * R24) * (Ops.sq R13 * r13))
    ((den * E14 + P12) * (a * b * k) * (Ops.sq R14 * r14))
    ((den * E23 + P12) * (c * k) * (Ops.sq R23 * r23))
    (Dl24 * (E34 + Dl24) * (a * c * R13) * (Ops.sq R24 * r24))
    ((E34 + Dl13) * (E34 + Dl24) * (a * k) * (Ops.sq R34 * r34))
    (1 + X2 - vx) (1 - b - vx) (1 - X4 - vx) (X2 - b - vx) (X2 - X4 - vx) (-b - X4 - vx)
    (a - ve) (-ve) (-c - ve) (a - c - ve)
  ⟨E14 * E23 * den + P12 * (E14 + E23 - E34), T.1, T.2, g⟩

/-- `P` alone, with shared roots (Newton steps) -/
def dirP2 (a b c x : α) : α :=
  let g := dirG a b c x
  let R12 := 1 + a * a - 2 * a * x
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R34 := b * b + c * c - 2 * b * c * x
  let r12 := Ops.sqrt R12
  let r13 := 1 + b
  let r24 := a + c
  let d12_23 := r13 * g.x4
  let Dl13 := g.x1 * hdr R12 r12 (Ops.sq r13) r13
  let Dl24 := g.x2 * hdr R12 r12 (Ops.sq r24) r24
  let E34 := (d12_23 + r24 * g.x5) * hdr R34 (Ops.sqrt R34) R12 r12
  let E14 := r24 * g.x3 * hdr R14 (Ops.sqrt R14) R12 r12
  let E23 := d12_23 * hdr R23 (Ops.sqrt R23) R12 r12
  E14 * E23 * (Dl13 + E34 + Dl24) + Dl13 * Dl24 * (E14 + E23 - E34)

/-! ## blow-up chart -/

/-- `P̂ = b P`, `det T̂`, `tr T̂` and `h` in the blow-up chart, for the shift `(vx, ve)` -/
def chMid (vx ve b al ga xi : α) : Out α :=
  let h := chG b al ga xi
  let x := 1 / 2 + b * xi
  let a := 1 + b * al
  let c := b * ga
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let r12 := Ops.sqrt R12
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let rho := Ops.sqrt rho2
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let Dl13 := h.x1 * hdr R12 r12 R13 r13
  let Dl24 := h.x2 * hdr R12 r12 R24 r24
  let E14 := r24 * h.x3 * hdr R14 r14 R12 r12
  let E23 := r13 * h.x4 * hdr R23 r23 R12 r12
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * rho) - b * b * b / (R12 * r12)
  let denh := E34h + b4 * (Dl13 + Dl24)
  let P12 := Dl13 * Dl24
  let D1 := E34h + b4 * Dl13
  let D2 := E34h + b4 * Dl24
  let k := r13 * r24
  let X2 := a * x
  let X4 := c * x
  let p := a * ga
  let px := p * x
  let T := midT (denh * Ops.sq k)
    (Ops.sq (1 - px * x) + Ops.sq px * (1 - Ops.sq x)) (px * (p - 1)) (Ops.sq p)
    (b4 * b * P12 * (ga * k) * (Ops.sq R12 * r12))
    (Dl13 * D1 * R24 * (Ops.sq R13 * r13))
    ((denh * E14 + b4 * P12) * (a * k) * (Ops.sq R14 * r14))
    ((denh * E23 + b4 * P12) * (ga * k) * (Ops.sq R23 * r23))
    (Dl24 * D2 * (a * ga * R13) * (Ops.sq R24 * r24))
    (D1 * D2 * (a * k) * (Ops.sq rho2 * rho))
    (1 + X2 - vx) (1 - b - vx) (1 - X4 - vx) (X2 - b - vx) (X2 - X4 - vx) (-b - X4 - vx)
    (a - ve) (-ve) (-c - ve) (a - c - ve)
  ⟨E14 * E23 * denh + P12 * (b4 * (E14 + E23) - E34h), T.1, T.2, h⟩

/-- `P̂ = b P` alone, with shared roots (Newton steps) -/
def chP2 (b al ga xi : α) : α :=
  let h := chG b al ga xi
  let x := 1 / 2 + b * xi
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let r12 := Ops.sqrt R12
  let r13 := 1 + b
  let r24 := 1 + b * (al + ga)
  let Dl13 := h.x1 * hdr R12 r12 (Ops.sq r13) r13
  let Dl24 := h.x2 * hdr R12 r12 (Ops.sq r24) r24
  let E14 := r24 * h.x3 * hdr R14 (Ops.sqrt R14) R12 r12
  let E23 := r13 * h.x4 * hdr R23 (Ops.sqrt R23) R12 r12
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * Ops.sqrt rho2) - b * b * b / (R12 * r12)
  E14 * E23 * (E34h + b4 * (Dl13 + Dl24)) + Dl13 * Dl24 * (b4 * (E14 + E23) - E34h)


/-! ## the normalized test

`Y = diag(1, 1 - x²) - M⁻¹ C M⁻¹`, `C = Σ d_e (u_e - ū)(u_e - ū)ᵀ`, `ū = Σ d_e u_e / W`.  With the
weights of `dirMid` (scaled by `den`) and `M = k N`, `M⁻¹ = adj N / (k det N)`, `det N = -p b`:
`Y = diag(1, s²) - X / F`, `X = Σ_e d_e z_e z_eᵀ`, `z_e = adj N (u_e - ū)`, `F = den k² p² b²`.
Then `det Y = 9 s² det(I/3 - G)` and `tr Y = 1 + s² - 3 tr(D G D)`, `D = diag(1, s)`, so
`Y ≻ 0 ⟺ λ_max(G) < 1/3`.  `X` is a sum of positive semidefinite rank-one terms. -/

/-- `(d zx², d zx ze, d ze²)` for `z = A v`, `A = [[Axx, Axe], [Axe, Aee]]` -/
def zz (Axx Axe Aee d vx ve : α) : α × α × α :=
  let zx := Axx * vx + Axe * ve
  let ze := Axe * vx + Aee * ve
  let dzx := d * zx
  (dzx * zx, dzx * ze, d * ze * ze)

/-- `(det Y, tr Y)` for `Y = diag(1, s2) - X / F`, `X = Σ_e d_e z_e z_eᵀ`, `z_e = A (u_e - ū)`,
`ū = Σ d_e u_e / Σ d_e`, `A = [[Axx, Axe], [Axe, Aee]]` (`u₂₃` has the `y`-entry of `u₁₂`, and
`u₃₄` that of `u₁₄`) -/
def midY (s2 Axx Axe Aee F d12 d13 d14 d23 d24 d34 u12x u13x u14x u23x u24x u34x u12e u13e u14e
    u24e : α) : α × α :=
  let iW := 1 / (d12 + d13 + d14 + d23 + d24 + d34)
  let mx := (d12 * u12x + d13 * u13x + d14 * u14x + d23 * u23x + d24 * u24x + d34 * u34x) * iW
  let me := ((d12 + d23) * u12e + d13 * u13e + (d14 + d34) * u14e + d24 * u24e) * iW
  let z12 := zz Axx Axe Aee d12 (u12x - mx) (u12e - me)
  let z13 := zz Axx Axe Aee d13 (u13x - mx) (u13e - me)
  let z14 := zz Axx Axe Aee d14 (u14x - mx) (u14e - me)
  let z23 := zz Axx Axe Aee d23 (u23x - mx) (u12e - me)
  let z24 := zz Axx Axe Aee d24 (u24x - mx) (u24e - me)
  let z34 := zz Axx Axe Aee d34 (u34x - mx) (u14e - me)
  let iF := 1 / F
  let Yxx := 1 - (z12.1 + z13.1 + z14.1 + z23.1 + z24.1 + z34.1) * iF
  let Xxe := (z12.2.1 + z13.2.1 + z14.2.1 + z23.2.1 + z24.2.1 + z34.2.1) * iF
  let Yee := s2 - (z12.2.2 + z13.2.2 + z14.2.2 + z23.2.2 + z24.2.2 + z34.2.2) * iF
  (Yxx * Yee - Ops.sq Xxe, Yxx + Yee)

/-- `P`, `det Y`, `tr Y` and `g` in the direct chart (the normalized test) -/
def dirMidN (a b c x : α) : Out α :=
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
  let Y := midY (1 - Ops.sq x) (-p) px (b - px * x) (den * Ops.sq (k * p * b))
    (P12 * (b * c * k) * (Ops.sq R12 * r12))
    (Dl13 * (E34 + Dl13) * (b * R24) * (Ops.sq R13 * r13))
    ((den * E14 + P12) * (a * b * k) * (Ops.sq R14 * r14))
    ((den * E23 + P12) * (c * k) * (Ops.sq R23 * r23))
    (Dl24 * (E34 + Dl24) * (a * c * R13) * (Ops.sq R24 * r24))
    ((E34 + Dl13) * (E34 + Dl24) * (a * k) * (Ops.sq R34 * r34))
    (1 + X2) (1 - b) (1 - X4) (X2 - b) (X2 - X4) (-b - X4) a 0 (-c) (a - c)
  ⟨E14 * E23 * den + P12 * (E14 + E23 - E34), Y.1, Y.2, g⟩

/-- `P̂ = b P`, `det Y`, `tr Y` and `h` in the blow-up chart (the normalized test).  With
`N = b N̂`, `N̂ = [[1 - p̂ x², -p̂ x], [-p̂ x, -p̂]]`, `p̂ = a ga`, `d_e = d̂_e / b` and
`den = denh / b³`, every power of `b` cancels in `X / F`: `det Y` and `tr Y` are those of `dirMidN`
at `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi`. -/
def chMidN (b al ga xi : α) : Out α :=
  let h := chG b al ga xi
  let x := 1 / 2 + b * xi
  let a := 1 + b * al
  let c := b * ga
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let r12 := Ops.sqrt R12
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let rho := Ops.sqrt rho2
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let Dl13 := h.x1 * hdr R12 r12 R13 r13
  let Dl24 := h.x2 * hdr R12 r12 R24 r24
  let E14 := r24 * h.x3 * hdr R14 r14 R12 r12
  let E23 := r13 * h.x4 * hdr R23 r23 R12 r12
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * rho) - b * b * b / (R12 * r12)
  let denh := E34h + b4 * (Dl13 + Dl24)
  let P12 := Dl13 * Dl24
  let D1 := E34h + b4 * Dl13
  let D2 := E34h + b4 * Dl24
  let k := r13 * r24
  let X2 := a * x
  let X4 := c * x
  let p := a * ga
  let px := p * x
  let Y := midY (1 - Ops.sq x) (-p) px (1 - px * x) (denh * Ops.sq (k * p))
    (b4 * b * P12 * (ga * k) * (Ops.sq R12 * r12))
    (Dl13 * D1 * R24 * (Ops.sq R13 * r13))
    ((denh * E14 + b4 * P12) * (a * k) * (Ops.sq R14 * r14))
    ((denh * E23 + b4 * P12) * (ga * k) * (Ops.sq R23 * r23))
    (Dl24 * D2 * (a * ga * R13) * (Ops.sq R24 * r24))
    (D1 * D2 * (a * k) * (Ops.sq rho2 * rho))
    (1 + X2) (1 - b) (1 - X4) (X2 - b) (X2 - X4) (-b - X4) a 0 (-c) (a - c)
  ⟨E14 * E23 * denh + P12 * (b4 * (E14 + E23) - E34h), Y.1, Y.2, h⟩


/-! ## the inputs of `midY`, as a structure

`dirMidN` and `chMidN` compute `midY` of twenty-one inputs.  `dirYIn` and `chYIn` compute those
inputs by the same let-chains, so `(dirMidN a b c x).det = (dirYIn a b c x).Y.1` (and so on) hold
by `rfl` for every `[Ops α]`.  The soundness proofs use them to check the carrier evaluations of
`midY` and of its inputs separately, which keeps elaboration fast. -/

/-- the twenty-one inputs of `midY` -/
structure YIn (α : Type) where
  s2 : α
  Axx : α
  Axe : α
  Aee : α
  F : α
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

/-- the inputs, mapped by `g` -/
def YIn.map {α β : Type} (g : α → β) (A : YIn α) : YIn β :=
  ⟨g A.s2, g A.Axx, g A.Axe, g A.Aee, g A.F, g A.d12, g A.d13, g A.d14, g A.d23, g A.d24, g A.d34,
    g A.u12x, g A.u13x, g A.u14x, g A.u23x, g A.u24x, g A.u34x, g A.u12e, g A.u13e, g A.u14e,
    g A.u24e⟩

/-- `(det Y, tr Y)` from the inputs -/
def YIn.Y (A : YIn α) : α × α :=
  midY A.s2 A.Axx A.Axe A.Aee A.F A.d12 A.d13 A.d14 A.d23 A.d24 A.d34 A.u12x A.u13x A.u14x
    A.u23x A.u24x A.u34x A.u12e A.u13e A.u14e A.u24e

/-- the inputs of `midY` in `dirMidN`, by the same let-chain -/
def dirYIn (a b c x : α) : YIn α :=
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
  ⟨1 - Ops.sq x, -p, px, b - px * x, den * Ops.sq (k * p * b),
    P12 * (b * c * k) * (Ops.sq R12 * r12),
    Dl13 * (E34 + Dl13) * (b * R24) * (Ops.sq R13 * r13),
    (den * E14 + P12) * (a * b * k) * (Ops.sq R14 * r14),
    (den * E23 + P12) * (c * k) * (Ops.sq R23 * r23),
    Dl24 * (E34 + Dl24) * (a * c * R13) * (Ops.sq R24 * r24),
    (E34 + Dl13) * (E34 + Dl24) * (a * k) * (Ops.sq R34 * r34),
    1 + X2, 1 - b, 1 - X4, X2 - b, X2 - X4, -b - X4, a, 0, -c, a - c⟩

/-- the inputs of `midY` in `chMidN`, by the same let-chain -/
def chYIn (b al ga xi : α) : YIn α :=
  let h := chG b al ga xi
  let x := 1 / 2 + b * xi
  let a := 1 + b * al
  let c := b * ga
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let r12 := Ops.sqrt R12
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let rho := Ops.sqrt rho2
  let r13 := 1 + b
  let r24 := a + c
  let R13 := Ops.sq r13
  let R24 := Ops.sq r24
  let Dl13 := h.x1 * hdr R12 r12 R13 r13
  let Dl24 := h.x2 * hdr R12 r12 R24 r24
  let E14 := r24 * h.x3 * hdr R14 r14 R12 r12
  let E23 := r13 * h.x4 * hdr R23 r23 R12 r12
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * rho) - b * b * b / (R12 * r12)
  let denh := E34h + b4 * (Dl13 + Dl24)
  let P12 := Dl13 * Dl24
  let D1 := E34h + b4 * Dl13
  let D2 := E34h + b4 * Dl24
  let k := r13 * r24
  let X2 := a * x
  let X4 := c * x
  let p := a * ga
  let px := p * x
  ⟨1 - Ops.sq x, -p, px, 1 - px * x, denh * Ops.sq (k * p),
    b4 * b * P12 * (ga * k) * (Ops.sq R12 * r12),
    Dl13 * D1 * R24 * (Ops.sq R13 * r13),
    (denh * E14 + b4 * P12) * (a * k) * (Ops.sq R14 * r14),
    (denh * E23 + b4 * P12) * (ga * k) * (Ops.sq R23 * r23),
    Dl24 * D2 * (a * ga * R13) * (Ops.sq R24 * r24),
    D1 * D2 * (a * k) * (Ops.sq rho2 * rho),
    1 + X2, 1 - b, 1 - X4, X2 - b, X2 - X4, -b - X4, a, 0, -c, a - c⟩

theorem dirMidN_det_eq (a b c x : α) : (dirMidN a b c x).det = (dirYIn a b c x).Y.1 := rfl

theorem dirMidN_tr_eq (a b c x : α) : (dirMidN a b c x).tr = (dirYIn a b c x).Y.2 := rfl

theorem chMidN_det_eq (b al ga xi : α) : (chMidN b al ga xi).det = (chYIn b al ga xi).Y.1 := rfl

theorem chMidN_tr_eq (b al ga xi : α) : (chMidN b al ga xi).tr = (chYIn b al ga xi).Y.2 := rfl

end

end C4
