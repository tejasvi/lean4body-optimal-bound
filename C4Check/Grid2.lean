module

public import C4Check.Search2
public import C4Check.Grid
public import C4Check.TF

@[expose] public section

/-!
# The two modes of the sheared replay, and their covers

`dirMode2`: the direct chart `(a, b, c)`, dependent coordinate `x` clamped to `[-1, 1]`.
`chMode2 k`: the blow-up chart `(b, al, ga)`, dependent coordinate `xi`; boxes inside the corner
disc `b² + (ga - 1)² ≤ 4^-k` may be left to the corner theorem.  Both test the normalized `Y`
(`dirMidN`, `chMidN`) with first-order jets; their own evaluator `ev2` refuses every leaf (modes
with an order-3 evaluator are built from these with `ev2` replaced).

The initial grids are those of the first-order checker (`dirCellBox`, `chCellBox` of `C4Check.Grid`).  A box is `Certified2`
if `checkBoxH2` succeeds on it with some hint, or if both halves of one of its splits are
certified; `Cover2 M box a b` says that every cell `a ≤ n < b` is.
-/

namespace C4

def dirMode2 : Mode2 where
  kl A B C := (dirK (some A) (some B) (some C), dirL (some A) (some B) (some C))
  gP R z0 z1 z2 z3 :=
    (@dirG _ (jetOps R) (some z0) (some z1) (some z2) (some z3),
     @dirP2 _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
  outJ R z0 z1 z2 z3 := @dirMidN _ (jetOps R) (some z0) (some z1) (some z2) (some z3)
  ev2 _ _ _ _ := false
  clamp := true
  disc := none

def chMode2 (k : Nat) : Mode2 where
  kl A B C := (chK (some A) (some B) (some C), chL (some A) (some B) (some C))
  gP R z0 z1 z2 z3 :=
    (@chG _ (jetOps R) (some z0) (some z1) (some z2) (some z3),
     @chP2 _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
  outJ R z0 z1 z2 z3 := @chMidN _ (jetOps R) (some z0) (some z1) (some z2) (some z3)
  ev2 _ _ _ _ := false
  clamp := false
  disc := some k

/-- cell `n` of the direct grid is certified by the hint `h` -/
def dirCell2 (n h : Nat) : Bool := (checkBoxH2 dirMode2 depth (dirCellBox n) h).isSome

/-- cell `n` of the blow-up grid is certified by the hint `h` (corner disc of radius `2^-k`) -/
def chCell2 (k n h : Nat) : Bool := (checkBoxH2 (chMode2 k) depth (chCellBox n) h).isSome

/-! ## assembling the certificates -/

/-- `B` is certified: `checkBoxH2` succeeds on it with some hint, or both halves of one of its
splits are certified -/
inductive Certified2 (M : Mode2) : Box → Prop
  | leaf {B : Box} (h : Nat) : (checkBoxH2 M depth B h).isSome = true → Certified2 M B
  | split {B : Box} (s : Nat) : Certified2 M (splitBox B s).1 → Certified2 M (splitBox B s).2 →
      Certified2 M B

/-- every cell `a ≤ n < b` of the grid `box` is certified -/
def Cover2 (M : Mode2) (box : Nat → Box) (a b : Nat) : Prop :=
  ∀ n, a ≤ n → n < b → Certified2 M (box n)

/-- a run of cells of the direct grid checked by `allCells` -/
theorem Cover2.dir {a b : Nat} {hs : List Nat} (h : allCells dirCell2 a b hs = true) :
    Cover2 dirMode2 dirCellBox a b := fun n h1 h2 =>
  match allCells_hinted h n h1 h2 with
  | ⟨x, hx⟩ => .leaf x hx

/-- a run of cells of the blow-up grid checked by `allCells` -/
theorem Cover2.ch {k a b : Nat} {hs : List Nat} (h : allCells (chCell2 k) a b hs = true) :
    Cover2 (chMode2 k) chCellBox a b := fun n h1 h2 =>
  match allCells_hinted h n h1 h2 with
  | ⟨x, hx⟩ => .leaf x hx

/-- one certified cell -/
theorem Cover2.one {M : Mode2} {box : Nat → Box} {n : Nat} (h : Certified2 M (box n)) :
    Cover2 M box n (Nat.succ n) := fun _ h1 h2 =>
  (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1) ▸ h

theorem Cover2.trans {M : Mode2} {box : Nat → Box} {a b c : Nat} (h1 : Cover2 M box a b)
    (h2 : Cover2 M box b c) : Cover2 M box a c := fun n ha hc =>
  if hb : n < b then h1 n ha hb else h2 n (Nat.not_lt.mp hb) hc


/-! ## the root grids

Every coordinate interval is an `ivG`.  The cells of a grid with `I × J × K` cells are numbered
`n = (i J + j) K + k`.
* `dir2CellBox`: `(a, b, c) ∈ [1/2, 1] × [1/2, 1] × [0, 7/4]`, cells of side `1/4`, `2 × 2 × 7`;
* `chACellBox`: `(b, al, ga) ∈ [1/4, 1/2] × [-2, 0] × [0, 5]`, cells `1/8 × 1 × 1`, `2 × 2 × 5`;
* `chBCellBox`: `[1/8, 1/4] × [-4, 0] × [0, 5]`, cells `1/8 × 1 × 1`, `1 × 4 × 5`;
* `chCCellBox`: `[0, 1/8] × [-2, 0] × [0, 3]`, cells `1/8 × 1/2 × 1/2`, `1 × 4 × 6`.
-/

/-- `[(n - o) 2^(s-96), (n + 1 - o) 2^(s-96)]` -/
def ivG (s o n : Nat) : I :=
  ⟨Nat.sub (Nat.add Bb (Nat.mul o (2 ^ s))) (Nat.mul n (2 ^ s)),
    Nat.sub (Nat.add Bb (Nat.mul (Nat.succ n) (2 ^ s))) (Nat.mul o (2 ^ s))⟩

/-- cell `n = (2 i + j) 7 + k` of the direct root grid -/
def dir2CellBox (n : Nat) : Box := ⟨ivG 94 0 (n / 14 + 2), ivG 94 0 (n / 7 % 2 + 2), ivG 94 0 (n % 7)⟩

/-- cell `n = (2 i + j) 5 + k` of the chart root grid A -/
def chACellBox (n : Nat) : Box := ⟨ivG 93 0 (n / 10 + 2), ivG 96 2 (n / 5 % 2), ivG 96 0 (n % 5)⟩

/-- cell `n = 5 j + k` of the chart root grid B -/
def chBCellBox (n : Nat) : Box := ⟨ivG 93 0 1, ivG 96 4 (n / 5 % 4), ivG 96 0 (n % 5)⟩

/-- cell `n = 6 j + k` of the chart root grid C -/
def chCCellBox (n : Nat) : Box := ⟨ivG 93 0 0, ivG 95 4 (n / 6 % 4), ivG 95 0 (n % 6)⟩

/-- cell `n` of the grid `box` is certified in the mode `M` by the hint `h` -/
def cellOK (M : Mode2) (box : Nat → Box) (n h : Nat) : Bool :=
  (checkBoxH2 M depth (box n) h).isSome

/-- a run of cells of any grid checked by `allCells` -/
theorem Cover2.cells {M : Mode2} {box : Nat → Box} {a b : Nat} {hs : List Nat}
    (h : allCells (cellOK M box) a b hs = true) : Cover2 M box a b := fun n h1 h2 =>
  match allCells_hinted h n h1 h2 with
  | ⟨x, hx⟩ => .leaf x hx


/-! ## the Taylor-model leaf evaluator

A Taylor model of `C4Check.TF` lives on `t ∈ [-1, 1]⁴`.  The leaf takes `z_i = z̄_i + r_i t_i`
(`z̄`, `r` the centre and the radii of `B`) and `x = x₀(z) + e t₃`.
* The root phase starts from the band `e₀` covering `W₀`.  A step with `ρ` evaluates the model
  of `P` on the band `e` and checks `newtOK ρ`: every zero of `P` there has `|t₃| ≤ ρ` (residual
  and `t₃`-slope at once, so localisation and uniqueness); the band becomes `ρ e`.  At most two
  steps; a step whose code is `0` is skipped, so `c₁ = 0` tests on the a-priori band `e₀`.
* The test phase evaluates the models of the normalized test on the final band and checks
  `det Y - μ g_f > 0` and `tr Y > 0`.
The 48 evaluator bits of the record: the root model and the test model (2 bits each: `W4`, `F4`,
`W5`, `F3`), the codes `c₁`, `c₂` of `ρ₁`, `ρ₂` (8 bits each; code `0` is no step, else
`c = 16 x + m` is `ρ = (16 + m) 2^-(5 + x)`), the `μ` flag (1 bit), `f` (3 bits), `μ` (24 bits,
`m 2^-16`). -/

/-- the parts of a Taylor-model type of `C4Check.TF` that the leaf uses -/
structure TFKit (T : Type) where
  /-- `var_i x r`: the coordinate `val x + (r / 2^96) t_i` -/
  var0 : Nat → Nat → T
  var1 : Nat → Nat → T
  var2 : Nat → Nat → T
  var3 : Nat → Nat → T
  /-- the constant `val x` -/
  ptB : Nat → T
  /-- the model is valid and its range positive -/
  posT : Option T → Bool
  /-- every zero in the box has `|t₃| ≤ ρ / 2^96` -/
  newtOK : Nat → Option T → Bool

def kitW4 : TFKit TF.W4.T :=
  ⟨TF.W4.var0, TF.W4.var1, TF.W4.var2, TF.W4.var3, TF.W4.ptB, TF.W4.posT, TF.W4.newtOK⟩
def kitF4 : TFKit TF.F4.T :=
  ⟨TF.F4.var0, TF.F4.var1, TF.F4.var2, TF.F4.var3, TF.F4.ptB, TF.F4.posT, TF.F4.newtOK⟩
def kitW5 : TFKit TF.W5.T :=
  ⟨TF.W5.var0, TF.W5.var1, TF.W5.var2, TF.W5.var3, TF.W5.ptB, TF.W5.posT, TF.W5.newtOK⟩
def kitF3 : TFKit TF.F3.T :=
  ⟨TF.F3.var0, TF.F3.var1, TF.F3.var2, TF.F3.var3, TF.F3.ptB, TF.F3.posT, TF.F3.newtOK⟩

section
variable {α : Type} [Ops α]

/-- `X₀ + Σ J_i d_i + Σ_{i≤j} H_ij d_i d_j + w` -/
def shearX (X0 J0 J1 J2 H00 H01 H02 H11 H12 H22 d0 d1 d2 w : α) : α :=
  X0 + (J0 * d0 + J1 * d1 + J2 * d2) +
    (d0 * (H00 * d0 + H01 * d1 + H02 * d2) + d1 * (H11 * d1 + H12 * d2) + H22 * Ops.sq d2) + w

end

/-- the models of the box coordinates and of `x = x₀(z) + e t₃`, fed to a formula `F` -/
def tfAt {T β : Type} [Ops (Option T)] (K : TFKit T)
    (F : Option T → Option T → Option T → Option T → β) (B : Box) (sh : Shear) (e : Nat) : β :=
  F (some (K.var0 (I.ctr B.X0) (I.radAt B.X0 (I.ctr B.X0))))
    (some (K.var1 (I.ctr B.X1) (I.radAt B.X1 (I.ctr B.X1))))
    (some (K.var2 (I.ctr B.X2) (I.radAt B.X2 (I.ctr B.X2))))
    (shearX (some (K.ptB sh.X0)) (some (K.ptB sh.J0)) (some (K.ptB sh.J1)) (some (K.ptB sh.J2))
      (some (K.ptB sh.H00)) (some (K.ptB sh.H01)) (some (K.ptB sh.H02)) (some (K.ptB sh.H11))
      (some (K.ptB sh.H12)) (some (K.ptB sh.H22))
      (some (K.var0 Bb (I.radAt B.X0 (I.ctr B.X0)))) (some (K.var1 Bb (I.radAt B.X1 (I.ctr B.X1))))
      (some (K.var2 Bb (I.radAt B.X2 (I.ctr B.X2)))) (some (K.var3 Bb e)))

/-- `ρ` of an 8-bit code `c = 16 x + m ≠ 0`, as an offset: `(16 + m) 2^-(5 + x)` (the code `0` is
no step, see `tfStep2`) -/
def rhoDec (c : Nat) : Nat :=
  Nat.shiftLeft (Nat.add 16 (Nat.land c 15)) (Nat.sub 91 (Nat.shiftRight c 4))

/-- one localisation step: if `newtOK ρ` holds for the model of `P` on the band `e`, the band
`ρ e` -/
def tfStep {T : Type} [Ops (Option T)] (K : TFKit T)
    (PF : ∀ {α : Type} [Ops α], α → α → α → α → α) (B : Box) (sh : Shear) (rho e : Nat) :
    Option Nat :=
  cont (K.newtOK rho (tfAt K PF B sh e)) (some (I.up (Nat.mul rho e)))

/-- the step of code `c`; the code `0` takes no step and keeps the band `e` -/
def tfStep2 {T : Type} [Ops (Option T)] (K : TFKit T)
    (PF : ∀ {α : Type} [Ops α], α → α → α → α → α) (B : Box) (sh : Shear) (c e : Nat) :
    Option Nat :=
  sel (Nat.beq c 0) (some e) (tfStep K PF B sh (rhoDec c) e)

/-- the root phase: the final band (`c1 = 0`: no Newton step, the a-priori band `e0`) -/
def tfRoot {T : Type} [Ops (Option T)] (K : TFKit T)
    (PF : ∀ {α : Type} [Ops α], α → α → α → α → α) (B : Box) (sh : Shear) (e0 c1 c2 : Nat) :
    Option Nat :=
  (tfStep2 K PF B sh c1 e0).bind (tfStep2 K PF B sh c2)

/-- the constraint `g_f` (none for `f > 5`) -/
def gselG {β : Type} (g : Six (Option β)) (f : Nat) : Option β :=
  sel (Nat.beq f 0) g.x1 (sel (Nat.beq f 1) g.x2 (sel (Nat.beq f 2) g.x3
    (sel (Nat.beq f 3) g.x4 (sel (Nat.beq f 4) g.x5 (sel (Nat.beq f 5) g.x6 none)))))

/-- `det Y - μ g_f > 0` (or `det Y > 0` if `mf = 0`) and `tr Y > 0` for the models -/
def tftest {T : Type} [Ops (Option T)] (K : TFKit T) (mf f mu : Nat) (o : Out (Option T)) :
    Bool :=
  both (K.posT (sel (Nat.beq mf 0) o.det (o.det - some (K.ptB mu) * gselG o.g f))) (K.posT o.tr)

/-- the test phase on the band `e` -/
def tfTest {T : Type} [Ops (Option T)] (K : TFKit T)
    (OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α) (B : Box) (sh : Shear)
    (e mf f mu : Nat) : Bool :=
  tftest K mf f mu (tfAt K OF B sh e)

/-- the root phase in the model `m` -/
def rootSel (PF : ∀ {α : Type} [Ops α], α → α → α → α → α) (B : Box) (sh : Shear)
    (m e0 c1 c2 : Nat) : Option Nat :=
  sel (Nat.beq m 0) (tfRoot kitW4 PF B sh e0 c1 c2)
    (sel (Nat.beq m 1) (tfRoot kitF4 PF B sh e0 c1 c2)
      (sel (Nat.beq m 2) (tfRoot kitW5 PF B sh e0 c1 c2) (tfRoot kitF3 PF B sh e0 c1 c2)))

/-- the test phase in the model `m` -/
def testSel (OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α) (B : Box) (sh : Shear)
    (m e mf f mu : Nat) : Bool :=
  sel (Nat.beq m 0) (tfTest kitW4 OF B sh e mf f mu)
    (sel (Nat.beq m 1) (tfTest kitF4 OF B sh e mf f mu)
      (sel (Nat.beq m 2) (tfTest kitW5 OF B sh e mf f mu) (tfTest kitF3 OF B sh e mf f mu)))

/-- `k e` for the band `e` of a successful root phase -/
def afterRoot (k : Nat → Bool) : Option Nat → Bool
  | some e => k e
  | none => false

/-- the Taylor-model leaf on `B` for the shear `sh`, the evaluator bits `fl` and the band `W` -/
def evTF (PF : ∀ {α : Type} [Ops α], α → α → α → α → α)
    (OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α)
    (B : Box) (sh : Shear) (fl : Nat) (W : I) : Bool :=
  afterRoot
    (fun e => testSel OF B sh (Nat.land (Nat.shiftRight fl 2) 3) e
      (Nat.land (Nat.shiftRight fl 20) 1) (Nat.land (Nat.shiftRight fl 21) 7)
      (Nat.add Bb (Nat.shiftLeft (Nat.land (Nat.shiftRight fl 24) 16777215) 80)))
    (rootSel PF B sh (Nat.land fl 3) (I.mx (Nat.sub W.L Bb) (Nat.sub W.H Bb))
      (Nat.land (Nat.shiftRight fl 4) 255) (Nat.land (Nat.shiftRight fl 12) 255))

/-- the direct chart with the Taylor-model leaf as its own evaluator -/
def dirModeTF : Mode2 := { dirMode2 with ev2 := evTF @dirP2 @dirMidN }

/-- the blow-up chart with the Taylor-model leaf as its own evaluator -/
def chModeTF (k : Nat) : Mode2 := { chMode2 k with ev2 := evTF @chP2 @chMidN }

/-! ### the minimal model set: `W4` and `F4`

The same leaf with the model codes `0` (`W4`) and `1` (`F4`) only; the codes `2`, `3` fail. -/

/-- the root phase in `W4` or `F4` -/
def rootSelM (PF : ∀ {α : Type} [Ops α], α → α → α → α → α) (B : Box) (sh : Shear)
    (m e0 c1 c2 : Nat) : Option Nat :=
  sel (Nat.beq m 0) (tfRoot kitW4 PF B sh e0 c1 c2)
    (sel (Nat.beq m 1) (tfRoot kitF4 PF B sh e0 c1 c2) none)

/-- the test phase in `W4` or `F4` -/
def testSelM (OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α) (B : Box) (sh : Shear)
    (m e mf f mu : Nat) : Bool :=
  sel (Nat.beq m 0) (tfTest kitW4 OF B sh e mf f mu)
    (sel (Nat.beq m 1) (tfTest kitF4 OF B sh e mf f mu) false)

/-- `evTF` with the models `W4` and `F4` only -/
def evTFM (PF : ∀ {α : Type} [Ops α], α → α → α → α → α)
    (OF : ∀ {α : Type} [Ops α], α → α → α → α → Out α)
    (B : Box) (sh : Shear) (fl : Nat) (W : I) : Bool :=
  afterRoot
    (fun e => testSelM OF B sh (Nat.land (Nat.shiftRight fl 2) 3) e
      (Nat.land (Nat.shiftRight fl 20) 1) (Nat.land (Nat.shiftRight fl 21) 7)
      (Nat.add Bb (Nat.shiftLeft (Nat.land (Nat.shiftRight fl 24) 16777215) 80)))
    (rootSelM PF B sh (Nat.land fl 3) (I.mx (Nat.sub W.L Bb) (Nat.sub W.H Bb))
      (Nat.land (Nat.shiftRight fl 4) 255) (Nat.land (Nat.shiftRight fl 12) 255))

/-- the direct chart with the `W4`/`F4` Taylor-model leaf -/
def dirModeTFM : Mode2 := { dirMode2 with ev2 := evTFM @dirP2 @dirMidN }

/-- the blow-up chart with the `W4`/`F4` Taylor-model leaf -/
def chModeTFM (k : Nat) : Mode2 := { chMode2 k with ev2 := evTFM @chP2 @chMidN }

end C4
