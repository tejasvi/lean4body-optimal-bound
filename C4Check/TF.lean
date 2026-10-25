module

public import C4Check.Formulas2

@[expose] public section

/-!
# Fixed-point Taylor models (generated code)

A model lives on the normalized box `t ∈ [-1, 1]⁴`: `t₀, t₁, t₂` are the box coordinates (the caller
scales them, `z_i = z̄_i + r_i t_i`) and `t₃` is the offset of the dependent coordinate from its hint
polynomial (`x = X(t) + e t₃`).  It is a polynomial with *point* coefficients `c_k` (the value of `X` is
`val X = (X - Bp) / 2^96`, bias `Bp = 2^400`) in a fixed set of monomials `t^(m_k)`, a remainder interval
`R` (an `I`, bias `2^256`), a bound `A` on `Σ_k |c_k - Bp|`, a flag `ok`, and the statistics `st` of the
coefficients (computed lazily, at most once per model).  `ok = true` means: every coefficient operation
so far was exact before its final rounding, so the model encloses its function:
`f t - Σ_k val(c_k) t^(m_k) ∈ R` for every `t` in the box.

* A product coefficient `Σ (X_i - Bp)(Y_j - Bp)` is `Σ X_i Y_j mod 2^400` (shifted by `2^399`) when every
  `|X - Bp| ≤ 2^170`, so the bias never has to be subtracted (`fin`).
* Products of graded degree `≥ N` are bounded on the box by the grade norms `n_d = Σ_{deg k = d} |c_k - Bp|`
  (`|t| ≤ 1`), and every coefficient rounding (`≤ 2^-97`) by `NR` offset units.
* `1/v` and `√v` use the residual identities `1/v = Y + (1 - vY)/v` and `√v = Y + (v - Y²)/(√v + Y)`
  for a polynomial `Y` (the truncated series; any `Y` is sound).
-/

namespace C4
namespace TF

/-- the bias of point coefficients -/
def Bp : Nat := 2 ^ 400
/-- `2 Bp` -/
def Bp2 : Nat := 2 ^ 401
/-- `Bp - Bb` (from the bias of `I` to `Bp`) -/
def DB : Nat := 2 ^ 400 - 2 ^ 256
/-- `Bp + Bb` -/
def BpB : Nat := 2 ^ 400 + 2 ^ 256
/-- `Σ_k |c_k - Bp| ≤ LIM` for both factors makes every product coefficient exact -/
def LIM : Nat := 2 ^ 170
/-- the bound that keeps sums and negations exact -/
def LIMA : Nat := 2 ^ 390
/-- `2^399 + 2^95` -/
def K1 : Nat := 2 ^ 399 + 2 ^ 95
/-- `2^400 - 1` -/
def M400 : Nat := 2 ^ 400 - 1
/-- `2^400 - 2^303` -/
def K2 : Nat := 2 ^ 400 - 2 ^ 303

/-- the coefficient `Bp + round(s / 2^96)` from `S = Σ X_i Y_j ≡ s (mod 2^400)`, `|s| < 2^398` -/
def fin (S : Nat) : Nat := Nat.add (Nat.shiftRight (Nat.land (Nat.add S K1) M400) 96) K2

/-- the product of two points (rounded; series only) -/
def pmul1 (x y : Nat) : Nat := fin (Nat.mul x y)

/-- `|X - Bp|` -/
def pabs (x : Nat) : Nat := Nat.add (Nat.sub x Bp) (Nat.sub Bp x)

/-- `1 / val x` (rounded; series only) -/
def rcp (x : Nat) : Nat :=
  sel (Nat.ble Bp x) (Nat.add Bp (Nat.div S2K (Nat.sub x Bp))) (Nat.sub Bp (Nat.div S2K (Nat.sub Bp x)))

/-- `√(val x)` (rounded; series only) -/
def rsq (x : Nat) : Nat := Nat.add Bp (I.isq (Nat.shiftLeft (Nat.sub x Bp) 96))

/-- the points `±n / d` -/
def frac (n d : Nat) : Nat := Nat.add Bp (Nat.div (Nat.mul n ONE) d)
def fracN (n d : Nat) : Nat := Nat.sub Bp (Nat.div (Nat.mul n ONE) d)

/-- `A > 0`: the lower end is positive -/
def posLo (A : I) : Bool := sel (Nat.ble Bb A.L) false true

/-- an offset bounding `|v|` for `v ∈ A` -/
def rmag (A : I) : Nat := I.mx (Nat.sub A.L Bb) (Nat.sub A.H Bb)

/-- the residual interval `1 / (√V + W)`, given `√V` (if defined) -/
def sqrtDen (W : I) : Option I → Option I
  | some s => (s.add W).inv
  | none => none

end TF

namespace TF.W4

/-! ## `W4`: graded degree `< 4` for grades `[1, 1, 1, 2]`, 24 monomials, 98 coefficient products per product

`c0` 1, `c1` t0, `c2` t1, `c3` t2, `c4` t0^2, `c5` t0·t1, `c6` t0·t2, `c7` t1^2, `c8` t1·t2, `c9` t2^2, `c10` t3, `c11` t0^3, `c12` t0^2·t1, `c13` t0^2·t2, `c14` t0·t1^2, `c15` t0·t1·t2, `c16` t0·t2^2, `c17` t0·t3, `c18` t1^3, `c19` t1^2·t2, `c20` t1·t2^2, `c21` t1·t3, `c22` t2^3, `c23` t2·t3. -/

/-- the rounding allowance of a product, in offset units -/
def NR : Nat := 24
/-- the number of coefficient products of a product -/
def NP : Nat := 98

/-- grade norms `n_d = Σ_{deg k = d} |c_k - Bp|`, the range `⟨lo, hi⟩` of the polynomial on the box, and
`as = Σ_k |c_k - Bp|` -/
structure St where
  n1 : Nat
  n2 : Nat
  n3 : Nat
  lo : Nat
  hi : Nat
  as : Nat

def statsOf (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : Nat) : St :=
  ⟨(Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.sub c7 Bp)) (Nat.sub Bp c7)) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11)) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))), Nat.sub (Nat.add (Nat.add BpB (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23)))) (Nat.add (Nat.add (Nat.sub Bp c4) (Nat.sub Bp c7)) (Nat.sub Bp c9))) c0, Nat.sub (Nat.add (Nat.add c0 Bb) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub c7 Bp)) (Nat.sub c9 Bp)))) Bp, Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c0 Bp) (Nat.sub Bp c0)) (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.sub c7 Bp)) (Nat.sub Bp c7)) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11)) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23)))⟩

structure T where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
  c8 : Nat
  c9 : Nat
  c10 : Nat
  c11 : Nat
  c12 : Nat
  c13 : Nat
  c14 : Nat
  c15 : Nat
  c16 : Nat
  c17 : Nat
  c18 : Nat
  c19 : Nat
  c20 : Nat
  c21 : Nat
  c22 : Nat
  c23 : Nat
  R : I
  A : Nat
  ok : Bool
  st : St

def mk (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : Nat) (R : I) (A : Nat) (ok : Bool) : T :=
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, R, A, ok, statsOf c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23⟩

/-- the range of the polynomial part -/
def prng (u : T) : I := ⟨u.st.lo, u.st.hi⟩

/-- the range of the model -/
def rng (u : T) : I := (prng u).add u.R

def add (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 v.c0) Bp) (Nat.sub (Nat.add u.c1 v.c1) Bp) (Nat.sub (Nat.add u.c2 v.c2) Bp) (Nat.sub (Nat.add u.c3 v.c3) Bp) (Nat.sub (Nat.add u.c4 v.c4) Bp) (Nat.sub (Nat.add u.c5 v.c5) Bp) (Nat.sub (Nat.add u.c6 v.c6) Bp) (Nat.sub (Nat.add u.c7 v.c7) Bp) (Nat.sub (Nat.add u.c8 v.c8) Bp) (Nat.sub (Nat.add u.c9 v.c9) Bp) (Nat.sub (Nat.add u.c10 v.c10) Bp) (Nat.sub (Nat.add u.c11 v.c11) Bp) (Nat.sub (Nat.add u.c12 v.c12) Bp) (Nat.sub (Nat.add u.c13 v.c13) Bp) (Nat.sub (Nat.add u.c14 v.c14) Bp) (Nat.sub (Nat.add u.c15 v.c15) Bp) (Nat.sub (Nat.add u.c16 v.c16) Bp) (Nat.sub (Nat.add u.c17 v.c17) Bp) (Nat.sub (Nat.add u.c18 v.c18) Bp) (Nat.sub (Nat.add u.c19 v.c19) Bp) (Nat.sub (Nat.add u.c20 v.c20) Bp) (Nat.sub (Nat.add u.c21 v.c21) Bp) (Nat.sub (Nat.add u.c22 v.c22) Bp) (Nat.sub (Nat.add u.c23 v.c23) Bp)
    (u.R.add v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def sub (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 Bp) v.c0) (Nat.sub (Nat.add u.c1 Bp) v.c1) (Nat.sub (Nat.add u.c2 Bp) v.c2) (Nat.sub (Nat.add u.c3 Bp) v.c3) (Nat.sub (Nat.add u.c4 Bp) v.c4) (Nat.sub (Nat.add u.c5 Bp) v.c5) (Nat.sub (Nat.add u.c6 Bp) v.c6) (Nat.sub (Nat.add u.c7 Bp) v.c7) (Nat.sub (Nat.add u.c8 Bp) v.c8) (Nat.sub (Nat.add u.c9 Bp) v.c9) (Nat.sub (Nat.add u.c10 Bp) v.c10) (Nat.sub (Nat.add u.c11 Bp) v.c11) (Nat.sub (Nat.add u.c12 Bp) v.c12) (Nat.sub (Nat.add u.c13 Bp) v.c13) (Nat.sub (Nat.add u.c14 Bp) v.c14) (Nat.sub (Nat.add u.c15 Bp) v.c15) (Nat.sub (Nat.add u.c16 Bp) v.c16) (Nat.sub (Nat.add u.c17 Bp) v.c17) (Nat.sub (Nat.add u.c18 Bp) v.c18) (Nat.sub (Nat.add u.c19 Bp) v.c19) (Nat.sub (Nat.add u.c20 Bp) v.c20) (Nat.sub (Nat.add u.c21 Bp) v.c21) (Nat.sub (Nat.add u.c22 Bp) v.c22) (Nat.sub (Nat.add u.c23 Bp) v.c23)
    (u.R.sub v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def neg (u : T) : T :=
  mk (Nat.sub Bp2 u.c0) (Nat.sub Bp2 u.c1) (Nat.sub Bp2 u.c2) (Nat.sub Bp2 u.c3) (Nat.sub Bp2 u.c4) (Nat.sub Bp2 u.c5) (Nat.sub Bp2 u.c6) (Nat.sub Bp2 u.c7) (Nat.sub Bp2 u.c8) (Nat.sub Bp2 u.c9) (Nat.sub Bp2 u.c10) (Nat.sub Bp2 u.c11) (Nat.sub Bp2 u.c12) (Nat.sub Bp2 u.c13) (Nat.sub Bp2 u.c14) (Nat.sub Bp2 u.c15) (Nat.sub Bp2 u.c16) (Nat.sub Bp2 u.c17) (Nat.sub Bp2 u.c18) (Nat.sub Bp2 u.c19) (Nat.sub Bp2 u.c20) (Nat.sub Bp2 u.c21) (Nat.sub Bp2 u.c22) (Nat.sub Bp2 u.c23) u.R.neg u.A (u.ok && Nat.ble u.A LIMA)

def mc0 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c0) 0)
def mc1 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c1) (Nat.add (Nat.mul u.c1 v.c0) 0))
def mc2 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c2) (Nat.add (Nat.mul u.c2 v.c0) 0))
def mc3 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c3) (Nat.add (Nat.mul u.c3 v.c0) 0))
def mc4 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c4) (Nat.add (Nat.mul u.c1 v.c1) (Nat.add (Nat.mul u.c4 v.c0) 0)))
def mc5 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c5) (Nat.add (Nat.mul u.c1 v.c2) (Nat.add (Nat.mul u.c2 v.c1) (Nat.add (Nat.mul u.c5 v.c0) 0))))
def mc6 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c6) (Nat.add (Nat.mul u.c1 v.c3) (Nat.add (Nat.mul u.c3 v.c1) (Nat.add (Nat.mul u.c6 v.c0) 0))))
def mc7 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c7) (Nat.add (Nat.mul u.c2 v.c2) (Nat.add (Nat.mul u.c7 v.c0) 0)))
def mc8 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c8) (Nat.add (Nat.mul u.c2 v.c3) (Nat.add (Nat.mul u.c3 v.c2) (Nat.add (Nat.mul u.c8 v.c0) 0))))
def mc9 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c9) (Nat.add (Nat.mul u.c3 v.c3) (Nat.add (Nat.mul u.c9 v.c0) 0)))
def mc10 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c10) (Nat.add (Nat.mul u.c10 v.c0) 0))
def mc11 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c11) (Nat.add (Nat.mul u.c1 v.c4) (Nat.add (Nat.mul u.c4 v.c1) (Nat.add (Nat.mul u.c11 v.c0) 0))))
def mc12 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c12) (Nat.add (Nat.mul u.c1 v.c5) (Nat.add (Nat.mul u.c2 v.c4) (Nat.add (Nat.mul u.c4 v.c2) (Nat.add (Nat.mul u.c5 v.c1) (Nat.add (Nat.mul u.c12 v.c0) 0))))))
def mc13 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c13) (Nat.add (Nat.mul u.c1 v.c6) (Nat.add (Nat.mul u.c3 v.c4) (Nat.add (Nat.mul u.c4 v.c3) (Nat.add (Nat.mul u.c6 v.c1) (Nat.add (Nat.mul u.c13 v.c0) 0))))))
def mc14 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c14) (Nat.add (Nat.mul u.c1 v.c7) (Nat.add (Nat.mul u.c2 v.c5) (Nat.add (Nat.mul u.c5 v.c2) (Nat.add (Nat.mul u.c7 v.c1) (Nat.add (Nat.mul u.c14 v.c0) 0))))))
def mc15 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c15) (Nat.add (Nat.mul u.c1 v.c8) (Nat.add (Nat.mul u.c2 v.c6) (Nat.add (Nat.mul u.c3 v.c5) (Nat.add (Nat.mul u.c5 v.c3) (Nat.add (Nat.mul u.c6 v.c2) (Nat.add (Nat.mul u.c8 v.c1) (Nat.add (Nat.mul u.c15 v.c0) 0))))))))
def mc16 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c16) (Nat.add (Nat.mul u.c1 v.c9) (Nat.add (Nat.mul u.c3 v.c6) (Nat.add (Nat.mul u.c6 v.c3) (Nat.add (Nat.mul u.c9 v.c1) (Nat.add (Nat.mul u.c16 v.c0) 0))))))
def mc17 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c17) (Nat.add (Nat.mul u.c1 v.c10) (Nat.add (Nat.mul u.c10 v.c1) (Nat.add (Nat.mul u.c17 v.c0) 0))))
def mc18 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c18) (Nat.add (Nat.mul u.c2 v.c7) (Nat.add (Nat.mul u.c7 v.c2) (Nat.add (Nat.mul u.c18 v.c0) 0))))
def mc19 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c19) (Nat.add (Nat.mul u.c2 v.c8) (Nat.add (Nat.mul u.c3 v.c7) (Nat.add (Nat.mul u.c7 v.c3) (Nat.add (Nat.mul u.c8 v.c2) (Nat.add (Nat.mul u.c19 v.c0) 0))))))
def mc20 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c20) (Nat.add (Nat.mul u.c2 v.c9) (Nat.add (Nat.mul u.c3 v.c8) (Nat.add (Nat.mul u.c8 v.c3) (Nat.add (Nat.mul u.c9 v.c2) (Nat.add (Nat.mul u.c20 v.c0) 0))))))
def mc21 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c21) (Nat.add (Nat.mul u.c2 v.c10) (Nat.add (Nat.mul u.c10 v.c2) (Nat.add (Nat.mul u.c21 v.c0) 0))))
def mc22 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c22) (Nat.add (Nat.mul u.c3 v.c9) (Nat.add (Nat.mul u.c9 v.c3) (Nat.add (Nat.mul u.c22 v.c0) 0))))
def mc23 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c23) (Nat.add (Nat.mul u.c3 v.c10) (Nat.add (Nat.mul u.c10 v.c3) (Nat.add (Nat.mul u.c23 v.c0) 0))))

/-- the product -/
def mul (u v : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 v.st.n3) (Nat.mul u.st.n2 v.st.n2)) (Nat.mul u.st.n2 v.st.n3)) (Nat.mul u.st.n3 v.st.n1)) (Nat.mul u.st.n3 v.st.n2)) (Nat.mul u.st.n3 v.st.n3))) NR)
  mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v)
    ((((prng u).mul v.R).add (u.R.mul (rng v))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as v.st.as) NP)) NR)
    (u.ok && v.ok && Nat.ble u.st.as LIM && Nat.ble v.st.as LIM)

def sc0 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (0) 1) (Nat.add (Nat.mul u.c0 u.c0) 0))
def sc1 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c1) 0) 1) (0))
def sc2 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c2) 0) 1) (0))
def sc3 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c3) 0) 1) (0))
def sc4 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c4) 0) 1) (Nat.add (Nat.mul u.c1 u.c1) 0))
def sc5 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c5) (Nat.add (Nat.mul u.c1 u.c2) 0)) 1) (0))
def sc6 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c6) (Nat.add (Nat.mul u.c1 u.c3) 0)) 1) (0))
def sc7 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c7) 0) 1) (Nat.add (Nat.mul u.c2 u.c2) 0))
def sc8 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c8) (Nat.add (Nat.mul u.c2 u.c3) 0)) 1) (0))
def sc9 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c9) 0) 1) (Nat.add (Nat.mul u.c3 u.c3) 0))
def sc10 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c10) 0) 1) (0))
def sc11 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c11) (Nat.add (Nat.mul u.c1 u.c4) 0)) 1) (0))
def sc12 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c12) (Nat.add (Nat.mul u.c1 u.c5) (Nat.add (Nat.mul u.c2 u.c4) 0))) 1) (0))
def sc13 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c13) (Nat.add (Nat.mul u.c1 u.c6) (Nat.add (Nat.mul u.c3 u.c4) 0))) 1) (0))
def sc14 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c14) (Nat.add (Nat.mul u.c1 u.c7) (Nat.add (Nat.mul u.c2 u.c5) 0))) 1) (0))
def sc15 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c15) (Nat.add (Nat.mul u.c1 u.c8) (Nat.add (Nat.mul u.c2 u.c6) (Nat.add (Nat.mul u.c3 u.c5) 0)))) 1) (0))
def sc16 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c16) (Nat.add (Nat.mul u.c1 u.c9) (Nat.add (Nat.mul u.c3 u.c6) 0))) 1) (0))
def sc17 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c17) (Nat.add (Nat.mul u.c1 u.c10) 0)) 1) (0))
def sc18 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c18) (Nat.add (Nat.mul u.c2 u.c7) 0)) 1) (0))
def sc19 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c19) (Nat.add (Nat.mul u.c2 u.c8) (Nat.add (Nat.mul u.c3 u.c7) 0))) 1) (0))
def sc20 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c20) (Nat.add (Nat.mul u.c2 u.c9) (Nat.add (Nat.mul u.c3 u.c8) 0))) 1) (0))
def sc21 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c21) (Nat.add (Nat.mul u.c2 u.c10) 0)) 1) (0))
def sc22 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c22) (Nat.add (Nat.mul u.c3 u.c9) 0)) 1) (0))
def sc23 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c23) (Nat.add (Nat.mul u.c3 u.c10) 0)) 1) (0))

/-- the square (each symmetric product once) -/
def sq (u : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 u.st.n3) (Nat.mul u.st.n2 u.st.n2)) (Nat.mul u.st.n2 u.st.n3)) (Nat.mul u.st.n3 u.st.n1)) (Nat.mul u.st.n3 u.st.n2)) (Nat.mul u.st.n3 u.st.n3))) NR)
  mk (sc0 u) (sc1 u) (sc2 u) (sc3 u) (sc4 u) (sc5 u) (sc6 u) (sc7 u) (sc8 u) (sc9 u) (sc10 u) (sc11 u) (sc12 u) (sc13 u) (sc14 u) (sc15 u) (sc16 u) (sc17 u) (sc18 u) (sc19 u) (sc20 u) (sc21 u) (sc22 u) (sc23 u)
    ((((prng u).mul u.R).add (u.R.mul (rng u))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as u.st.as) NP)) NR)
    (u.ok && Nat.ble u.st.as LIM)

/-- the truncated product of the polynomial parts (series only) -/
def pmul (u v : T) : T := mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v) I.zero 0 true

/-- the constant `n` -/
def cst (n : Int) : T :=
  match n with
  | .ofNat j => mk (Nat.add Bp (Nat.mul j ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul j ONE) true
  | .negSucc j => mk (Nat.sub Bp (Nat.mul (Nat.succ j) ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul (Nat.succ j) ONE)
      (Nat.ble (Nat.mul (Nat.succ j) ONE) Bp)

/-- the point `(x - Bb) / 2^96` (`x` with the bias of `I`) -/
def ptB (x : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t0` -/
def var0 (x r : Nat) : T := mk (Nat.add x DB) (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t1` -/
def var1 (x r : Nat) : T := mk (Nat.add x DB) Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t2` -/
def var2 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t3` -/
def var3 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- `u` without its constant term, times the point `s` (series only) -/
def tail (s : Nat) (u : T) : T := mk Bp (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) I.zero 0 true

/-- `c + u` for a point `c` (series only) -/
def addc (c : Nat) (u : T) : T := mk (Nat.sub (Nat.add c u.c0) Bp) u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 I.zero 0 true

/-- `c + s u` for points `c`, `s` (series only) -/
def axpy (c s : Nat) (u : T) : T :=
  mk (Nat.sub (Nat.add c (pmul1 s u.c0)) Bp) (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) I.zero 0 true

/-- the polynomial of `u` with the remainder `R`, the exact `A` and the flag `ok` -/
def withR (u : T) (R : I) (ok : Bool) : T := mk u.c0 u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs u.c0) (pabs u.c1)) (pabs u.c2)) (pabs u.c3)) (pabs u.c4)) (pabs u.c5)) (pabs u.c6)) (pabs u.c7)) (pabs u.c8)) (pabs u.c9)) (pabs u.c10)) (pabs u.c11)) (pabs u.c12)) (pabs u.c13)) (pabs u.c14)) (pabs u.c15)) (pabs u.c16)) (pabs u.c17)) (pabs u.c18)) (pabs u.c19)) (pabs u.c20)) (pabs u.c21)) (pabs u.c22)) (pabs u.c23)) ok

/-- the truncated series of `1/v` (any polynomial is sound) -/
def invSeries (v : T) : T :=
  let y0 := rcp v.c0
  let t := tail (Nat.sub Bp2 y0) v
  let P3 := addc (Nat.add Bp ONE) t
  let P2 := addc (Nat.add Bp ONE) (pmul t P3)
  let P1 := addc (Nat.add Bp ONE) (pmul t P2)
  axpy Bp y0 P1

/-- the truncated series of `√v` (any polynomial is sound) -/
def sqrtSeries (v : T) : T :=
  let s0 := rsq v.c0
  let t := tail (rcp v.c0) v
  let Q3 := addc (frac 1 16) (cst 0)
  let Q2 := addc (fracN 1 8) (pmul t Q3)
  let Q1 := addc (frac 1 2) (pmul t Q2)
  axpy s0 s0 (pmul t Q1)

/-- `Y` with the remainder `rng(E) · iv`, given `iv` (if defined) -/
def resid (Y E : T) (ok : Bool) : Option I → Option T
  | some iv => some (withR Y ((rng E).mul iv) (ok && E.ok))
  | none => none

def inv (v : T) : Option T :=
  let Y := withR (invSeries v) I.zero true
  resid Y (sub (cst 1) (mul v Y)) v.ok (rng v).inv

def sqrt (v : T) : Option T :=
  let Y := withR (sqrtSeries v) I.zero true
  resid Y (sub v (mul Y Y)) v.ok (sqrtDen (rng Y) (rng v).sqrt)

def div (u v : T) : Option T := Option.map (mul u) (inv v)

/-- Taylor-model arithmetic -/
instance tfOps : Ops (Option T) where
  add x y := match x, y with | some a, some b => some (add a b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (sub a b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (mul a b) | _, _ => none
  div x y := match x, y with | some a, some b => div a b | _, _ => none
  neg x := match x with | some a => some (neg a) | none => none
  sqrt x := match x with | some a => sqrt a | none => none
  sq x := match x with | some a => some (sq a) | none => none
  ofInt n := some (cst n)

/-- the model is valid and its range is positive -/
def posT : Option T → Bool
  | some u => u.ok && posLo (rng u)
  | none => false

/-- every zero of the enclosed function in the box has `|t₃| ≤ ρ/2^96`: writing the polynomial as
`p₀(t) + t₃ q(t)`, `|t₃| |q| ≤ |p₀| + |R|` at a zero, and `|q| ≥ qmin` -/
def newtOK (rho : Nat) : Option T → Bool
  | some p =>
    let qmin := Nat.sub (pabs p.c10) (Nat.add (Nat.add (pabs p.c17) (pabs p.c21)) (pabs p.c23))
    p.ok && Nat.ble 1 qmin &&
      Nat.ble (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c0) (pabs p.c1)) (pabs p.c2)) (pabs p.c3)) (pabs p.c4)) (pabs p.c5)) (pabs p.c6)) (pabs p.c7)) (pabs p.c8)) (pabs p.c9)) (pabs p.c11)) (pabs p.c12)) (pabs p.c13)) (pabs p.c14)) (pabs p.c15)) (pabs p.c16)) (pabs p.c18)) (pabs p.c19)) (pabs p.c20)) (pabs p.c22)) (rmag p.R)) ONE) (Nat.mul rho qmin)
  | none => false

end TF.W4

namespace TF.F4

/-! ## `F4`: graded degree `< 4` for grades `[1, 1, 1, 1]`, 35 monomials, 165 coefficient products per product

`c0` 1, `c1` t0, `c2` t1, `c3` t2, `c4` t3, `c5` t0^2, `c6` t0·t1, `c7` t0·t2, `c8` t0·t3, `c9` t1^2, `c10` t1·t2, `c11` t1·t3, `c12` t2^2, `c13` t2·t3, `c14` t3^2, `c15` t0^3, `c16` t0^2·t1, `c17` t0^2·t2, `c18` t0^2·t3, `c19` t0·t1^2, `c20` t0·t1·t2, `c21` t0·t1·t3, `c22` t0·t2^2, `c23` t0·t2·t3, `c24` t0·t3^2, `c25` t1^3, `c26` t1^2·t2, `c27` t1^2·t3, `c28` t1·t2^2, `c29` t1·t2·t3, `c30` t1·t3^2, `c31` t2^3, `c32` t2^2·t3, `c33` t2·t3^2, `c34` t3^3. -/

/-- the rounding allowance of a product, in offset units -/
def NR : Nat := 35
/-- the number of coefficient products of a product -/
def NP : Nat := 165

/-- grade norms `n_d = Σ_{deg k = d} |c_k - Bp|`, the range `⟨lo, hi⟩` of the polynomial on the box, and
`as = Σ_k |c_k - Bp|` -/
structure St where
  n1 : Nat
  n2 : Nat
  n3 : Nat
  lo : Nat
  hi : Nat
  as : Nat

def statsOf (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 : Nat) : St :=
  ⟨(Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5)) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.sub c12 Bp)) (Nat.sub Bp c12)) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.sub c14 Bp)) (Nat.sub Bp c14)), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15)) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c27 Bp) (Nat.sub Bp c27))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c29 Bp) (Nat.sub Bp c29))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))), Nat.sub (Nat.add (Nat.add BpB (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c27 Bp) (Nat.sub Bp c27))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c29 Bp) (Nat.sub Bp c29))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34)))) (Nat.add (Nat.add (Nat.add (Nat.sub Bp c5) (Nat.sub Bp c9)) (Nat.sub Bp c12)) (Nat.sub Bp c14))) c0, Nat.sub (Nat.add (Nat.add c0 Bb) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c27 Bp) (Nat.sub Bp c27))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c29 Bp) (Nat.sub Bp c29))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))) (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub c9 Bp)) (Nat.sub c12 Bp)) (Nat.sub c14 Bp)))) Bp, Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c0 Bp) (Nat.sub Bp c0)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5)) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.sub c12 Bp)) (Nat.sub Bp c12)) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.sub c14 Bp)) (Nat.sub Bp c14))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15)) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c27 Bp) (Nat.sub Bp c27))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c29 Bp) (Nat.sub Bp c29))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34)))⟩

structure T where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
  c8 : Nat
  c9 : Nat
  c10 : Nat
  c11 : Nat
  c12 : Nat
  c13 : Nat
  c14 : Nat
  c15 : Nat
  c16 : Nat
  c17 : Nat
  c18 : Nat
  c19 : Nat
  c20 : Nat
  c21 : Nat
  c22 : Nat
  c23 : Nat
  c24 : Nat
  c25 : Nat
  c26 : Nat
  c27 : Nat
  c28 : Nat
  c29 : Nat
  c30 : Nat
  c31 : Nat
  c32 : Nat
  c33 : Nat
  c34 : Nat
  R : I
  A : Nat
  ok : Bool
  st : St

def mk (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 : Nat) (R : I) (A : Nat) (ok : Bool) : T :=
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, R, A, ok, statsOf c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34⟩

/-- the range of the polynomial part -/
def prng (u : T) : I := ⟨u.st.lo, u.st.hi⟩

/-- the range of the model -/
def rng (u : T) : I := (prng u).add u.R

def add (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 v.c0) Bp) (Nat.sub (Nat.add u.c1 v.c1) Bp) (Nat.sub (Nat.add u.c2 v.c2) Bp) (Nat.sub (Nat.add u.c3 v.c3) Bp) (Nat.sub (Nat.add u.c4 v.c4) Bp) (Nat.sub (Nat.add u.c5 v.c5) Bp) (Nat.sub (Nat.add u.c6 v.c6) Bp) (Nat.sub (Nat.add u.c7 v.c7) Bp) (Nat.sub (Nat.add u.c8 v.c8) Bp) (Nat.sub (Nat.add u.c9 v.c9) Bp) (Nat.sub (Nat.add u.c10 v.c10) Bp) (Nat.sub (Nat.add u.c11 v.c11) Bp) (Nat.sub (Nat.add u.c12 v.c12) Bp) (Nat.sub (Nat.add u.c13 v.c13) Bp) (Nat.sub (Nat.add u.c14 v.c14) Bp) (Nat.sub (Nat.add u.c15 v.c15) Bp) (Nat.sub (Nat.add u.c16 v.c16) Bp) (Nat.sub (Nat.add u.c17 v.c17) Bp) (Nat.sub (Nat.add u.c18 v.c18) Bp) (Nat.sub (Nat.add u.c19 v.c19) Bp) (Nat.sub (Nat.add u.c20 v.c20) Bp) (Nat.sub (Nat.add u.c21 v.c21) Bp) (Nat.sub (Nat.add u.c22 v.c22) Bp) (Nat.sub (Nat.add u.c23 v.c23) Bp) (Nat.sub (Nat.add u.c24 v.c24) Bp) (Nat.sub (Nat.add u.c25 v.c25) Bp) (Nat.sub (Nat.add u.c26 v.c26) Bp) (Nat.sub (Nat.add u.c27 v.c27) Bp) (Nat.sub (Nat.add u.c28 v.c28) Bp) (Nat.sub (Nat.add u.c29 v.c29) Bp) (Nat.sub (Nat.add u.c30 v.c30) Bp) (Nat.sub (Nat.add u.c31 v.c31) Bp) (Nat.sub (Nat.add u.c32 v.c32) Bp) (Nat.sub (Nat.add u.c33 v.c33) Bp) (Nat.sub (Nat.add u.c34 v.c34) Bp)
    (u.R.add v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def sub (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 Bp) v.c0) (Nat.sub (Nat.add u.c1 Bp) v.c1) (Nat.sub (Nat.add u.c2 Bp) v.c2) (Nat.sub (Nat.add u.c3 Bp) v.c3) (Nat.sub (Nat.add u.c4 Bp) v.c4) (Nat.sub (Nat.add u.c5 Bp) v.c5) (Nat.sub (Nat.add u.c6 Bp) v.c6) (Nat.sub (Nat.add u.c7 Bp) v.c7) (Nat.sub (Nat.add u.c8 Bp) v.c8) (Nat.sub (Nat.add u.c9 Bp) v.c9) (Nat.sub (Nat.add u.c10 Bp) v.c10) (Nat.sub (Nat.add u.c11 Bp) v.c11) (Nat.sub (Nat.add u.c12 Bp) v.c12) (Nat.sub (Nat.add u.c13 Bp) v.c13) (Nat.sub (Nat.add u.c14 Bp) v.c14) (Nat.sub (Nat.add u.c15 Bp) v.c15) (Nat.sub (Nat.add u.c16 Bp) v.c16) (Nat.sub (Nat.add u.c17 Bp) v.c17) (Nat.sub (Nat.add u.c18 Bp) v.c18) (Nat.sub (Nat.add u.c19 Bp) v.c19) (Nat.sub (Nat.add u.c20 Bp) v.c20) (Nat.sub (Nat.add u.c21 Bp) v.c21) (Nat.sub (Nat.add u.c22 Bp) v.c22) (Nat.sub (Nat.add u.c23 Bp) v.c23) (Nat.sub (Nat.add u.c24 Bp) v.c24) (Nat.sub (Nat.add u.c25 Bp) v.c25) (Nat.sub (Nat.add u.c26 Bp) v.c26) (Nat.sub (Nat.add u.c27 Bp) v.c27) (Nat.sub (Nat.add u.c28 Bp) v.c28) (Nat.sub (Nat.add u.c29 Bp) v.c29) (Nat.sub (Nat.add u.c30 Bp) v.c30) (Nat.sub (Nat.add u.c31 Bp) v.c31) (Nat.sub (Nat.add u.c32 Bp) v.c32) (Nat.sub (Nat.add u.c33 Bp) v.c33) (Nat.sub (Nat.add u.c34 Bp) v.c34)
    (u.R.sub v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def neg (u : T) : T :=
  mk (Nat.sub Bp2 u.c0) (Nat.sub Bp2 u.c1) (Nat.sub Bp2 u.c2) (Nat.sub Bp2 u.c3) (Nat.sub Bp2 u.c4) (Nat.sub Bp2 u.c5) (Nat.sub Bp2 u.c6) (Nat.sub Bp2 u.c7) (Nat.sub Bp2 u.c8) (Nat.sub Bp2 u.c9) (Nat.sub Bp2 u.c10) (Nat.sub Bp2 u.c11) (Nat.sub Bp2 u.c12) (Nat.sub Bp2 u.c13) (Nat.sub Bp2 u.c14) (Nat.sub Bp2 u.c15) (Nat.sub Bp2 u.c16) (Nat.sub Bp2 u.c17) (Nat.sub Bp2 u.c18) (Nat.sub Bp2 u.c19) (Nat.sub Bp2 u.c20) (Nat.sub Bp2 u.c21) (Nat.sub Bp2 u.c22) (Nat.sub Bp2 u.c23) (Nat.sub Bp2 u.c24) (Nat.sub Bp2 u.c25) (Nat.sub Bp2 u.c26) (Nat.sub Bp2 u.c27) (Nat.sub Bp2 u.c28) (Nat.sub Bp2 u.c29) (Nat.sub Bp2 u.c30) (Nat.sub Bp2 u.c31) (Nat.sub Bp2 u.c32) (Nat.sub Bp2 u.c33) (Nat.sub Bp2 u.c34) u.R.neg u.A (u.ok && Nat.ble u.A LIMA)

def mc0 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c0) 0)
def mc1 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c1) (Nat.add (Nat.mul u.c1 v.c0) 0))
def mc2 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c2) (Nat.add (Nat.mul u.c2 v.c0) 0))
def mc3 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c3) (Nat.add (Nat.mul u.c3 v.c0) 0))
def mc4 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c4) (Nat.add (Nat.mul u.c4 v.c0) 0))
def mc5 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c5) (Nat.add (Nat.mul u.c1 v.c1) (Nat.add (Nat.mul u.c5 v.c0) 0)))
def mc6 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c6) (Nat.add (Nat.mul u.c1 v.c2) (Nat.add (Nat.mul u.c2 v.c1) (Nat.add (Nat.mul u.c6 v.c0) 0))))
def mc7 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c7) (Nat.add (Nat.mul u.c1 v.c3) (Nat.add (Nat.mul u.c3 v.c1) (Nat.add (Nat.mul u.c7 v.c0) 0))))
def mc8 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c8) (Nat.add (Nat.mul u.c1 v.c4) (Nat.add (Nat.mul u.c4 v.c1) (Nat.add (Nat.mul u.c8 v.c0) 0))))
def mc9 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c9) (Nat.add (Nat.mul u.c2 v.c2) (Nat.add (Nat.mul u.c9 v.c0) 0)))
def mc10 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c10) (Nat.add (Nat.mul u.c2 v.c3) (Nat.add (Nat.mul u.c3 v.c2) (Nat.add (Nat.mul u.c10 v.c0) 0))))
def mc11 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c11) (Nat.add (Nat.mul u.c2 v.c4) (Nat.add (Nat.mul u.c4 v.c2) (Nat.add (Nat.mul u.c11 v.c0) 0))))
def mc12 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c12) (Nat.add (Nat.mul u.c3 v.c3) (Nat.add (Nat.mul u.c12 v.c0) 0)))
def mc13 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c13) (Nat.add (Nat.mul u.c3 v.c4) (Nat.add (Nat.mul u.c4 v.c3) (Nat.add (Nat.mul u.c13 v.c0) 0))))
def mc14 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c14) (Nat.add (Nat.mul u.c4 v.c4) (Nat.add (Nat.mul u.c14 v.c0) 0)))
def mc15 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c15) (Nat.add (Nat.mul u.c1 v.c5) (Nat.add (Nat.mul u.c5 v.c1) (Nat.add (Nat.mul u.c15 v.c0) 0))))
def mc16 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c16) (Nat.add (Nat.mul u.c1 v.c6) (Nat.add (Nat.mul u.c2 v.c5) (Nat.add (Nat.mul u.c5 v.c2) (Nat.add (Nat.mul u.c6 v.c1) (Nat.add (Nat.mul u.c16 v.c0) 0))))))
def mc17 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c17) (Nat.add (Nat.mul u.c1 v.c7) (Nat.add (Nat.mul u.c3 v.c5) (Nat.add (Nat.mul u.c5 v.c3) (Nat.add (Nat.mul u.c7 v.c1) (Nat.add (Nat.mul u.c17 v.c0) 0))))))
def mc18 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c18) (Nat.add (Nat.mul u.c1 v.c8) (Nat.add (Nat.mul u.c4 v.c5) (Nat.add (Nat.mul u.c5 v.c4) (Nat.add (Nat.mul u.c8 v.c1) (Nat.add (Nat.mul u.c18 v.c0) 0))))))
def mc19 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c19) (Nat.add (Nat.mul u.c1 v.c9) (Nat.add (Nat.mul u.c2 v.c6) (Nat.add (Nat.mul u.c6 v.c2) (Nat.add (Nat.mul u.c9 v.c1) (Nat.add (Nat.mul u.c19 v.c0) 0))))))
def mc20 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c20) (Nat.add (Nat.mul u.c1 v.c10) (Nat.add (Nat.mul u.c2 v.c7) (Nat.add (Nat.mul u.c3 v.c6) (Nat.add (Nat.mul u.c6 v.c3) (Nat.add (Nat.mul u.c7 v.c2) (Nat.add (Nat.mul u.c10 v.c1) (Nat.add (Nat.mul u.c20 v.c0) 0))))))))
def mc21 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c21) (Nat.add (Nat.mul u.c1 v.c11) (Nat.add (Nat.mul u.c2 v.c8) (Nat.add (Nat.mul u.c4 v.c6) (Nat.add (Nat.mul u.c6 v.c4) (Nat.add (Nat.mul u.c8 v.c2) (Nat.add (Nat.mul u.c11 v.c1) (Nat.add (Nat.mul u.c21 v.c0) 0))))))))
def mc22 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c22) (Nat.add (Nat.mul u.c1 v.c12) (Nat.add (Nat.mul u.c3 v.c7) (Nat.add (Nat.mul u.c7 v.c3) (Nat.add (Nat.mul u.c12 v.c1) (Nat.add (Nat.mul u.c22 v.c0) 0))))))
def mc23 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c23) (Nat.add (Nat.mul u.c1 v.c13) (Nat.add (Nat.mul u.c3 v.c8) (Nat.add (Nat.mul u.c4 v.c7) (Nat.add (Nat.mul u.c7 v.c4) (Nat.add (Nat.mul u.c8 v.c3) (Nat.add (Nat.mul u.c13 v.c1) (Nat.add (Nat.mul u.c23 v.c0) 0))))))))
def mc24 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c24) (Nat.add (Nat.mul u.c1 v.c14) (Nat.add (Nat.mul u.c4 v.c8) (Nat.add (Nat.mul u.c8 v.c4) (Nat.add (Nat.mul u.c14 v.c1) (Nat.add (Nat.mul u.c24 v.c0) 0))))))
def mc25 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c25) (Nat.add (Nat.mul u.c2 v.c9) (Nat.add (Nat.mul u.c9 v.c2) (Nat.add (Nat.mul u.c25 v.c0) 0))))
def mc26 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c26) (Nat.add (Nat.mul u.c2 v.c10) (Nat.add (Nat.mul u.c3 v.c9) (Nat.add (Nat.mul u.c9 v.c3) (Nat.add (Nat.mul u.c10 v.c2) (Nat.add (Nat.mul u.c26 v.c0) 0))))))
def mc27 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c27) (Nat.add (Nat.mul u.c2 v.c11) (Nat.add (Nat.mul u.c4 v.c9) (Nat.add (Nat.mul u.c9 v.c4) (Nat.add (Nat.mul u.c11 v.c2) (Nat.add (Nat.mul u.c27 v.c0) 0))))))
def mc28 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c28) (Nat.add (Nat.mul u.c2 v.c12) (Nat.add (Nat.mul u.c3 v.c10) (Nat.add (Nat.mul u.c10 v.c3) (Nat.add (Nat.mul u.c12 v.c2) (Nat.add (Nat.mul u.c28 v.c0) 0))))))
def mc29 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c29) (Nat.add (Nat.mul u.c2 v.c13) (Nat.add (Nat.mul u.c3 v.c11) (Nat.add (Nat.mul u.c4 v.c10) (Nat.add (Nat.mul u.c10 v.c4) (Nat.add (Nat.mul u.c11 v.c3) (Nat.add (Nat.mul u.c13 v.c2) (Nat.add (Nat.mul u.c29 v.c0) 0))))))))
def mc30 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c30) (Nat.add (Nat.mul u.c2 v.c14) (Nat.add (Nat.mul u.c4 v.c11) (Nat.add (Nat.mul u.c11 v.c4) (Nat.add (Nat.mul u.c14 v.c2) (Nat.add (Nat.mul u.c30 v.c0) 0))))))
def mc31 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c31) (Nat.add (Nat.mul u.c3 v.c12) (Nat.add (Nat.mul u.c12 v.c3) (Nat.add (Nat.mul u.c31 v.c0) 0))))
def mc32 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c32) (Nat.add (Nat.mul u.c3 v.c13) (Nat.add (Nat.mul u.c4 v.c12) (Nat.add (Nat.mul u.c12 v.c4) (Nat.add (Nat.mul u.c13 v.c3) (Nat.add (Nat.mul u.c32 v.c0) 0))))))
def mc33 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c33) (Nat.add (Nat.mul u.c3 v.c14) (Nat.add (Nat.mul u.c4 v.c13) (Nat.add (Nat.mul u.c13 v.c4) (Nat.add (Nat.mul u.c14 v.c3) (Nat.add (Nat.mul u.c33 v.c0) 0))))))
def mc34 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c34) (Nat.add (Nat.mul u.c4 v.c14) (Nat.add (Nat.mul u.c14 v.c4) (Nat.add (Nat.mul u.c34 v.c0) 0))))

/-- the product -/
def mul (u v : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 v.st.n3) (Nat.mul u.st.n2 v.st.n2)) (Nat.mul u.st.n2 v.st.n3)) (Nat.mul u.st.n3 v.st.n1)) (Nat.mul u.st.n3 v.st.n2)) (Nat.mul u.st.n3 v.st.n3))) NR)
  mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v) (mc24 u v) (mc25 u v) (mc26 u v) (mc27 u v) (mc28 u v) (mc29 u v) (mc30 u v) (mc31 u v) (mc32 u v) (mc33 u v) (mc34 u v)
    ((((prng u).mul v.R).add (u.R.mul (rng v))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as v.st.as) NP)) NR)
    (u.ok && v.ok && Nat.ble u.st.as LIM && Nat.ble v.st.as LIM)

def sc0 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (0) 1) (Nat.add (Nat.mul u.c0 u.c0) 0))
def sc1 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c1) 0) 1) (0))
def sc2 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c2) 0) 1) (0))
def sc3 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c3) 0) 1) (0))
def sc4 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c4) 0) 1) (0))
def sc5 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c5) 0) 1) (Nat.add (Nat.mul u.c1 u.c1) 0))
def sc6 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c6) (Nat.add (Nat.mul u.c1 u.c2) 0)) 1) (0))
def sc7 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c7) (Nat.add (Nat.mul u.c1 u.c3) 0)) 1) (0))
def sc8 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c8) (Nat.add (Nat.mul u.c1 u.c4) 0)) 1) (0))
def sc9 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c9) 0) 1) (Nat.add (Nat.mul u.c2 u.c2) 0))
def sc10 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c10) (Nat.add (Nat.mul u.c2 u.c3) 0)) 1) (0))
def sc11 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c11) (Nat.add (Nat.mul u.c2 u.c4) 0)) 1) (0))
def sc12 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c12) 0) 1) (Nat.add (Nat.mul u.c3 u.c3) 0))
def sc13 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c13) (Nat.add (Nat.mul u.c3 u.c4) 0)) 1) (0))
def sc14 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c14) 0) 1) (Nat.add (Nat.mul u.c4 u.c4) 0))
def sc15 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c15) (Nat.add (Nat.mul u.c1 u.c5) 0)) 1) (0))
def sc16 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c16) (Nat.add (Nat.mul u.c1 u.c6) (Nat.add (Nat.mul u.c2 u.c5) 0))) 1) (0))
def sc17 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c17) (Nat.add (Nat.mul u.c1 u.c7) (Nat.add (Nat.mul u.c3 u.c5) 0))) 1) (0))
def sc18 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c18) (Nat.add (Nat.mul u.c1 u.c8) (Nat.add (Nat.mul u.c4 u.c5) 0))) 1) (0))
def sc19 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c19) (Nat.add (Nat.mul u.c1 u.c9) (Nat.add (Nat.mul u.c2 u.c6) 0))) 1) (0))
def sc20 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c20) (Nat.add (Nat.mul u.c1 u.c10) (Nat.add (Nat.mul u.c2 u.c7) (Nat.add (Nat.mul u.c3 u.c6) 0)))) 1) (0))
def sc21 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c21) (Nat.add (Nat.mul u.c1 u.c11) (Nat.add (Nat.mul u.c2 u.c8) (Nat.add (Nat.mul u.c4 u.c6) 0)))) 1) (0))
def sc22 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c22) (Nat.add (Nat.mul u.c1 u.c12) (Nat.add (Nat.mul u.c3 u.c7) 0))) 1) (0))
def sc23 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c23) (Nat.add (Nat.mul u.c1 u.c13) (Nat.add (Nat.mul u.c3 u.c8) (Nat.add (Nat.mul u.c4 u.c7) 0)))) 1) (0))
def sc24 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c24) (Nat.add (Nat.mul u.c1 u.c14) (Nat.add (Nat.mul u.c4 u.c8) 0))) 1) (0))
def sc25 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c25) (Nat.add (Nat.mul u.c2 u.c9) 0)) 1) (0))
def sc26 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c26) (Nat.add (Nat.mul u.c2 u.c10) (Nat.add (Nat.mul u.c3 u.c9) 0))) 1) (0))
def sc27 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c27) (Nat.add (Nat.mul u.c2 u.c11) (Nat.add (Nat.mul u.c4 u.c9) 0))) 1) (0))
def sc28 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c28) (Nat.add (Nat.mul u.c2 u.c12) (Nat.add (Nat.mul u.c3 u.c10) 0))) 1) (0))
def sc29 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c29) (Nat.add (Nat.mul u.c2 u.c13) (Nat.add (Nat.mul u.c3 u.c11) (Nat.add (Nat.mul u.c4 u.c10) 0)))) 1) (0))
def sc30 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c30) (Nat.add (Nat.mul u.c2 u.c14) (Nat.add (Nat.mul u.c4 u.c11) 0))) 1) (0))
def sc31 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c31) (Nat.add (Nat.mul u.c3 u.c12) 0)) 1) (0))
def sc32 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c32) (Nat.add (Nat.mul u.c3 u.c13) (Nat.add (Nat.mul u.c4 u.c12) 0))) 1) (0))
def sc33 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c33) (Nat.add (Nat.mul u.c3 u.c14) (Nat.add (Nat.mul u.c4 u.c13) 0))) 1) (0))
def sc34 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c34) (Nat.add (Nat.mul u.c4 u.c14) 0)) 1) (0))

/-- the square (each symmetric product once) -/
def sq (u : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 u.st.n3) (Nat.mul u.st.n2 u.st.n2)) (Nat.mul u.st.n2 u.st.n3)) (Nat.mul u.st.n3 u.st.n1)) (Nat.mul u.st.n3 u.st.n2)) (Nat.mul u.st.n3 u.st.n3))) NR)
  mk (sc0 u) (sc1 u) (sc2 u) (sc3 u) (sc4 u) (sc5 u) (sc6 u) (sc7 u) (sc8 u) (sc9 u) (sc10 u) (sc11 u) (sc12 u) (sc13 u) (sc14 u) (sc15 u) (sc16 u) (sc17 u) (sc18 u) (sc19 u) (sc20 u) (sc21 u) (sc22 u) (sc23 u) (sc24 u) (sc25 u) (sc26 u) (sc27 u) (sc28 u) (sc29 u) (sc30 u) (sc31 u) (sc32 u) (sc33 u) (sc34 u)
    ((((prng u).mul u.R).add (u.R.mul (rng u))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as u.st.as) NP)) NR)
    (u.ok && Nat.ble u.st.as LIM)

/-- the truncated product of the polynomial parts (series only) -/
def pmul (u v : T) : T := mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v) (mc24 u v) (mc25 u v) (mc26 u v) (mc27 u v) (mc28 u v) (mc29 u v) (mc30 u v) (mc31 u v) (mc32 u v) (mc33 u v) (mc34 u v) I.zero 0 true

/-- the constant `n` -/
def cst (n : Int) : T :=
  match n with
  | .ofNat j => mk (Nat.add Bp (Nat.mul j ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul j ONE) true
  | .negSucc j => mk (Nat.sub Bp (Nat.mul (Nat.succ j) ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul (Nat.succ j) ONE)
      (Nat.ble (Nat.mul (Nat.succ j) ONE) Bp)

/-- the point `(x - Bb) / 2^96` (`x` with the bias of `I`) -/
def ptB (x : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t0` -/
def var0 (x r : Nat) : T := mk (Nat.add x DB) (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t1` -/
def var1 (x r : Nat) : T := mk (Nat.add x DB) Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t2` -/
def var2 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t3` -/
def var3 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- `u` without its constant term, times the point `s` (series only) -/
def tail (s : Nat) (u : T) : T := mk Bp (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) (pmul1 s u.c24) (pmul1 s u.c25) (pmul1 s u.c26) (pmul1 s u.c27) (pmul1 s u.c28) (pmul1 s u.c29) (pmul1 s u.c30) (pmul1 s u.c31) (pmul1 s u.c32) (pmul1 s u.c33) (pmul1 s u.c34) I.zero 0 true

/-- `c + u` for a point `c` (series only) -/
def addc (c : Nat) (u : T) : T := mk (Nat.sub (Nat.add c u.c0) Bp) u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 u.c24 u.c25 u.c26 u.c27 u.c28 u.c29 u.c30 u.c31 u.c32 u.c33 u.c34 I.zero 0 true

/-- `c + s u` for points `c`, `s` (series only) -/
def axpy (c s : Nat) (u : T) : T :=
  mk (Nat.sub (Nat.add c (pmul1 s u.c0)) Bp) (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) (pmul1 s u.c24) (pmul1 s u.c25) (pmul1 s u.c26) (pmul1 s u.c27) (pmul1 s u.c28) (pmul1 s u.c29) (pmul1 s u.c30) (pmul1 s u.c31) (pmul1 s u.c32) (pmul1 s u.c33) (pmul1 s u.c34) I.zero 0 true

/-- the polynomial of `u` with the remainder `R`, the exact `A` and the flag `ok` -/
def withR (u : T) (R : I) (ok : Bool) : T := mk u.c0 u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 u.c24 u.c25 u.c26 u.c27 u.c28 u.c29 u.c30 u.c31 u.c32 u.c33 u.c34 R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs u.c0) (pabs u.c1)) (pabs u.c2)) (pabs u.c3)) (pabs u.c4)) (pabs u.c5)) (pabs u.c6)) (pabs u.c7)) (pabs u.c8)) (pabs u.c9)) (pabs u.c10)) (pabs u.c11)) (pabs u.c12)) (pabs u.c13)) (pabs u.c14)) (pabs u.c15)) (pabs u.c16)) (pabs u.c17)) (pabs u.c18)) (pabs u.c19)) (pabs u.c20)) (pabs u.c21)) (pabs u.c22)) (pabs u.c23)) (pabs u.c24)) (pabs u.c25)) (pabs u.c26)) (pabs u.c27)) (pabs u.c28)) (pabs u.c29)) (pabs u.c30)) (pabs u.c31)) (pabs u.c32)) (pabs u.c33)) (pabs u.c34)) ok

/-- the truncated series of `1/v` (any polynomial is sound) -/
def invSeries (v : T) : T :=
  let y0 := rcp v.c0
  let t := tail (Nat.sub Bp2 y0) v
  let P3 := addc (Nat.add Bp ONE) t
  let P2 := addc (Nat.add Bp ONE) (pmul t P3)
  let P1 := addc (Nat.add Bp ONE) (pmul t P2)
  axpy Bp y0 P1

/-- the truncated series of `√v` (any polynomial is sound) -/
def sqrtSeries (v : T) : T :=
  let s0 := rsq v.c0
  let t := tail (rcp v.c0) v
  let Q3 := addc (frac 1 16) (cst 0)
  let Q2 := addc (fracN 1 8) (pmul t Q3)
  let Q1 := addc (frac 1 2) (pmul t Q2)
  axpy s0 s0 (pmul t Q1)

/-- `Y` with the remainder `rng(E) · iv`, given `iv` (if defined) -/
def resid (Y E : T) (ok : Bool) : Option I → Option T
  | some iv => some (withR Y ((rng E).mul iv) (ok && E.ok))
  | none => none

def inv (v : T) : Option T :=
  let Y := withR (invSeries v) I.zero true
  resid Y (sub (cst 1) (mul v Y)) v.ok (rng v).inv

def sqrt (v : T) : Option T :=
  let Y := withR (sqrtSeries v) I.zero true
  resid Y (sub v (mul Y Y)) v.ok (sqrtDen (rng Y) (rng v).sqrt)

def div (u v : T) : Option T := Option.map (mul u) (inv v)

/-- Taylor-model arithmetic -/
instance tfOps : Ops (Option T) where
  add x y := match x, y with | some a, some b => some (add a b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (sub a b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (mul a b) | _, _ => none
  div x y := match x, y with | some a, some b => div a b | _, _ => none
  neg x := match x with | some a => some (neg a) | none => none
  sqrt x := match x with | some a => sqrt a | none => none
  sq x := match x with | some a => some (sq a) | none => none
  ofInt n := some (cst n)

/-- the model is valid and its range is positive -/
def posT : Option T → Bool
  | some u => u.ok && posLo (rng u)
  | none => false

/-- every zero of the enclosed function in the box has `|t₃| ≤ ρ/2^96`: writing the polynomial as
`p₀(t) + t₃ q(t)`, `|t₃| |q| ≤ |p₀| + |R|` at a zero, and `|q| ≥ qmin` -/
def newtOK (rho : Nat) : Option T → Bool
  | some p =>
    let qmin := Nat.sub (pabs p.c4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c8) (pabs p.c11)) (pabs p.c13)) (pabs p.c14)) (pabs p.c18)) (pabs p.c21)) (pabs p.c23)) (pabs p.c24)) (pabs p.c27)) (pabs p.c29)) (pabs p.c30)) (pabs p.c32)) (pabs p.c33)) (pabs p.c34))
    p.ok && Nat.ble 1 qmin &&
      Nat.ble (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c0) (pabs p.c1)) (pabs p.c2)) (pabs p.c3)) (pabs p.c5)) (pabs p.c6)) (pabs p.c7)) (pabs p.c9)) (pabs p.c10)) (pabs p.c12)) (pabs p.c15)) (pabs p.c16)) (pabs p.c17)) (pabs p.c19)) (pabs p.c20)) (pabs p.c22)) (pabs p.c25)) (pabs p.c26)) (pabs p.c28)) (pabs p.c31)) (rmag p.R)) ONE) (Nat.mul rho qmin)
  | none => false

end TF.F4

namespace TF.W5

/-! ## `W5`: graded degree `< 5` for grades `[1, 1, 1, 2]`, 46 monomials, 269 coefficient products per product

`c0` 1, `c1` t0, `c2` t1, `c3` t2, `c4` t0^2, `c5` t0·t1, `c6` t0·t2, `c7` t1^2, `c8` t1·t2, `c9` t2^2, `c10` t3, `c11` t0^3, `c12` t0^2·t1, `c13` t0^2·t2, `c14` t0·t1^2, `c15` t0·t1·t2, `c16` t0·t2^2, `c17` t0·t3, `c18` t1^3, `c19` t1^2·t2, `c20` t1·t2^2, `c21` t1·t3, `c22` t2^3, `c23` t2·t3, `c24` t0^4, `c25` t0^3·t1, `c26` t0^3·t2, `c27` t0^2·t1^2, `c28` t0^2·t1·t2, `c29` t0^2·t2^2, `c30` t0^2·t3, `c31` t0·t1^3, `c32` t0·t1^2·t2, `c33` t0·t1·t2^2, `c34` t0·t1·t3, `c35` t0·t2^3, `c36` t0·t2·t3, `c37` t1^4, `c38` t1^3·t2, `c39` t1^2·t2^2, `c40` t1^2·t3, `c41` t1·t2^3, `c42` t1·t2·t3, `c43` t2^4, `c44` t2^2·t3, `c45` t3^2. -/

/-- the rounding allowance of a product, in offset units -/
def NR : Nat := 46
/-- the number of coefficient products of a product -/
def NP : Nat := 269

/-- grade norms `n_d = Σ_{deg k = d} |c_k - Bp|`, the range `⟨lo, hi⟩` of the polynomial on the box, and
`as = Σ_k |c_k - Bp|` -/
structure St where
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n4 : Nat
  lo : Nat
  hi : Nat
  as : Nat

def statsOf (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 : Nat) : St :=
  ⟨(Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.sub c7 Bp)) (Nat.sub Bp c7)) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11)) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24)) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.sub c27 Bp)) (Nat.sub Bp c27)) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.sub c29 Bp)) (Nat.sub Bp c29)) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))) (Nat.add (Nat.sub c35 Bp) (Nat.sub Bp c35))) (Nat.add (Nat.sub c36 Bp) (Nat.sub Bp c36))) (Nat.sub c37 Bp)) (Nat.sub Bp c37)) (Nat.add (Nat.sub c38 Bp) (Nat.sub Bp c38))) (Nat.sub c39 Bp)) (Nat.sub Bp c39)) (Nat.add (Nat.sub c40 Bp) (Nat.sub Bp c40))) (Nat.add (Nat.sub c41 Bp) (Nat.sub Bp c41))) (Nat.add (Nat.sub c42 Bp) (Nat.sub Bp c42))) (Nat.sub c43 Bp)) (Nat.sub Bp c43)) (Nat.add (Nat.sub c44 Bp) (Nat.sub Bp c44))) (Nat.sub c45 Bp)) (Nat.sub Bp c45)), Nat.sub (Nat.add (Nat.add BpB (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))) (Nat.add (Nat.sub c35 Bp) (Nat.sub Bp c35))) (Nat.add (Nat.sub c36 Bp) (Nat.sub Bp c36))) (Nat.add (Nat.sub c38 Bp) (Nat.sub Bp c38))) (Nat.add (Nat.sub c40 Bp) (Nat.sub Bp c40))) (Nat.add (Nat.sub c41 Bp) (Nat.sub Bp c41))) (Nat.add (Nat.sub c42 Bp) (Nat.sub Bp c42))) (Nat.add (Nat.sub c44 Bp) (Nat.sub Bp c44)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub Bp c4) (Nat.sub Bp c7)) (Nat.sub Bp c9)) (Nat.sub Bp c24)) (Nat.sub Bp c27)) (Nat.sub Bp c29)) (Nat.sub Bp c37)) (Nat.sub Bp c39)) (Nat.sub Bp c43)) (Nat.sub Bp c45))) c0, Nat.sub (Nat.add (Nat.add c0 Bb) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23))) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))) (Nat.add (Nat.sub c35 Bp) (Nat.sub Bp c35))) (Nat.add (Nat.sub c36 Bp) (Nat.sub Bp c36))) (Nat.add (Nat.sub c38 Bp) (Nat.sub Bp c38))) (Nat.add (Nat.sub c40 Bp) (Nat.sub Bp c40))) (Nat.add (Nat.sub c41 Bp) (Nat.sub Bp c41))) (Nat.add (Nat.sub c42 Bp) (Nat.sub Bp c42))) (Nat.add (Nat.sub c44 Bp) (Nat.sub Bp c44))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub c7 Bp)) (Nat.sub c9 Bp)) (Nat.sub c24 Bp)) (Nat.sub c27 Bp)) (Nat.sub c29 Bp)) (Nat.sub c37 Bp)) (Nat.sub c39 Bp)) (Nat.sub c43 Bp)) (Nat.sub c45 Bp)))) Bp, Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c0 Bp) (Nat.sub Bp c0)) (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)) (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.sub c7 Bp)) (Nat.sub Bp c7)) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11)) (Nat.add (Nat.sub c12 Bp) (Nat.sub Bp c12))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.sub c14 Bp) (Nat.sub Bp c14))) (Nat.add (Nat.sub c15 Bp) (Nat.sub Bp c15))) (Nat.add (Nat.sub c16 Bp) (Nat.sub Bp c16))) (Nat.add (Nat.sub c17 Bp) (Nat.sub Bp c17))) (Nat.add (Nat.sub c18 Bp) (Nat.sub Bp c18))) (Nat.add (Nat.sub c19 Bp) (Nat.sub Bp c19))) (Nat.add (Nat.sub c20 Bp) (Nat.sub Bp c20))) (Nat.add (Nat.sub c21 Bp) (Nat.sub Bp c21))) (Nat.add (Nat.sub c22 Bp) (Nat.sub Bp c22))) (Nat.add (Nat.sub c23 Bp) (Nat.sub Bp c23)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c24 Bp) (Nat.sub Bp c24)) (Nat.add (Nat.sub c25 Bp) (Nat.sub Bp c25))) (Nat.add (Nat.sub c26 Bp) (Nat.sub Bp c26))) (Nat.sub c27 Bp)) (Nat.sub Bp c27)) (Nat.add (Nat.sub c28 Bp) (Nat.sub Bp c28))) (Nat.sub c29 Bp)) (Nat.sub Bp c29)) (Nat.add (Nat.sub c30 Bp) (Nat.sub Bp c30))) (Nat.add (Nat.sub c31 Bp) (Nat.sub Bp c31))) (Nat.add (Nat.sub c32 Bp) (Nat.sub Bp c32))) (Nat.add (Nat.sub c33 Bp) (Nat.sub Bp c33))) (Nat.add (Nat.sub c34 Bp) (Nat.sub Bp c34))) (Nat.add (Nat.sub c35 Bp) (Nat.sub Bp c35))) (Nat.add (Nat.sub c36 Bp) (Nat.sub Bp c36))) (Nat.sub c37 Bp)) (Nat.sub Bp c37)) (Nat.add (Nat.sub c38 Bp) (Nat.sub Bp c38))) (Nat.sub c39 Bp)) (Nat.sub Bp c39)) (Nat.add (Nat.sub c40 Bp) (Nat.sub Bp c40))) (Nat.add (Nat.sub c41 Bp) (Nat.sub Bp c41))) (Nat.add (Nat.sub c42 Bp) (Nat.sub Bp c42))) (Nat.sub c43 Bp)) (Nat.sub Bp c43)) (Nat.add (Nat.sub c44 Bp) (Nat.sub Bp c44))) (Nat.sub c45 Bp)) (Nat.sub Bp c45))⟩

structure T where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
  c8 : Nat
  c9 : Nat
  c10 : Nat
  c11 : Nat
  c12 : Nat
  c13 : Nat
  c14 : Nat
  c15 : Nat
  c16 : Nat
  c17 : Nat
  c18 : Nat
  c19 : Nat
  c20 : Nat
  c21 : Nat
  c22 : Nat
  c23 : Nat
  c24 : Nat
  c25 : Nat
  c26 : Nat
  c27 : Nat
  c28 : Nat
  c29 : Nat
  c30 : Nat
  c31 : Nat
  c32 : Nat
  c33 : Nat
  c34 : Nat
  c35 : Nat
  c36 : Nat
  c37 : Nat
  c38 : Nat
  c39 : Nat
  c40 : Nat
  c41 : Nat
  c42 : Nat
  c43 : Nat
  c44 : Nat
  c45 : Nat
  R : I
  A : Nat
  ok : Bool
  st : St

def mk (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 : Nat) (R : I) (A : Nat) (ok : Bool) : T :=
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, R, A, ok, statsOf c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45⟩

/-- the range of the polynomial part -/
def prng (u : T) : I := ⟨u.st.lo, u.st.hi⟩

/-- the range of the model -/
def rng (u : T) : I := (prng u).add u.R

def add (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 v.c0) Bp) (Nat.sub (Nat.add u.c1 v.c1) Bp) (Nat.sub (Nat.add u.c2 v.c2) Bp) (Nat.sub (Nat.add u.c3 v.c3) Bp) (Nat.sub (Nat.add u.c4 v.c4) Bp) (Nat.sub (Nat.add u.c5 v.c5) Bp) (Nat.sub (Nat.add u.c6 v.c6) Bp) (Nat.sub (Nat.add u.c7 v.c7) Bp) (Nat.sub (Nat.add u.c8 v.c8) Bp) (Nat.sub (Nat.add u.c9 v.c9) Bp) (Nat.sub (Nat.add u.c10 v.c10) Bp) (Nat.sub (Nat.add u.c11 v.c11) Bp) (Nat.sub (Nat.add u.c12 v.c12) Bp) (Nat.sub (Nat.add u.c13 v.c13) Bp) (Nat.sub (Nat.add u.c14 v.c14) Bp) (Nat.sub (Nat.add u.c15 v.c15) Bp) (Nat.sub (Nat.add u.c16 v.c16) Bp) (Nat.sub (Nat.add u.c17 v.c17) Bp) (Nat.sub (Nat.add u.c18 v.c18) Bp) (Nat.sub (Nat.add u.c19 v.c19) Bp) (Nat.sub (Nat.add u.c20 v.c20) Bp) (Nat.sub (Nat.add u.c21 v.c21) Bp) (Nat.sub (Nat.add u.c22 v.c22) Bp) (Nat.sub (Nat.add u.c23 v.c23) Bp) (Nat.sub (Nat.add u.c24 v.c24) Bp) (Nat.sub (Nat.add u.c25 v.c25) Bp) (Nat.sub (Nat.add u.c26 v.c26) Bp) (Nat.sub (Nat.add u.c27 v.c27) Bp) (Nat.sub (Nat.add u.c28 v.c28) Bp) (Nat.sub (Nat.add u.c29 v.c29) Bp) (Nat.sub (Nat.add u.c30 v.c30) Bp) (Nat.sub (Nat.add u.c31 v.c31) Bp) (Nat.sub (Nat.add u.c32 v.c32) Bp) (Nat.sub (Nat.add u.c33 v.c33) Bp) (Nat.sub (Nat.add u.c34 v.c34) Bp) (Nat.sub (Nat.add u.c35 v.c35) Bp) (Nat.sub (Nat.add u.c36 v.c36) Bp) (Nat.sub (Nat.add u.c37 v.c37) Bp) (Nat.sub (Nat.add u.c38 v.c38) Bp) (Nat.sub (Nat.add u.c39 v.c39) Bp) (Nat.sub (Nat.add u.c40 v.c40) Bp) (Nat.sub (Nat.add u.c41 v.c41) Bp) (Nat.sub (Nat.add u.c42 v.c42) Bp) (Nat.sub (Nat.add u.c43 v.c43) Bp) (Nat.sub (Nat.add u.c44 v.c44) Bp) (Nat.sub (Nat.add u.c45 v.c45) Bp)
    (u.R.add v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def sub (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 Bp) v.c0) (Nat.sub (Nat.add u.c1 Bp) v.c1) (Nat.sub (Nat.add u.c2 Bp) v.c2) (Nat.sub (Nat.add u.c3 Bp) v.c3) (Nat.sub (Nat.add u.c4 Bp) v.c4) (Nat.sub (Nat.add u.c5 Bp) v.c5) (Nat.sub (Nat.add u.c6 Bp) v.c6) (Nat.sub (Nat.add u.c7 Bp) v.c7) (Nat.sub (Nat.add u.c8 Bp) v.c8) (Nat.sub (Nat.add u.c9 Bp) v.c9) (Nat.sub (Nat.add u.c10 Bp) v.c10) (Nat.sub (Nat.add u.c11 Bp) v.c11) (Nat.sub (Nat.add u.c12 Bp) v.c12) (Nat.sub (Nat.add u.c13 Bp) v.c13) (Nat.sub (Nat.add u.c14 Bp) v.c14) (Nat.sub (Nat.add u.c15 Bp) v.c15) (Nat.sub (Nat.add u.c16 Bp) v.c16) (Nat.sub (Nat.add u.c17 Bp) v.c17) (Nat.sub (Nat.add u.c18 Bp) v.c18) (Nat.sub (Nat.add u.c19 Bp) v.c19) (Nat.sub (Nat.add u.c20 Bp) v.c20) (Nat.sub (Nat.add u.c21 Bp) v.c21) (Nat.sub (Nat.add u.c22 Bp) v.c22) (Nat.sub (Nat.add u.c23 Bp) v.c23) (Nat.sub (Nat.add u.c24 Bp) v.c24) (Nat.sub (Nat.add u.c25 Bp) v.c25) (Nat.sub (Nat.add u.c26 Bp) v.c26) (Nat.sub (Nat.add u.c27 Bp) v.c27) (Nat.sub (Nat.add u.c28 Bp) v.c28) (Nat.sub (Nat.add u.c29 Bp) v.c29) (Nat.sub (Nat.add u.c30 Bp) v.c30) (Nat.sub (Nat.add u.c31 Bp) v.c31) (Nat.sub (Nat.add u.c32 Bp) v.c32) (Nat.sub (Nat.add u.c33 Bp) v.c33) (Nat.sub (Nat.add u.c34 Bp) v.c34) (Nat.sub (Nat.add u.c35 Bp) v.c35) (Nat.sub (Nat.add u.c36 Bp) v.c36) (Nat.sub (Nat.add u.c37 Bp) v.c37) (Nat.sub (Nat.add u.c38 Bp) v.c38) (Nat.sub (Nat.add u.c39 Bp) v.c39) (Nat.sub (Nat.add u.c40 Bp) v.c40) (Nat.sub (Nat.add u.c41 Bp) v.c41) (Nat.sub (Nat.add u.c42 Bp) v.c42) (Nat.sub (Nat.add u.c43 Bp) v.c43) (Nat.sub (Nat.add u.c44 Bp) v.c44) (Nat.sub (Nat.add u.c45 Bp) v.c45)
    (u.R.sub v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def neg (u : T) : T :=
  mk (Nat.sub Bp2 u.c0) (Nat.sub Bp2 u.c1) (Nat.sub Bp2 u.c2) (Nat.sub Bp2 u.c3) (Nat.sub Bp2 u.c4) (Nat.sub Bp2 u.c5) (Nat.sub Bp2 u.c6) (Nat.sub Bp2 u.c7) (Nat.sub Bp2 u.c8) (Nat.sub Bp2 u.c9) (Nat.sub Bp2 u.c10) (Nat.sub Bp2 u.c11) (Nat.sub Bp2 u.c12) (Nat.sub Bp2 u.c13) (Nat.sub Bp2 u.c14) (Nat.sub Bp2 u.c15) (Nat.sub Bp2 u.c16) (Nat.sub Bp2 u.c17) (Nat.sub Bp2 u.c18) (Nat.sub Bp2 u.c19) (Nat.sub Bp2 u.c20) (Nat.sub Bp2 u.c21) (Nat.sub Bp2 u.c22) (Nat.sub Bp2 u.c23) (Nat.sub Bp2 u.c24) (Nat.sub Bp2 u.c25) (Nat.sub Bp2 u.c26) (Nat.sub Bp2 u.c27) (Nat.sub Bp2 u.c28) (Nat.sub Bp2 u.c29) (Nat.sub Bp2 u.c30) (Nat.sub Bp2 u.c31) (Nat.sub Bp2 u.c32) (Nat.sub Bp2 u.c33) (Nat.sub Bp2 u.c34) (Nat.sub Bp2 u.c35) (Nat.sub Bp2 u.c36) (Nat.sub Bp2 u.c37) (Nat.sub Bp2 u.c38) (Nat.sub Bp2 u.c39) (Nat.sub Bp2 u.c40) (Nat.sub Bp2 u.c41) (Nat.sub Bp2 u.c42) (Nat.sub Bp2 u.c43) (Nat.sub Bp2 u.c44) (Nat.sub Bp2 u.c45) u.R.neg u.A (u.ok && Nat.ble u.A LIMA)

def mc0 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c0) 0)
def mc1 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c1) (Nat.add (Nat.mul u.c1 v.c0) 0))
def mc2 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c2) (Nat.add (Nat.mul u.c2 v.c0) 0))
def mc3 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c3) (Nat.add (Nat.mul u.c3 v.c0) 0))
def mc4 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c4) (Nat.add (Nat.mul u.c1 v.c1) (Nat.add (Nat.mul u.c4 v.c0) 0)))
def mc5 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c5) (Nat.add (Nat.mul u.c1 v.c2) (Nat.add (Nat.mul u.c2 v.c1) (Nat.add (Nat.mul u.c5 v.c0) 0))))
def mc6 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c6) (Nat.add (Nat.mul u.c1 v.c3) (Nat.add (Nat.mul u.c3 v.c1) (Nat.add (Nat.mul u.c6 v.c0) 0))))
def mc7 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c7) (Nat.add (Nat.mul u.c2 v.c2) (Nat.add (Nat.mul u.c7 v.c0) 0)))
def mc8 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c8) (Nat.add (Nat.mul u.c2 v.c3) (Nat.add (Nat.mul u.c3 v.c2) (Nat.add (Nat.mul u.c8 v.c0) 0))))
def mc9 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c9) (Nat.add (Nat.mul u.c3 v.c3) (Nat.add (Nat.mul u.c9 v.c0) 0)))
def mc10 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c10) (Nat.add (Nat.mul u.c10 v.c0) 0))
def mc11 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c11) (Nat.add (Nat.mul u.c1 v.c4) (Nat.add (Nat.mul u.c4 v.c1) (Nat.add (Nat.mul u.c11 v.c0) 0))))
def mc12 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c12) (Nat.add (Nat.mul u.c1 v.c5) (Nat.add (Nat.mul u.c2 v.c4) (Nat.add (Nat.mul u.c4 v.c2) (Nat.add (Nat.mul u.c5 v.c1) (Nat.add (Nat.mul u.c12 v.c0) 0))))))
def mc13 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c13) (Nat.add (Nat.mul u.c1 v.c6) (Nat.add (Nat.mul u.c3 v.c4) (Nat.add (Nat.mul u.c4 v.c3) (Nat.add (Nat.mul u.c6 v.c1) (Nat.add (Nat.mul u.c13 v.c0) 0))))))
def mc14 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c14) (Nat.add (Nat.mul u.c1 v.c7) (Nat.add (Nat.mul u.c2 v.c5) (Nat.add (Nat.mul u.c5 v.c2) (Nat.add (Nat.mul u.c7 v.c1) (Nat.add (Nat.mul u.c14 v.c0) 0))))))
def mc15 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c15) (Nat.add (Nat.mul u.c1 v.c8) (Nat.add (Nat.mul u.c2 v.c6) (Nat.add (Nat.mul u.c3 v.c5) (Nat.add (Nat.mul u.c5 v.c3) (Nat.add (Nat.mul u.c6 v.c2) (Nat.add (Nat.mul u.c8 v.c1) (Nat.add (Nat.mul u.c15 v.c0) 0))))))))
def mc16 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c16) (Nat.add (Nat.mul u.c1 v.c9) (Nat.add (Nat.mul u.c3 v.c6) (Nat.add (Nat.mul u.c6 v.c3) (Nat.add (Nat.mul u.c9 v.c1) (Nat.add (Nat.mul u.c16 v.c0) 0))))))
def mc17 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c17) (Nat.add (Nat.mul u.c1 v.c10) (Nat.add (Nat.mul u.c10 v.c1) (Nat.add (Nat.mul u.c17 v.c0) 0))))
def mc18 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c18) (Nat.add (Nat.mul u.c2 v.c7) (Nat.add (Nat.mul u.c7 v.c2) (Nat.add (Nat.mul u.c18 v.c0) 0))))
def mc19 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c19) (Nat.add (Nat.mul u.c2 v.c8) (Nat.add (Nat.mul u.c3 v.c7) (Nat.add (Nat.mul u.c7 v.c3) (Nat.add (Nat.mul u.c8 v.c2) (Nat.add (Nat.mul u.c19 v.c0) 0))))))
def mc20 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c20) (Nat.add (Nat.mul u.c2 v.c9) (Nat.add (Nat.mul u.c3 v.c8) (Nat.add (Nat.mul u.c8 v.c3) (Nat.add (Nat.mul u.c9 v.c2) (Nat.add (Nat.mul u.c20 v.c0) 0))))))
def mc21 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c21) (Nat.add (Nat.mul u.c2 v.c10) (Nat.add (Nat.mul u.c10 v.c2) (Nat.add (Nat.mul u.c21 v.c0) 0))))
def mc22 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c22) (Nat.add (Nat.mul u.c3 v.c9) (Nat.add (Nat.mul u.c9 v.c3) (Nat.add (Nat.mul u.c22 v.c0) 0))))
def mc23 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c23) (Nat.add (Nat.mul u.c3 v.c10) (Nat.add (Nat.mul u.c10 v.c3) (Nat.add (Nat.mul u.c23 v.c0) 0))))
def mc24 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c24) (Nat.add (Nat.mul u.c1 v.c11) (Nat.add (Nat.mul u.c4 v.c4) (Nat.add (Nat.mul u.c11 v.c1) (Nat.add (Nat.mul u.c24 v.c0) 0)))))
def mc25 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c25) (Nat.add (Nat.mul u.c1 v.c12) (Nat.add (Nat.mul u.c2 v.c11) (Nat.add (Nat.mul u.c4 v.c5) (Nat.add (Nat.mul u.c5 v.c4) (Nat.add (Nat.mul u.c11 v.c2) (Nat.add (Nat.mul u.c12 v.c1) (Nat.add (Nat.mul u.c25 v.c0) 0))))))))
def mc26 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c26) (Nat.add (Nat.mul u.c1 v.c13) (Nat.add (Nat.mul u.c3 v.c11) (Nat.add (Nat.mul u.c4 v.c6) (Nat.add (Nat.mul u.c6 v.c4) (Nat.add (Nat.mul u.c11 v.c3) (Nat.add (Nat.mul u.c13 v.c1) (Nat.add (Nat.mul u.c26 v.c0) 0))))))))
def mc27 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c27) (Nat.add (Nat.mul u.c1 v.c14) (Nat.add (Nat.mul u.c2 v.c12) (Nat.add (Nat.mul u.c4 v.c7) (Nat.add (Nat.mul u.c5 v.c5) (Nat.add (Nat.mul u.c7 v.c4) (Nat.add (Nat.mul u.c12 v.c2) (Nat.add (Nat.mul u.c14 v.c1) (Nat.add (Nat.mul u.c27 v.c0) 0)))))))))
def mc28 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c28) (Nat.add (Nat.mul u.c1 v.c15) (Nat.add (Nat.mul u.c2 v.c13) (Nat.add (Nat.mul u.c3 v.c12) (Nat.add (Nat.mul u.c4 v.c8) (Nat.add (Nat.mul u.c5 v.c6) (Nat.add (Nat.mul u.c6 v.c5) (Nat.add (Nat.mul u.c8 v.c4) (Nat.add (Nat.mul u.c12 v.c3) (Nat.add (Nat.mul u.c13 v.c2) (Nat.add (Nat.mul u.c15 v.c1) (Nat.add (Nat.mul u.c28 v.c0) 0))))))))))))
def mc29 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c29) (Nat.add (Nat.mul u.c1 v.c16) (Nat.add (Nat.mul u.c3 v.c13) (Nat.add (Nat.mul u.c4 v.c9) (Nat.add (Nat.mul u.c6 v.c6) (Nat.add (Nat.mul u.c9 v.c4) (Nat.add (Nat.mul u.c13 v.c3) (Nat.add (Nat.mul u.c16 v.c1) (Nat.add (Nat.mul u.c29 v.c0) 0)))))))))
def mc30 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c30) (Nat.add (Nat.mul u.c1 v.c17) (Nat.add (Nat.mul u.c4 v.c10) (Nat.add (Nat.mul u.c10 v.c4) (Nat.add (Nat.mul u.c17 v.c1) (Nat.add (Nat.mul u.c30 v.c0) 0))))))
def mc31 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c31) (Nat.add (Nat.mul u.c1 v.c18) (Nat.add (Nat.mul u.c2 v.c14) (Nat.add (Nat.mul u.c5 v.c7) (Nat.add (Nat.mul u.c7 v.c5) (Nat.add (Nat.mul u.c14 v.c2) (Nat.add (Nat.mul u.c18 v.c1) (Nat.add (Nat.mul u.c31 v.c0) 0))))))))
def mc32 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c32) (Nat.add (Nat.mul u.c1 v.c19) (Nat.add (Nat.mul u.c2 v.c15) (Nat.add (Nat.mul u.c3 v.c14) (Nat.add (Nat.mul u.c5 v.c8) (Nat.add (Nat.mul u.c6 v.c7) (Nat.add (Nat.mul u.c7 v.c6) (Nat.add (Nat.mul u.c8 v.c5) (Nat.add (Nat.mul u.c14 v.c3) (Nat.add (Nat.mul u.c15 v.c2) (Nat.add (Nat.mul u.c19 v.c1) (Nat.add (Nat.mul u.c32 v.c0) 0))))))))))))
def mc33 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c33) (Nat.add (Nat.mul u.c1 v.c20) (Nat.add (Nat.mul u.c2 v.c16) (Nat.add (Nat.mul u.c3 v.c15) (Nat.add (Nat.mul u.c5 v.c9) (Nat.add (Nat.mul u.c6 v.c8) (Nat.add (Nat.mul u.c8 v.c6) (Nat.add (Nat.mul u.c9 v.c5) (Nat.add (Nat.mul u.c15 v.c3) (Nat.add (Nat.mul u.c16 v.c2) (Nat.add (Nat.mul u.c20 v.c1) (Nat.add (Nat.mul u.c33 v.c0) 0))))))))))))
def mc34 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c34) (Nat.add (Nat.mul u.c1 v.c21) (Nat.add (Nat.mul u.c2 v.c17) (Nat.add (Nat.mul u.c5 v.c10) (Nat.add (Nat.mul u.c10 v.c5) (Nat.add (Nat.mul u.c17 v.c2) (Nat.add (Nat.mul u.c21 v.c1) (Nat.add (Nat.mul u.c34 v.c0) 0))))))))
def mc35 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c35) (Nat.add (Nat.mul u.c1 v.c22) (Nat.add (Nat.mul u.c3 v.c16) (Nat.add (Nat.mul u.c6 v.c9) (Nat.add (Nat.mul u.c9 v.c6) (Nat.add (Nat.mul u.c16 v.c3) (Nat.add (Nat.mul u.c22 v.c1) (Nat.add (Nat.mul u.c35 v.c0) 0))))))))
def mc36 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c36) (Nat.add (Nat.mul u.c1 v.c23) (Nat.add (Nat.mul u.c3 v.c17) (Nat.add (Nat.mul u.c6 v.c10) (Nat.add (Nat.mul u.c10 v.c6) (Nat.add (Nat.mul u.c17 v.c3) (Nat.add (Nat.mul u.c23 v.c1) (Nat.add (Nat.mul u.c36 v.c0) 0))))))))
def mc37 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c37) (Nat.add (Nat.mul u.c2 v.c18) (Nat.add (Nat.mul u.c7 v.c7) (Nat.add (Nat.mul u.c18 v.c2) (Nat.add (Nat.mul u.c37 v.c0) 0)))))
def mc38 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c38) (Nat.add (Nat.mul u.c2 v.c19) (Nat.add (Nat.mul u.c3 v.c18) (Nat.add (Nat.mul u.c7 v.c8) (Nat.add (Nat.mul u.c8 v.c7) (Nat.add (Nat.mul u.c18 v.c3) (Nat.add (Nat.mul u.c19 v.c2) (Nat.add (Nat.mul u.c38 v.c0) 0))))))))
def mc39 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c39) (Nat.add (Nat.mul u.c2 v.c20) (Nat.add (Nat.mul u.c3 v.c19) (Nat.add (Nat.mul u.c7 v.c9) (Nat.add (Nat.mul u.c8 v.c8) (Nat.add (Nat.mul u.c9 v.c7) (Nat.add (Nat.mul u.c19 v.c3) (Nat.add (Nat.mul u.c20 v.c2) (Nat.add (Nat.mul u.c39 v.c0) 0)))))))))
def mc40 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c40) (Nat.add (Nat.mul u.c2 v.c21) (Nat.add (Nat.mul u.c7 v.c10) (Nat.add (Nat.mul u.c10 v.c7) (Nat.add (Nat.mul u.c21 v.c2) (Nat.add (Nat.mul u.c40 v.c0) 0))))))
def mc41 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c41) (Nat.add (Nat.mul u.c2 v.c22) (Nat.add (Nat.mul u.c3 v.c20) (Nat.add (Nat.mul u.c8 v.c9) (Nat.add (Nat.mul u.c9 v.c8) (Nat.add (Nat.mul u.c20 v.c3) (Nat.add (Nat.mul u.c22 v.c2) (Nat.add (Nat.mul u.c41 v.c0) 0))))))))
def mc42 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c42) (Nat.add (Nat.mul u.c2 v.c23) (Nat.add (Nat.mul u.c3 v.c21) (Nat.add (Nat.mul u.c8 v.c10) (Nat.add (Nat.mul u.c10 v.c8) (Nat.add (Nat.mul u.c21 v.c3) (Nat.add (Nat.mul u.c23 v.c2) (Nat.add (Nat.mul u.c42 v.c0) 0))))))))
def mc43 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c43) (Nat.add (Nat.mul u.c3 v.c22) (Nat.add (Nat.mul u.c9 v.c9) (Nat.add (Nat.mul u.c22 v.c3) (Nat.add (Nat.mul u.c43 v.c0) 0)))))
def mc44 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c44) (Nat.add (Nat.mul u.c3 v.c23) (Nat.add (Nat.mul u.c9 v.c10) (Nat.add (Nat.mul u.c10 v.c9) (Nat.add (Nat.mul u.c23 v.c3) (Nat.add (Nat.mul u.c44 v.c0) 0))))))
def mc45 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c45) (Nat.add (Nat.mul u.c10 v.c10) (Nat.add (Nat.mul u.c45 v.c0) 0)))

/-- the product -/
def mul (u v : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 v.st.n4) (Nat.mul u.st.n2 v.st.n3)) (Nat.mul u.st.n2 v.st.n4)) (Nat.mul u.st.n3 v.st.n2)) (Nat.mul u.st.n3 v.st.n3)) (Nat.mul u.st.n3 v.st.n4)) (Nat.mul u.st.n4 v.st.n1)) (Nat.mul u.st.n4 v.st.n2)) (Nat.mul u.st.n4 v.st.n3)) (Nat.mul u.st.n4 v.st.n4))) NR)
  mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v) (mc24 u v) (mc25 u v) (mc26 u v) (mc27 u v) (mc28 u v) (mc29 u v) (mc30 u v) (mc31 u v) (mc32 u v) (mc33 u v) (mc34 u v) (mc35 u v) (mc36 u v) (mc37 u v) (mc38 u v) (mc39 u v) (mc40 u v) (mc41 u v) (mc42 u v) (mc43 u v) (mc44 u v) (mc45 u v)
    ((((prng u).mul v.R).add (u.R.mul (rng v))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as v.st.as) NP)) NR)
    (u.ok && v.ok && Nat.ble u.st.as LIM && Nat.ble v.st.as LIM)

def sc0 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (0) 1) (Nat.add (Nat.mul u.c0 u.c0) 0))
def sc1 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c1) 0) 1) (0))
def sc2 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c2) 0) 1) (0))
def sc3 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c3) 0) 1) (0))
def sc4 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c4) 0) 1) (Nat.add (Nat.mul u.c1 u.c1) 0))
def sc5 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c5) (Nat.add (Nat.mul u.c1 u.c2) 0)) 1) (0))
def sc6 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c6) (Nat.add (Nat.mul u.c1 u.c3) 0)) 1) (0))
def sc7 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c7) 0) 1) (Nat.add (Nat.mul u.c2 u.c2) 0))
def sc8 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c8) (Nat.add (Nat.mul u.c2 u.c3) 0)) 1) (0))
def sc9 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c9) 0) 1) (Nat.add (Nat.mul u.c3 u.c3) 0))
def sc10 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c10) 0) 1) (0))
def sc11 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c11) (Nat.add (Nat.mul u.c1 u.c4) 0)) 1) (0))
def sc12 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c12) (Nat.add (Nat.mul u.c1 u.c5) (Nat.add (Nat.mul u.c2 u.c4) 0))) 1) (0))
def sc13 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c13) (Nat.add (Nat.mul u.c1 u.c6) (Nat.add (Nat.mul u.c3 u.c4) 0))) 1) (0))
def sc14 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c14) (Nat.add (Nat.mul u.c1 u.c7) (Nat.add (Nat.mul u.c2 u.c5) 0))) 1) (0))
def sc15 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c15) (Nat.add (Nat.mul u.c1 u.c8) (Nat.add (Nat.mul u.c2 u.c6) (Nat.add (Nat.mul u.c3 u.c5) 0)))) 1) (0))
def sc16 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c16) (Nat.add (Nat.mul u.c1 u.c9) (Nat.add (Nat.mul u.c3 u.c6) 0))) 1) (0))
def sc17 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c17) (Nat.add (Nat.mul u.c1 u.c10) 0)) 1) (0))
def sc18 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c18) (Nat.add (Nat.mul u.c2 u.c7) 0)) 1) (0))
def sc19 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c19) (Nat.add (Nat.mul u.c2 u.c8) (Nat.add (Nat.mul u.c3 u.c7) 0))) 1) (0))
def sc20 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c20) (Nat.add (Nat.mul u.c2 u.c9) (Nat.add (Nat.mul u.c3 u.c8) 0))) 1) (0))
def sc21 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c21) (Nat.add (Nat.mul u.c2 u.c10) 0)) 1) (0))
def sc22 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c22) (Nat.add (Nat.mul u.c3 u.c9) 0)) 1) (0))
def sc23 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c23) (Nat.add (Nat.mul u.c3 u.c10) 0)) 1) (0))
def sc24 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c24) (Nat.add (Nat.mul u.c1 u.c11) 0)) 1) (Nat.add (Nat.mul u.c4 u.c4) 0))
def sc25 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c25) (Nat.add (Nat.mul u.c1 u.c12) (Nat.add (Nat.mul u.c2 u.c11) (Nat.add (Nat.mul u.c4 u.c5) 0)))) 1) (0))
def sc26 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c26) (Nat.add (Nat.mul u.c1 u.c13) (Nat.add (Nat.mul u.c3 u.c11) (Nat.add (Nat.mul u.c4 u.c6) 0)))) 1) (0))
def sc27 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c27) (Nat.add (Nat.mul u.c1 u.c14) (Nat.add (Nat.mul u.c2 u.c12) (Nat.add (Nat.mul u.c4 u.c7) 0)))) 1) (Nat.add (Nat.mul u.c5 u.c5) 0))
def sc28 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c28) (Nat.add (Nat.mul u.c1 u.c15) (Nat.add (Nat.mul u.c2 u.c13) (Nat.add (Nat.mul u.c3 u.c12) (Nat.add (Nat.mul u.c4 u.c8) (Nat.add (Nat.mul u.c5 u.c6) 0)))))) 1) (0))
def sc29 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c29) (Nat.add (Nat.mul u.c1 u.c16) (Nat.add (Nat.mul u.c3 u.c13) (Nat.add (Nat.mul u.c4 u.c9) 0)))) 1) (Nat.add (Nat.mul u.c6 u.c6) 0))
def sc30 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c30) (Nat.add (Nat.mul u.c1 u.c17) (Nat.add (Nat.mul u.c4 u.c10) 0))) 1) (0))
def sc31 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c31) (Nat.add (Nat.mul u.c1 u.c18) (Nat.add (Nat.mul u.c2 u.c14) (Nat.add (Nat.mul u.c5 u.c7) 0)))) 1) (0))
def sc32 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c32) (Nat.add (Nat.mul u.c1 u.c19) (Nat.add (Nat.mul u.c2 u.c15) (Nat.add (Nat.mul u.c3 u.c14) (Nat.add (Nat.mul u.c5 u.c8) (Nat.add (Nat.mul u.c6 u.c7) 0)))))) 1) (0))
def sc33 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c33) (Nat.add (Nat.mul u.c1 u.c20) (Nat.add (Nat.mul u.c2 u.c16) (Nat.add (Nat.mul u.c3 u.c15) (Nat.add (Nat.mul u.c5 u.c9) (Nat.add (Nat.mul u.c6 u.c8) 0)))))) 1) (0))
def sc34 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c34) (Nat.add (Nat.mul u.c1 u.c21) (Nat.add (Nat.mul u.c2 u.c17) (Nat.add (Nat.mul u.c5 u.c10) 0)))) 1) (0))
def sc35 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c35) (Nat.add (Nat.mul u.c1 u.c22) (Nat.add (Nat.mul u.c3 u.c16) (Nat.add (Nat.mul u.c6 u.c9) 0)))) 1) (0))
def sc36 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c36) (Nat.add (Nat.mul u.c1 u.c23) (Nat.add (Nat.mul u.c3 u.c17) (Nat.add (Nat.mul u.c6 u.c10) 0)))) 1) (0))
def sc37 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c37) (Nat.add (Nat.mul u.c2 u.c18) 0)) 1) (Nat.add (Nat.mul u.c7 u.c7) 0))
def sc38 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c38) (Nat.add (Nat.mul u.c2 u.c19) (Nat.add (Nat.mul u.c3 u.c18) (Nat.add (Nat.mul u.c7 u.c8) 0)))) 1) (0))
def sc39 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c39) (Nat.add (Nat.mul u.c2 u.c20) (Nat.add (Nat.mul u.c3 u.c19) (Nat.add (Nat.mul u.c7 u.c9) 0)))) 1) (Nat.add (Nat.mul u.c8 u.c8) 0))
def sc40 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c40) (Nat.add (Nat.mul u.c2 u.c21) (Nat.add (Nat.mul u.c7 u.c10) 0))) 1) (0))
def sc41 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c41) (Nat.add (Nat.mul u.c2 u.c22) (Nat.add (Nat.mul u.c3 u.c20) (Nat.add (Nat.mul u.c8 u.c9) 0)))) 1) (0))
def sc42 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c42) (Nat.add (Nat.mul u.c2 u.c23) (Nat.add (Nat.mul u.c3 u.c21) (Nat.add (Nat.mul u.c8 u.c10) 0)))) 1) (0))
def sc43 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c43) (Nat.add (Nat.mul u.c3 u.c22) 0)) 1) (Nat.add (Nat.mul u.c9 u.c9) 0))
def sc44 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c44) (Nat.add (Nat.mul u.c3 u.c23) (Nat.add (Nat.mul u.c9 u.c10) 0))) 1) (0))
def sc45 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c45) 0) 1) (Nat.add (Nat.mul u.c10 u.c10) 0))

/-- the square (each symmetric product once) -/
def sq (u : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul u.st.n1 u.st.n4) (Nat.mul u.st.n2 u.st.n3)) (Nat.mul u.st.n2 u.st.n4)) (Nat.mul u.st.n3 u.st.n2)) (Nat.mul u.st.n3 u.st.n3)) (Nat.mul u.st.n3 u.st.n4)) (Nat.mul u.st.n4 u.st.n1)) (Nat.mul u.st.n4 u.st.n2)) (Nat.mul u.st.n4 u.st.n3)) (Nat.mul u.st.n4 u.st.n4))) NR)
  mk (sc0 u) (sc1 u) (sc2 u) (sc3 u) (sc4 u) (sc5 u) (sc6 u) (sc7 u) (sc8 u) (sc9 u) (sc10 u) (sc11 u) (sc12 u) (sc13 u) (sc14 u) (sc15 u) (sc16 u) (sc17 u) (sc18 u) (sc19 u) (sc20 u) (sc21 u) (sc22 u) (sc23 u) (sc24 u) (sc25 u) (sc26 u) (sc27 u) (sc28 u) (sc29 u) (sc30 u) (sc31 u) (sc32 u) (sc33 u) (sc34 u) (sc35 u) (sc36 u) (sc37 u) (sc38 u) (sc39 u) (sc40 u) (sc41 u) (sc42 u) (sc43 u) (sc44 u) (sc45 u)
    ((((prng u).mul u.R).add (u.R.mul (rng u))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as u.st.as) NP)) NR)
    (u.ok && Nat.ble u.st.as LIM)

/-- the truncated product of the polynomial parts (series only) -/
def pmul (u v : T) : T := mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) (mc15 u v) (mc16 u v) (mc17 u v) (mc18 u v) (mc19 u v) (mc20 u v) (mc21 u v) (mc22 u v) (mc23 u v) (mc24 u v) (mc25 u v) (mc26 u v) (mc27 u v) (mc28 u v) (mc29 u v) (mc30 u v) (mc31 u v) (mc32 u v) (mc33 u v) (mc34 u v) (mc35 u v) (mc36 u v) (mc37 u v) (mc38 u v) (mc39 u v) (mc40 u v) (mc41 u v) (mc42 u v) (mc43 u v) (mc44 u v) (mc45 u v) I.zero 0 true

/-- the constant `n` -/
def cst (n : Int) : T :=
  match n with
  | .ofNat j => mk (Nat.add Bp (Nat.mul j ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul j ONE) true
  | .negSucc j => mk (Nat.sub Bp (Nat.mul (Nat.succ j) ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul (Nat.succ j) ONE)
      (Nat.ble (Nat.mul (Nat.succ j) ONE) Bp)

/-- the point `(x - Bb) / 2^96` (`x` with the bias of `I`) -/
def ptB (x : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t0` -/
def var0 (x r : Nat) : T := mk (Nat.add x DB) (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t1` -/
def var1 (x r : Nat) : T := mk (Nat.add x DB) Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t2` -/
def var2 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t3` -/
def var3 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- `u` without its constant term, times the point `s` (series only) -/
def tail (s : Nat) (u : T) : T := mk Bp (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) (pmul1 s u.c24) (pmul1 s u.c25) (pmul1 s u.c26) (pmul1 s u.c27) (pmul1 s u.c28) (pmul1 s u.c29) (pmul1 s u.c30) (pmul1 s u.c31) (pmul1 s u.c32) (pmul1 s u.c33) (pmul1 s u.c34) (pmul1 s u.c35) (pmul1 s u.c36) (pmul1 s u.c37) (pmul1 s u.c38) (pmul1 s u.c39) (pmul1 s u.c40) (pmul1 s u.c41) (pmul1 s u.c42) (pmul1 s u.c43) (pmul1 s u.c44) (pmul1 s u.c45) I.zero 0 true

/-- `c + u` for a point `c` (series only) -/
def addc (c : Nat) (u : T) : T := mk (Nat.sub (Nat.add c u.c0) Bp) u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 u.c24 u.c25 u.c26 u.c27 u.c28 u.c29 u.c30 u.c31 u.c32 u.c33 u.c34 u.c35 u.c36 u.c37 u.c38 u.c39 u.c40 u.c41 u.c42 u.c43 u.c44 u.c45 I.zero 0 true

/-- `c + s u` for points `c`, `s` (series only) -/
def axpy (c s : Nat) (u : T) : T :=
  mk (Nat.sub (Nat.add c (pmul1 s u.c0)) Bp) (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) (pmul1 s u.c15) (pmul1 s u.c16) (pmul1 s u.c17) (pmul1 s u.c18) (pmul1 s u.c19) (pmul1 s u.c20) (pmul1 s u.c21) (pmul1 s u.c22) (pmul1 s u.c23) (pmul1 s u.c24) (pmul1 s u.c25) (pmul1 s u.c26) (pmul1 s u.c27) (pmul1 s u.c28) (pmul1 s u.c29) (pmul1 s u.c30) (pmul1 s u.c31) (pmul1 s u.c32) (pmul1 s u.c33) (pmul1 s u.c34) (pmul1 s u.c35) (pmul1 s u.c36) (pmul1 s u.c37) (pmul1 s u.c38) (pmul1 s u.c39) (pmul1 s u.c40) (pmul1 s u.c41) (pmul1 s u.c42) (pmul1 s u.c43) (pmul1 s u.c44) (pmul1 s u.c45) I.zero 0 true

/-- the polynomial of `u` with the remainder `R`, the exact `A` and the flag `ok` -/
def withR (u : T) (R : I) (ok : Bool) : T := mk u.c0 u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 u.c15 u.c16 u.c17 u.c18 u.c19 u.c20 u.c21 u.c22 u.c23 u.c24 u.c25 u.c26 u.c27 u.c28 u.c29 u.c30 u.c31 u.c32 u.c33 u.c34 u.c35 u.c36 u.c37 u.c38 u.c39 u.c40 u.c41 u.c42 u.c43 u.c44 u.c45 R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs u.c0) (pabs u.c1)) (pabs u.c2)) (pabs u.c3)) (pabs u.c4)) (pabs u.c5)) (pabs u.c6)) (pabs u.c7)) (pabs u.c8)) (pabs u.c9)) (pabs u.c10)) (pabs u.c11)) (pabs u.c12)) (pabs u.c13)) (pabs u.c14)) (pabs u.c15)) (pabs u.c16)) (pabs u.c17)) (pabs u.c18)) (pabs u.c19)) (pabs u.c20)) (pabs u.c21)) (pabs u.c22)) (pabs u.c23)) (pabs u.c24)) (pabs u.c25)) (pabs u.c26)) (pabs u.c27)) (pabs u.c28)) (pabs u.c29)) (pabs u.c30)) (pabs u.c31)) (pabs u.c32)) (pabs u.c33)) (pabs u.c34)) (pabs u.c35)) (pabs u.c36)) (pabs u.c37)) (pabs u.c38)) (pabs u.c39)) (pabs u.c40)) (pabs u.c41)) (pabs u.c42)) (pabs u.c43)) (pabs u.c44)) (pabs u.c45)) ok

/-- the truncated series of `1/v` (any polynomial is sound) -/
def invSeries (v : T) : T :=
  let y0 := rcp v.c0
  let t := tail (Nat.sub Bp2 y0) v
  let P4 := addc (Nat.add Bp ONE) t
  let P3 := addc (Nat.add Bp ONE) (pmul t P4)
  let P2 := addc (Nat.add Bp ONE) (pmul t P3)
  let P1 := addc (Nat.add Bp ONE) (pmul t P2)
  axpy Bp y0 P1

/-- the truncated series of `√v` (any polynomial is sound) -/
def sqrtSeries (v : T) : T :=
  let s0 := rsq v.c0
  let t := tail (rcp v.c0) v
  let Q4 := addc (fracN 5 128) (cst 0)
  let Q3 := addc (frac 1 16) (pmul t Q4)
  let Q2 := addc (fracN 1 8) (pmul t Q3)
  let Q1 := addc (frac 1 2) (pmul t Q2)
  axpy s0 s0 (pmul t Q1)

/-- `Y` with the remainder `rng(E) · iv`, given `iv` (if defined) -/
def resid (Y E : T) (ok : Bool) : Option I → Option T
  | some iv => some (withR Y ((rng E).mul iv) (ok && E.ok))
  | none => none

def inv (v : T) : Option T :=
  let Y := withR (invSeries v) I.zero true
  resid Y (sub (cst 1) (mul v Y)) v.ok (rng v).inv

def sqrt (v : T) : Option T :=
  let Y := withR (sqrtSeries v) I.zero true
  resid Y (sub v (mul Y Y)) v.ok (sqrtDen (rng Y) (rng v).sqrt)

def div (u v : T) : Option T := Option.map (mul u) (inv v)

/-- Taylor-model arithmetic -/
instance tfOps : Ops (Option T) where
  add x y := match x, y with | some a, some b => some (add a b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (sub a b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (mul a b) | _, _ => none
  div x y := match x, y with | some a, some b => div a b | _, _ => none
  neg x := match x with | some a => some (neg a) | none => none
  sqrt x := match x with | some a => sqrt a | none => none
  sq x := match x with | some a => some (sq a) | none => none
  ofInt n := some (cst n)

/-- the model is valid and its range is positive -/
def posT : Option T → Bool
  | some u => u.ok && posLo (rng u)
  | none => false

/-- every zero of the enclosed function in the box has `|t₃| ≤ ρ/2^96`: writing the polynomial as
`p₀(t) + t₃ q(t)`, `|t₃| |q| ≤ |p₀| + |R|` at a zero, and `|q| ≥ qmin` -/
def newtOK (rho : Nat) : Option T → Bool
  | some p =>
    let qmin := Nat.sub (pabs p.c10) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c17) (pabs p.c21)) (pabs p.c23)) (pabs p.c30)) (pabs p.c34)) (pabs p.c36)) (pabs p.c40)) (pabs p.c42)) (pabs p.c44)) (pabs p.c45))
    p.ok && Nat.ble 1 qmin &&
      Nat.ble (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c0) (pabs p.c1)) (pabs p.c2)) (pabs p.c3)) (pabs p.c4)) (pabs p.c5)) (pabs p.c6)) (pabs p.c7)) (pabs p.c8)) (pabs p.c9)) (pabs p.c11)) (pabs p.c12)) (pabs p.c13)) (pabs p.c14)) (pabs p.c15)) (pabs p.c16)) (pabs p.c18)) (pabs p.c19)) (pabs p.c20)) (pabs p.c22)) (pabs p.c24)) (pabs p.c25)) (pabs p.c26)) (pabs p.c27)) (pabs p.c28)) (pabs p.c29)) (pabs p.c31)) (pabs p.c32)) (pabs p.c33)) (pabs p.c35)) (pabs p.c37)) (pabs p.c38)) (pabs p.c39)) (pabs p.c41)) (pabs p.c43)) (rmag p.R)) ONE) (Nat.mul rho qmin)
  | none => false

end TF.W5

namespace TF.F3

/-! ## `F3`: graded degree `< 3` for grades `[1, 1, 1, 1]`, 15 monomials, 45 coefficient products per product

`c0` 1, `c1` t0, `c2` t1, `c3` t2, `c4` t3, `c5` t0^2, `c6` t0·t1, `c7` t0·t2, `c8` t0·t3, `c9` t1^2, `c10` t1·t2, `c11` t1·t3, `c12` t2^2, `c13` t2·t3, `c14` t3^2. -/

/-- the rounding allowance of a product, in offset units -/
def NR : Nat := 15
/-- the number of coefficient products of a product -/
def NP : Nat := 45

/-- grade norms `n_d = Σ_{deg k = d} |c_k - Bp|`, the range `⟨lo, hi⟩` of the polynomial on the box, and
`as = Σ_k |c_k - Bp|` -/
structure St where
  n1 : Nat
  n2 : Nat
  lo : Nat
  hi : Nat
  as : Nat

def statsOf (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Nat) : St :=
  ⟨(Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))), (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5)) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.sub c12 Bp)) (Nat.sub Bp c12)) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.sub c14 Bp)) (Nat.sub Bp c14)), Nat.sub (Nat.add (Nat.add BpB (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13)))) (Nat.add (Nat.add (Nat.add (Nat.sub Bp c5) (Nat.sub Bp c9)) (Nat.sub Bp c12)) (Nat.sub Bp c14))) c0, Nat.sub (Nat.add (Nat.add c0 Bb) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4))) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub c9 Bp)) (Nat.sub c12 Bp)) (Nat.sub c14 Bp)))) Bp, Nat.add (Nat.add (Nat.add (Nat.sub c0 Bp) (Nat.sub Bp c0)) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c1 Bp) (Nat.sub Bp c1)) (Nat.add (Nat.sub c2 Bp) (Nat.sub Bp c2))) (Nat.add (Nat.sub c3 Bp) (Nat.sub Bp c3))) (Nat.add (Nat.sub c4 Bp) (Nat.sub Bp c4)))) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.sub c5 Bp) (Nat.sub Bp c5)) (Nat.add (Nat.sub c6 Bp) (Nat.sub Bp c6))) (Nat.add (Nat.sub c7 Bp) (Nat.sub Bp c7))) (Nat.add (Nat.sub c8 Bp) (Nat.sub Bp c8))) (Nat.sub c9 Bp)) (Nat.sub Bp c9)) (Nat.add (Nat.sub c10 Bp) (Nat.sub Bp c10))) (Nat.add (Nat.sub c11 Bp) (Nat.sub Bp c11))) (Nat.sub c12 Bp)) (Nat.sub Bp c12)) (Nat.add (Nat.sub c13 Bp) (Nat.sub Bp c13))) (Nat.sub c14 Bp)) (Nat.sub Bp c14))⟩

structure T where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
  c8 : Nat
  c9 : Nat
  c10 : Nat
  c11 : Nat
  c12 : Nat
  c13 : Nat
  c14 : Nat
  R : I
  A : Nat
  ok : Bool
  st : St

def mk (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Nat) (R : I) (A : Nat) (ok : Bool) : T :=
  ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, R, A, ok, statsOf c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14⟩

/-- the range of the polynomial part -/
def prng (u : T) : I := ⟨u.st.lo, u.st.hi⟩

/-- the range of the model -/
def rng (u : T) : I := (prng u).add u.R

def add (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 v.c0) Bp) (Nat.sub (Nat.add u.c1 v.c1) Bp) (Nat.sub (Nat.add u.c2 v.c2) Bp) (Nat.sub (Nat.add u.c3 v.c3) Bp) (Nat.sub (Nat.add u.c4 v.c4) Bp) (Nat.sub (Nat.add u.c5 v.c5) Bp) (Nat.sub (Nat.add u.c6 v.c6) Bp) (Nat.sub (Nat.add u.c7 v.c7) Bp) (Nat.sub (Nat.add u.c8 v.c8) Bp) (Nat.sub (Nat.add u.c9 v.c9) Bp) (Nat.sub (Nat.add u.c10 v.c10) Bp) (Nat.sub (Nat.add u.c11 v.c11) Bp) (Nat.sub (Nat.add u.c12 v.c12) Bp) (Nat.sub (Nat.add u.c13 v.c13) Bp) (Nat.sub (Nat.add u.c14 v.c14) Bp)
    (u.R.add v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def sub (u v : T) : T :=
  mk (Nat.sub (Nat.add u.c0 Bp) v.c0) (Nat.sub (Nat.add u.c1 Bp) v.c1) (Nat.sub (Nat.add u.c2 Bp) v.c2) (Nat.sub (Nat.add u.c3 Bp) v.c3) (Nat.sub (Nat.add u.c4 Bp) v.c4) (Nat.sub (Nat.add u.c5 Bp) v.c5) (Nat.sub (Nat.add u.c6 Bp) v.c6) (Nat.sub (Nat.add u.c7 Bp) v.c7) (Nat.sub (Nat.add u.c8 Bp) v.c8) (Nat.sub (Nat.add u.c9 Bp) v.c9) (Nat.sub (Nat.add u.c10 Bp) v.c10) (Nat.sub (Nat.add u.c11 Bp) v.c11) (Nat.sub (Nat.add u.c12 Bp) v.c12) (Nat.sub (Nat.add u.c13 Bp) v.c13) (Nat.sub (Nat.add u.c14 Bp) v.c14)
    (u.R.sub v.R) (Nat.add u.A v.A) (u.ok && v.ok && Nat.ble (Nat.add u.A v.A) LIMA)

def neg (u : T) : T :=
  mk (Nat.sub Bp2 u.c0) (Nat.sub Bp2 u.c1) (Nat.sub Bp2 u.c2) (Nat.sub Bp2 u.c3) (Nat.sub Bp2 u.c4) (Nat.sub Bp2 u.c5) (Nat.sub Bp2 u.c6) (Nat.sub Bp2 u.c7) (Nat.sub Bp2 u.c8) (Nat.sub Bp2 u.c9) (Nat.sub Bp2 u.c10) (Nat.sub Bp2 u.c11) (Nat.sub Bp2 u.c12) (Nat.sub Bp2 u.c13) (Nat.sub Bp2 u.c14) u.R.neg u.A (u.ok && Nat.ble u.A LIMA)

def mc0 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c0) 0)
def mc1 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c1) (Nat.add (Nat.mul u.c1 v.c0) 0))
def mc2 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c2) (Nat.add (Nat.mul u.c2 v.c0) 0))
def mc3 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c3) (Nat.add (Nat.mul u.c3 v.c0) 0))
def mc4 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c4) (Nat.add (Nat.mul u.c4 v.c0) 0))
def mc5 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c5) (Nat.add (Nat.mul u.c1 v.c1) (Nat.add (Nat.mul u.c5 v.c0) 0)))
def mc6 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c6) (Nat.add (Nat.mul u.c1 v.c2) (Nat.add (Nat.mul u.c2 v.c1) (Nat.add (Nat.mul u.c6 v.c0) 0))))
def mc7 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c7) (Nat.add (Nat.mul u.c1 v.c3) (Nat.add (Nat.mul u.c3 v.c1) (Nat.add (Nat.mul u.c7 v.c0) 0))))
def mc8 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c8) (Nat.add (Nat.mul u.c1 v.c4) (Nat.add (Nat.mul u.c4 v.c1) (Nat.add (Nat.mul u.c8 v.c0) 0))))
def mc9 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c9) (Nat.add (Nat.mul u.c2 v.c2) (Nat.add (Nat.mul u.c9 v.c0) 0)))
def mc10 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c10) (Nat.add (Nat.mul u.c2 v.c3) (Nat.add (Nat.mul u.c3 v.c2) (Nat.add (Nat.mul u.c10 v.c0) 0))))
def mc11 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c11) (Nat.add (Nat.mul u.c2 v.c4) (Nat.add (Nat.mul u.c4 v.c2) (Nat.add (Nat.mul u.c11 v.c0) 0))))
def mc12 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c12) (Nat.add (Nat.mul u.c3 v.c3) (Nat.add (Nat.mul u.c12 v.c0) 0)))
def mc13 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c13) (Nat.add (Nat.mul u.c3 v.c4) (Nat.add (Nat.mul u.c4 v.c3) (Nat.add (Nat.mul u.c13 v.c0) 0))))
def mc14 (u v : T) : Nat := fin (Nat.add (Nat.mul u.c0 v.c14) (Nat.add (Nat.mul u.c4 v.c4) (Nat.add (Nat.mul u.c14 v.c0) 0)))

/-- the product -/
def mul (u v : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.mul u.st.n1 v.st.n2) (Nat.mul u.st.n2 v.st.n1)) (Nat.mul u.st.n2 v.st.n2))) NR)
  mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v)
    ((((prng u).mul v.R).add (u.R.mul (rng v))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as v.st.as) NP)) NR)
    (u.ok && v.ok && Nat.ble u.st.as LIM && Nat.ble v.st.as LIM)

def sc0 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (0) 1) (Nat.add (Nat.mul u.c0 u.c0) 0))
def sc1 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c1) 0) 1) (0))
def sc2 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c2) 0) 1) (0))
def sc3 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c3) 0) 1) (0))
def sc4 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c4) 0) 1) (0))
def sc5 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c5) 0) 1) (Nat.add (Nat.mul u.c1 u.c1) 0))
def sc6 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c6) (Nat.add (Nat.mul u.c1 u.c2) 0)) 1) (0))
def sc7 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c7) (Nat.add (Nat.mul u.c1 u.c3) 0)) 1) (0))
def sc8 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c8) (Nat.add (Nat.mul u.c1 u.c4) 0)) 1) (0))
def sc9 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c9) 0) 1) (Nat.add (Nat.mul u.c2 u.c2) 0))
def sc10 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c10) (Nat.add (Nat.mul u.c2 u.c3) 0)) 1) (0))
def sc11 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c11) (Nat.add (Nat.mul u.c2 u.c4) 0)) 1) (0))
def sc12 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c12) 0) 1) (Nat.add (Nat.mul u.c3 u.c3) 0))
def sc13 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c13) (Nat.add (Nat.mul u.c3 u.c4) 0)) 1) (0))
def sc14 (u : T) : Nat := fin (Nat.add (Nat.shiftLeft (Nat.add (Nat.mul u.c0 u.c14) 0) 1) (Nat.add (Nat.mul u.c4 u.c4) 0))

/-- the square (each symmetric product once) -/
def sq (u : T) : T :=
  let E := Nat.add Bb (Nat.add (I.up (Nat.add (Nat.add (Nat.mul u.st.n1 u.st.n2) (Nat.mul u.st.n2 u.st.n1)) (Nat.mul u.st.n2 u.st.n2))) NR)
  mk (sc0 u) (sc1 u) (sc2 u) (sc3 u) (sc4 u) (sc5 u) (sc6 u) (sc7 u) (sc8 u) (sc9 u) (sc10 u) (sc11 u) (sc12 u) (sc13 u) (sc14 u)
    ((((prng u).mul u.R).add (u.R.mul (rng u))).add ⟨E, E⟩) (Nat.add (I.up (Nat.mul (Nat.mul u.st.as u.st.as) NP)) NR)
    (u.ok && Nat.ble u.st.as LIM)

/-- the truncated product of the polynomial parts (series only) -/
def pmul (u v : T) : T := mk (mc0 u v) (mc1 u v) (mc2 u v) (mc3 u v) (mc4 u v) (mc5 u v) (mc6 u v) (mc7 u v) (mc8 u v) (mc9 u v) (mc10 u v) (mc11 u v) (mc12 u v) (mc13 u v) (mc14 u v) I.zero 0 true

/-- the constant `n` -/
def cst (n : Int) : T :=
  match n with
  | .ofNat j => mk (Nat.add Bp (Nat.mul j ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul j ONE) true
  | .negSucc j => mk (Nat.sub Bp (Nat.mul (Nat.succ j) ONE)) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.mul (Nat.succ j) ONE)
      (Nat.ble (Nat.mul (Nat.succ j) ONE) Bp)

/-- the point `(x - Bb) / 2^96` (`x` with the bias of `I`) -/
def ptB (x : Nat) : T := mk (Nat.add x DB) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t0` -/
def var0 (x r : Nat) : T := mk (Nat.add x DB) (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t1` -/
def var1 (x r : Nat) : T := mk (Nat.add x DB) Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t2` -/
def var2 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- the coordinate `(x - Bb)/2^96 + (r/2^96) t3` -/
def var3 (x r : Nat) : T := mk (Nat.add x DB) Bp Bp Bp (Nat.add Bp r) Bp Bp Bp Bp Bp Bp Bp Bp Bp Bp I.zero (Nat.add (Nat.add (Nat.sub x Bb) (Nat.sub Bb x)) r) true

/-- `u` without its constant term, times the point `s` (series only) -/
def tail (s : Nat) (u : T) : T := mk Bp (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) I.zero 0 true

/-- `c + u` for a point `c` (series only) -/
def addc (c : Nat) (u : T) : T := mk (Nat.sub (Nat.add c u.c0) Bp) u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 I.zero 0 true

/-- `c + s u` for points `c`, `s` (series only) -/
def axpy (c s : Nat) (u : T) : T :=
  mk (Nat.sub (Nat.add c (pmul1 s u.c0)) Bp) (pmul1 s u.c1) (pmul1 s u.c2) (pmul1 s u.c3) (pmul1 s u.c4) (pmul1 s u.c5) (pmul1 s u.c6) (pmul1 s u.c7) (pmul1 s u.c8) (pmul1 s u.c9) (pmul1 s u.c10) (pmul1 s u.c11) (pmul1 s u.c12) (pmul1 s u.c13) (pmul1 s u.c14) I.zero 0 true

/-- the polynomial of `u` with the remainder `R`, the exact `A` and the flag `ok` -/
def withR (u : T) (R : I) (ok : Bool) : T := mk u.c0 u.c1 u.c2 u.c3 u.c4 u.c5 u.c6 u.c7 u.c8 u.c9 u.c10 u.c11 u.c12 u.c13 u.c14 R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs u.c0) (pabs u.c1)) (pabs u.c2)) (pabs u.c3)) (pabs u.c4)) (pabs u.c5)) (pabs u.c6)) (pabs u.c7)) (pabs u.c8)) (pabs u.c9)) (pabs u.c10)) (pabs u.c11)) (pabs u.c12)) (pabs u.c13)) (pabs u.c14)) ok

/-- the truncated series of `1/v` (any polynomial is sound) -/
def invSeries (v : T) : T :=
  let y0 := rcp v.c0
  let t := tail (Nat.sub Bp2 y0) v
  let P2 := addc (Nat.add Bp ONE) t
  let P1 := addc (Nat.add Bp ONE) (pmul t P2)
  axpy Bp y0 P1

/-- the truncated series of `√v` (any polynomial is sound) -/
def sqrtSeries (v : T) : T :=
  let s0 := rsq v.c0
  let t := tail (rcp v.c0) v
  let Q2 := addc (fracN 1 8) (cst 0)
  let Q1 := addc (frac 1 2) (pmul t Q2)
  axpy s0 s0 (pmul t Q1)

/-- `Y` with the remainder `rng(E) · iv`, given `iv` (if defined) -/
def resid (Y E : T) (ok : Bool) : Option I → Option T
  | some iv => some (withR Y ((rng E).mul iv) (ok && E.ok))
  | none => none

def inv (v : T) : Option T :=
  let Y := withR (invSeries v) I.zero true
  resid Y (sub (cst 1) (mul v Y)) v.ok (rng v).inv

def sqrt (v : T) : Option T :=
  let Y := withR (sqrtSeries v) I.zero true
  resid Y (sub v (mul Y Y)) v.ok (sqrtDen (rng Y) (rng v).sqrt)

def div (u v : T) : Option T := Option.map (mul u) (inv v)

/-- Taylor-model arithmetic -/
instance tfOps : Ops (Option T) where
  add x y := match x, y with | some a, some b => some (add a b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (sub a b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (mul a b) | _, _ => none
  div x y := match x, y with | some a, some b => div a b | _, _ => none
  neg x := match x with | some a => some (neg a) | none => none
  sqrt x := match x with | some a => sqrt a | none => none
  sq x := match x with | some a => some (sq a) | none => none
  ofInt n := some (cst n)

/-- the model is valid and its range is positive -/
def posT : Option T → Bool
  | some u => u.ok && posLo (rng u)
  | none => false

/-- every zero of the enclosed function in the box has `|t₃| ≤ ρ/2^96`: writing the polynomial as
`p₀(t) + t₃ q(t)`, `|t₃| |q| ≤ |p₀| + |R|` at a zero, and `|q| ≥ qmin` -/
def newtOK (rho : Nat) : Option T → Bool
  | some p =>
    let qmin := Nat.sub (pabs p.c4) (Nat.add (Nat.add (Nat.add (pabs p.c8) (pabs p.c11)) (pabs p.c13)) (pabs p.c14))
    p.ok && Nat.ble 1 qmin &&
      Nat.ble (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (pabs p.c0) (pabs p.c1)) (pabs p.c2)) (pabs p.c3)) (pabs p.c5)) (pabs p.c6)) (pabs p.c7)) (pabs p.c9)) (pabs p.c10)) (pabs p.c12)) (rmag p.R)) ONE) (Nat.mul rho qmin)
  | none => false

end TF.F3

end C4
