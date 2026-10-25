module

public import C4Check.Formulas2
public import C4Check.Search

@[expose] public section

/-!
# Replaying a branch and bound with sheared leaves

The replay of `C4Check.Search`, with a new leaf.  For a 3-box `B` of the independent coordinates
`z`, the dependent coordinate `x` (resp. `xi`) is bounded and its feasible zeros localised exactly
as in the first-order checker (`C4Check.Search`: `xrange`, then `locH` on its mode `Mode2.toMode`,
which has the same constraints and `P`).  Each kept interval `Y` is then certified by a *sheared leaf*: with the quadratic shear
`x₀(z) = X₀ + Σ J_i δ_i + Σ_{i≤j} H_ij δ_i δ_j`, `δ = z - z̄` (`z̄` the centre of `B`), every
feasible zero `x ∈ Y` has `w = x - x₀(z) ∈ W₀ = Y - x₀(B)`, and an *evaluator* certifies the
normalized midpoint test (`det Y > 0`, `tr Y > 0`, `C4Check.Formulas2.dirMidN`) at every feasible
zero `x = x₀(z) + w` with `w ∈ W₀`:
* `ev = 0`, the built-in first-order evaluator: `k` Newton steps (`pstepG` of `C4Check.Search` on the jets
  of `g` and `P` in the coordinates `(z, w)`) shrink `W₀` to an interval `E` that still holds the `w` of
  every feasible zero, and on `B × E` the jets of the test show `det Y - μ g_f > 0` (`μ ≥ 0`, `f` a
  face from the hint, or `μ = 0`) and `tr Y > 0`;
* `ev = 1`, the mode's own evaluator `Mode2.ev2` (e.g. order-3 Taylor forms), with its own
  soundness proof.
A leaf may instead be a *corner-disc leaf* (in a mode with `disc = some k`): the box lies in
`{b ≥ 0, b² + (ga - 1)² ≤ 4^-k}`, checked exactly; those points are left to the corner theorem.

The hint is read from the least significant end, as in the replay of `C4Check.Search`:
* a 2-bit symbol: `0` = leaf, `1`, `2`, `3` = split along coordinate `0`, `1`, `2` (the hints of
  the two halves follow);
* at a leaf, 1 bit: `0` = sheared leaf, `1` = corner-disc leaf (nothing follows);
* at a sheared leaf, unless the range of `x` is empty: the localisation symbols of `C4Check.Search`, then one record
  of 401 bits per kept interval `Y`, from the low end: `X₀` (64 bits, `ctr Y + (m - 2^63) 2^-60`),
  `J₀`, `J₁`, `J₂` (32 bits each, `(m - 2^31) 2^-24`), `H₀₀`, `H₀₁`, `H₀₂`, `H₁₁`, `H₁₂`, `H₂₂`
  (32 bits each, `(m - 2^31) 2^-20`), `ev` (1 bit), and 48 bits for the evaluator; the built-in
  one reads `k` (2 bits), the `μ` flag (1 bit), `f` (3 bits) and `μ` (32 bits, `m 2^-24`).
Every value read from the hint is a parameter of a check that is sound for every value (only
`μ ≥ 0` matters, and it holds by construction), so a wrong hint can only make the check fail.
As in `C4Check.Search`, every test on a computed interval sits in a small definition that takes the interval as
an argument, and every other `match` is on an argument or goes through `Option.bind`.
-/

namespace C4

/-- a quadratic shear `x₀(z) = X₀ + Σ J_i δ_i + Σ_{i≤j} H_ij δ_i δ_j` (biased fixed-point values) -/
structure Shear where
  X0 : Nat
  J0 : Nat
  J1 : Nat
  J2 : Nat
  H00 : Nat
  H01 : Nat
  H02 : Nat
  H11 : Nat
  H12 : Nat
  H22 : Nat
deriving Inhabited

/-- what the sheared replay needs to know about a chart -/
structure Mode2 where
  /-- `(k_i, l_i)` of the six affine constraints, over a 3-box -/
  kl : I → I → I → Six (Option I) × Six (Option I)
  /-- jets of the six constraints and of `P`, for jets of the four arguments -/
  gP : Rad → J → J → J → J → Six (Option J) × Option J
  /-- jets of the outputs of the normalized test, for jets of the four arguments -/
  outJ : Rad → J → J → J → J → Out (Option J)
  /-- the mode's own leaf evaluator: on `B`, with the shear, the 48 evaluator bits of the record
  and the `w`-range `W₀`; sound in the sense of `ModeSound2.ev2` -/
  ev2 : Box → Shear → Nat → I → Bool
  /-- whether to clamp the dependent coordinate to `[-1, 1]` -/
  clamp : Bool
  /-- `some k`: a box inside the corner disc `b² + (ga - 1)² ≤ 4^-k` (coordinates `0` and `2`)
  may be left to the corner theorem -/
  disc : Option Nat

/-- the mode of the first-order checker (`C4Check.Search`) with the same constraints and `P` and no
`tr S` jet: its `xrange` and `locH` run on it -/
def Mode2.toMode (M : Mode2) : Mode := ⟨M.kl, M.gP, fun _ _ _ _ _ _ _ => none, M.clamp⟩

/-! ## the shear -/

/-- `A` widened by the offset `E` on both sides -/
def widen (A : I) (E : Nat) : I := ⟨Nat.add A.L E, Nat.add A.H E⟩

/-- the jet of `x = x₀(z) + w` on a 4-box whose last factor is `W`, about its centre (`w` is the
fourth coordinate, with centre `ctr W`): slopes `J₀ + H₀₀ δ₀ + H₀₁ δ₁ + H₀₂ δ₂`,
`J₁ + H₁₁ δ₁ + H₁₂ δ₂`, `J₂ + H₂₂ δ₂`, `1` -/
def shearJ (R : Rad) (sh : Shear) (W : I) : J :=
  ⟨J.cf R ((I.pt sh.X0).add (I.pt (I.ctr W)))
      (widen (I.pt sh.J0) (Nat.add (Nat.add (I.eterm (I.pt sh.H00) R.r0)
        (I.eterm (I.pt sh.H01) R.r1)) (I.eterm (I.pt sh.H02) R.r2)))
      (widen (I.pt sh.J1) (Nat.add (I.eterm (I.pt sh.H11) R.r1) (I.eterm (I.pt sh.H12) R.r2)))
      (widen (I.pt sh.J2) (I.eterm (I.pt sh.H22) R.r2)) I.one,
    (I.pt sh.X0).add (I.pt (I.ctr W)),
    widen (I.pt sh.J0) (Nat.add (Nat.add (I.eterm (I.pt sh.H00) R.r0)
      (I.eterm (I.pt sh.H01) R.r1)) (I.eterm (I.pt sh.H02) R.r2)),
    widen (I.pt sh.J1) (Nat.add (I.eterm (I.pt sh.H11) R.r1) (I.eterm (I.pt sh.H12) R.r2)),
    widen (I.pt sh.J2) (I.eterm (I.pt sh.H22) R.r2), I.one⟩

/-- the range of `x₀` over `B` -/
def x0range (B : Box) (sh : Shear) : I := (shearJ (rad B I.zero) sh I.zero).U

/-- the jets of `g` and `P` on `B × W` in the coordinates `(z, w)` -/
def sgP (M : Mode2) (B : Box) (sh : Shear) (W : I) : Six (Option J) × Option J :=
  M.gP (rad B W) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (shearJ (rad B W) sh W)

/-- `k` Newton steps in the coordinates `(z, w)`, from `W` -/
def snewton (M : Mode2) (B : Box) (sh : Shear) : Nat → I → Option I
  | 0, W => some W
  | k + 1, W => (pstepG (rad B W) W (sgP M B sh W)).bind (snewton M B sh k)

/-! ## the built-in evaluator -/

/-- the jets of the outputs on `B × E` in the coordinates `(z, w)` -/
def sout (M : Mode2) (B : Box) (sh : Shear) (E : I) : Out (Option J) :=
  M.outJ (rad B E) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (shearJ (rad B E) sh E)

/-- the constraint `g_f` (none for `f > 5`) -/
def gsel (g : Six (Option J)) (f : Nat) : Option J :=
  sel (Nat.beq f 0) g.x1 (sel (Nat.beq f 1) g.x2 (sel (Nat.beq f 2) g.x3
    (sel (Nat.beq f 3) g.x4 (sel (Nat.beq f 4) g.x5 (sel (Nat.beq f 5) g.x6 none)))))

/-- `d - μ g` -/
def subMu (R : Rad) (mu : Nat) : Option J → Option J → Option J
  | some d, some g => some (d.sub (J.mul R (J.cst (I.pt mu)) g))
  | _, _ => none

/-- `A > 0`: the lower end of `A` is positive -/
def posL (A : I) : Bool := sel (Nat.ble Bb A.L) false true

/-- the jet is positive on the box -/
def posJ (R : Rad) : Option J → Bool
  | some j => posL (J.range R j)
  | none => false

/-- `a && b` (a bare `Bool.casesOn`) -/
def both (a b : Bool) : Bool := sel a b false

/-- `det Y - μ g_f > 0` (or `det Y > 0` if the flag `mf` is `0`) and `tr Y > 0` on the box -/
def stest (R : Rad) (mf f mu : Nat) (o : Out (Option J)) : Bool :=
  both (posJ R (sel (Nat.beq mf 0) o.det (subMu R mu o.det (gsel o.g f)))) (posJ R o.tr)

/-- `t`, unless `E` is empty (then there is nothing to test) -/
def ifNE (E : I) (t : Bool) : Bool := cond (I.isEmpty E) true t

/-- the test on `B × E` -/
def stestE (M : Mode2) (B : Box) (sh : Shear) (mf f mu : Nat) : Option I → Bool
  | some E => ifNE E (stest (rad B E) mf f mu (sout M B sh E))
  | none => false

/-- `m 2^-24 ≥ 0` for a 32-bit field -/
def muDec (m : Nat) : Nat := Nat.add Bb (Nat.shiftLeft m 72)

/-- the built-in evaluator: `k` Newton steps from `W`, then the jet test (`fl` holds `k`, the `μ`
flag, `f` and `μ`) -/
def evJ1 (M : Mode2) (B : Box) (sh : Shear) (fl : Nat) (W : I) : Bool :=
  stestE M B sh (Nat.land (Nat.shiftRight fl 2) 1) (Nat.land (Nat.shiftRight fl 3) 7)
    (muDec (Nat.land (Nat.shiftRight fl 6) 4294967295)) (snewton M B sh (Nat.land fl 3) W)

/-! ## reading the hint -/

/-- `ctr Y + (m - 2^63) 2^-60` for a 64-bit field -/
def x0Dec (Y : I) (m : Nat) : Nat := Nat.sub (Nat.add (I.ctr Y) (Nat.shiftLeft m 36)) (2 ^ 99)

/-- `(m - 2^31) 2^-24` for a 32-bit field -/
def jDec (m : Nat) : Nat := Nat.sub (Nat.add Bb (Nat.shiftLeft m 72)) (2 ^ 103)

/-- `(m - 2^31) 2^-20` for a 32-bit field -/
def hDec (m : Nat) : Nat := Nat.sub (Nat.add Bb (Nat.shiftLeft m 76)) (2 ^ 107)

/-- the shear of the record at the low end of `h`, on the kept interval `Y` -/
def shDec (Y : I) (h : Nat) : Shear :=
  ⟨x0Dec Y (Nat.land h 18446744073709551615),
    jDec (Nat.land (Nat.shiftRight h 64) 4294967295),
    jDec (Nat.land (Nat.shiftRight h 96) 4294967295),
    jDec (Nat.land (Nat.shiftRight h 128) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 160) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 192) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 224) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 256) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 288) 4294967295),
    hDec (Nat.land (Nat.shiftRight h 320) 4294967295)⟩

/-- the sheared leaf on `Y` with the shear `sh`, evaluator bit `ev` and evaluator bits `fl` -/
def sleafF (M : Mode2) (B : Box) (Y : I) (sh : Shear) (ev fl : Nat) : Bool :=
  sel (Nat.beq ev 0) (evJ1 M B sh fl (Y.sub (x0range B sh))) (M.ev2 B sh fl (Y.sub (x0range B sh)))

/-- the sheared leaf on `Y` with the record at the low end of `h` -/
def sleafH (M : Mode2) (B : Box) (Y : I) (h : Nat) : Bool :=
  sleafF M B Y (shDec Y h) (Nat.land (Nat.shiftRight h 352) 1)
    (Nat.land (Nat.shiftRight h 353) 281474976710655)

/-- `r` if `b`, else `none` -/
def cont (b : Bool) (r : Option Nat) : Option Nat := sel b r none

/-- certify every kept interval with its record; returns the rest of the hint -/
def sAllH (M : Mode2) (B : Box) : List I → Nat → Option Nat
  | [], h => some h
  | Y :: rest, h => cont (sleafH M B Y h) (sAllH M B rest (Nat.shiftRight h 401))

/-! ## the corner disc -/

/-- `|X - Y|` -/
def adiff (X Y : Nat) : Nat := Nat.add (Nat.sub X Y) (Nat.sub Y X)

/-- the box has `b ≥ 0` and `b² + (ga - 1)² ≤ 4^-k` everywhere (`b`, `ga` its coordinates `0`,
`2`, `k ≤ 96`): exact, with `b ≤ b_hi` and `|ga - 1| ≤ max(|ga_hi - 1|, |ga_lo - 1|)` -/
def discOK (k : Nat) (B : Box) : Bool :=
  sel (Nat.ble B.X0.L Bb)
    (sel (Nat.ble k 96)
      (Nat.ble
        (Nat.add (Nat.mul (Nat.sub B.X0.H Bb) (Nat.sub B.X0.H Bb))
          (Nat.mul (I.mx (adiff B.X2.H (Nat.add Bb ONE)) (adiff (Nat.add B.X2.L ONE) Bb))
            (I.mx (adiff B.X2.H (Nat.add Bb ONE)) (adiff (Nat.add B.X2.L ONE) Bb))))
        (Nat.shiftLeft 1 (Nat.sub 192 (Nat.add k k))))
      false)
    false

/-- the corner-disc leaf (only in a mode with a disc) -/
def discLeaf (B : Box) (h : Nat) : Option Nat → Option Nat
  | some k => cont (discOK k B) (some h)
  | none => none

/-! ## the recursion -/

/-- replay the hint of a sheared leaf; returns the rest of the hint -/
def leafH2 (M : Mode2) (B : Box) (h : Nat) : Option Nat :=
  (xrange M.toMode B).bind fun X =>
    sel (I.isEmpty X) (some h) ((locH M.toMode B 4096 h [X] []).bind fun r => sAllH M B r.1 r.2)

/-- replay the hint of a box; returns the rest of the hint -/
def checkBoxH2 (M : Mode2) : Nat → Box → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, B, h =>
    sel (Nat.beq (Nat.land h 3) 0)
      (sel (Nat.beq (Nat.land (Nat.shiftRight h 2) 1) 0) (leafH2 M B (Nat.shiftRight h 3))
        (discLeaf B (Nat.shiftRight h 3) M.disc))
      ((checkBoxH2 M fuel (splitBox B (Nat.land h 3)).1 (Nat.shiftRight h 2)).bind fun h' =>
        checkBoxH2 M fuel (splitBox B (Nat.land h 3)).2 h')

end C4
