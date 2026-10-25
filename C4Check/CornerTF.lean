module

public import C4Check.Formulas2
public import C4Check.Grid

@[expose] public section

/-!
# CornerTF: Taylor forms with exact coefficients, for the corner theorem

The domain of a Taylor form is the box `b ∈ [0, ρ]`, `g ∈ [-ρ, ρ]`, `δ ∈ [-w, w]`, where
`ρ = 2^-rb` and `w = wm 2^-s`; `δ = α - α_c` is the offset from the centre of an `α`-interval.
Write `m = max b |g|`.  A Taylor form `t` of order `M` encloses `u` if at every point of the box
there are `h_p ∈ H_p` (`p ≤ M`) and `|h_r| ≤ Hr 2^-96` with
`u = Σ_d Σ_{i ≤ d} E[d][i](δ)/S · b^i g^(d-i) + Σ_p h_p b^p g^(M-p) + h_r m^(M+1)`.

* `E[d]` is the homogeneous part of degree `d`, listed by the power of `b`.  Its coefficients are
  polynomials in `δ` (listed from degree `0`) with integer coefficients, each standing for
  `n / S`, `S = 2^128 3^8`.  Every denominator met at the corner is of the form `2^a 3^b` with
  small `a, b`.
* Overflow of degree exactly `M` keeps its monomial: it goes to the interval tops `H_p`.  Overflow
  of degree `≥ M + 1` goes to the radial top `Hr`, a magnitude.
* `ok` records that every division that must be exact was exact, and that the shapes are right:
  `E[d]` has at most `d + 1` entries and there are `M + 1` tops.
* Division and square roots use any exact polynomial `Y` (the series inverse or root, computed
  here but never trusted): `1/u = Y + (1 - u Y)/u` and `√u = Y + (u - Y²)/(√u + Y)`.  The residual
  is formed in Taylor-form arithmetic, its exact part is checked to vanish, and its tops are
  multiplied by an enclosure of `1/u` (resp. `1/(√u + Y)`).
-/

namespace C4
namespace CTF

/-- the scale `2^48 · 3^8` of the exact coefficients (a small power of two keeps the low words of
the coefficients distinct: the kernel hashes number literals by their low 64 bits) -/
def S : Nat := 1846757322198614016

/-! ## integers -/

def isNeg : Int → Bool
  | .negSucc _ => true
  | .ofNat _ => false

/-- `n / d`, and whether `d ∣ n` -/
def idiv (n : Int) (d : Nat) : Int × Bool := (Int.ediv n d, Int.emod n d == 0)

/-! ## polynomials in `δ` -/

abbrev QP := List Int

def qadd : QP → QP → QP
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: qadd p q

def qneg : QP → QP
  | [] => []
  | a :: p => (-a) :: qneg p

def qsc (c : Int) : QP → QP
  | [] => []
  | a :: p => (c * a) :: qsc c p

/-- the product (the scale of the result is `S²`) -/
def qmulR : QP → QP → QP
  | [], _ => []
  | a :: p, q => qadd (qsc a q) (0 :: qmulR p q)

/-- drop trailing zero coefficients -/
def qtrim : QP → QP
  | [] => []
  | a :: p =>
    match qtrim p with
    | [] => sel (a == 0) [] [a]
    | c :: cs => a :: c :: cs

/-- divide every coefficient by `d`; `false` if a division is not exact -/
def qdiv (d : Nat) : QP → QP × Bool
  | [] => ([], true)
  | a :: p =>
    let r := idiv a d
    let t := qdiv d p
    (r.1 :: t.1, r.2 && t.2)

def qzero : QP → Bool
  | [] => true
  | a :: p => sel (a == 0) (qzero p) false

/-! ## homogeneous parts and exact parts -/

abbrev Hom := List QP
abbrev Ex := List Hom

def hadd : Hom → Hom → Hom
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => qadd a b :: hadd p q

def hneg : Hom → Hom
  | [] => []
  | a :: p => qneg a :: hneg p

def hscal (a : QP) : Hom → Hom
  | [] => []
  | c :: p => qmulR a c :: hscal a p

/-- the product of homogeneous parts (scale `S²`) -/
def hmulR : Hom → Hom → Hom
  | [], _ => []
  | a :: p, q => hadd (hscal a q) ([] :: hmulR p q)

def hdiv (d : Nat) : Hom → Hom × Bool
  | [] => ([], true)
  | a :: p =>
    let r := qdiv d a
    let t := hdiv d p
    (qtrim r.1 :: t.1, r.2 && t.2)

def hzero : Hom → Bool
  | [] => true
  | a :: p => sel (qzero a) (hzero p) false

def eadd : Ex → Ex → Ex
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => hadd a b :: eadd p q

def eneg : Ex → Ex
  | [] => []
  | a :: p => hneg a :: eneg p

/-- `a ⊛ B[j]` for the first `n` parts of `B` -/
def ehscal (a : Hom) : Nat → Ex → Ex
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: p => hmulR a c :: ehscal a n p

/-- the Cauchy product (scale `S²`), truncated to the parts of degree `< n` -/
def emulR : Nat → Ex → Ex → Ex
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | n + 1, a :: A, B => eadd (ehscal a (n + 1) B) ([] :: emulR n A B)

def ediv (d : Nat) : Ex → Ex × Bool
  | [] => ([], true)
  | a :: p =>
    let r := hdiv d a
    let t := ediv d p
    (r.1 :: t.1, r.2 && t.2)

def ezero : Ex → Bool
  | [] => true
  | a :: p => sel (hzero a) (ezero p) false

def eget : Ex → Nat → Hom
  | [], _ => []
  | a :: _, 0 => a
  | _ :: p, n + 1 => eget p n

/-- every part `E[d]` (`d ≥ k`) has at most `d + 1` entries -/
def wfE (k : Nat) : Ex → Bool
  | [] => true
  | a :: p => sel (Nat.ble a.length (k + 1)) (wfE (k + 1) p) false

/-! ## the series inverse and root (data only: nothing about them is proved) -/

/-- `Σ_{k=1}^{d} u[k] ⊛ Y[d-k]` -/
def convSum (u Y : Ex) (d : Nat) : Nat → Hom
  | 0 => []
  | k + 1 => hadd (hmulR (eget u (k + 1)) (eget Y (d - (k + 1)))) (convSum u Y d k)

/-- `Σ_{k=1}^{d-1} Y[k] ⊛ Y[d-k]` -/
def sqSum (Y : Ex) (d : Nat) : Nat → Hom
  | 0 => []
  | k + 1 =>
    sel (Nat.ble d (k + 1)) (sqSum Y d k)
      (hadd (hmulR (eget Y (k + 1)) (eget Y (d - (k + 1)))) (sqSum Y d k))

/-- `Y[d] = -(Σ_{k≥1} u[k] ⊛ Y[d-k]) / n0` for `u₀₀ = n0 / S` -/
def einvGo (u : Ex) (n0 : Int) : Nat → Nat → Ex → Ex
  | 0, _, Y => Y
  | n + 1, d, Y =>
    let r := (hdiv n0.natAbs (hneg (convSum u Y d d))).1
    einvGo u n0 n (d + 1) (Y ++ [sel (isNeg n0) (hneg r) r])

/-- `Y[d] = (S u[d] - Σ_{k=1}^{d-1} Y[k] ⊛ Y[d-k]) / (2 y0)` for `Y₀₀ = y0 / S` -/
def esqrtGo (u : Ex) (y0 : Nat) : Nat → Nat → Ex → Ex
  | 0, _, Y => Y
  | n + 1, d, Y =>
    let num := hadd (hscal [(S : Int)] (eget u d)) (hneg (sqSum Y d d))
    esqrtGo u y0 n (d + 1) (Y ++ [(hdiv (2 * y0) num).1])

/-! ## fixed point -/

/-- an offset `X` with `n / S ≤ val X` -/
def upS (n : Int) : Nat :=
  match n with
  | .ofNat k => Nat.add Bb (I.cdiv (Nat.shiftLeft k 96) S)
  | .negSucc k => Nat.sub Bb (Nat.div (Nat.shiftLeft (Nat.succ k) 96) S)

/-- an interval containing `[lo / S, hi / S]` -/
def ivS (lo hi : Int) : I := ⟨upS (-lo), upS hi⟩

/-- `acc + Σ_{k ≥ 1} (⌊|n_k| wm^k 2^(-s k)⌋ + 1)`, with `pw = wm^k`, `sh = s k` -/
def qtailS (wm s : Nat) : QP → Nat → Nat → Nat → Nat
  | [], _, _, acc => acc
  | a :: p, pw, sh, acc =>
    qtailS wm s p (Nat.mul pw wm) (sh + s)
      (acc + Nat.succ (Nat.shiftRight (Nat.mul a.natAbs pw) sh))

/-- an interval for `q(δ) / S` over `|δ| ≤ wm 2^-s` -/
def qrng (wm s : Nat) : QP → I
  | [] => I.zero
  | a :: p => let U : Int := qtailS wm s p wm s 0; ivS (a - U) (a + U)

/-- `|x| ≤ imag A · 2^-96` for `x ∈ A` -/
def imag (A : I) : Nat := Nat.sub (I.mx A.L A.H) Bb

/-- `⌈a b 2^-96⌉` -/
def mmul (a b : Nat) : Nat := Nat.shiftRight (Nat.add (Nat.mul a b) RND) 96

/-! ## the domain -/

structure Dom where
  /-- the order -/
  M : Nat
  /-- `w = wm 2^-s` -/
  wm : Nat
  s : Nat
  /-- `ρ = 2^-rb` -/
  rb : Nat

/-- `ρ^k 2^96`, rounded up -/
def rpow (D : Dom) (k : Nat) : Nat :=
  sel (Nat.ble (Nat.mul D.rb k) 96) (Nat.shiftLeft 1 (Nat.sub 96 (Nat.mul D.rb k))) 1

/-- an interval for `b^i g^n` on the box -/
def mono (D : Dom) (i n : Nat) : I :=
  let v := Nat.add Bb (rpow D (i + n))
  sel (Nat.beq (i + n) 0) I.one (sel (Nat.beq (n % 2) 1) ⟨v, v⟩ ⟨Bb, v⟩)

/-! ## Taylor forms -/

deriving instance DecidableEq for I

structure TF where
  E : Ex
  H : List I
  Hr : Nat
  ok : Bool
deriving Inhabited, DecidableEq

def hrng (D : Dom) : Hom → List I
  | [] => []
  | a :: p => qrng D.wm D.s a :: hrng D p

def erng (D : Dom) : Ex → List (List I)
  | [] => []
  | a :: p => hrng D a :: erng D p

def zeroH : Nat → List I
  | 0 => [I.zero]
  | n + 1 => I.zero :: zeroH n

def iadd : List I → List I → List I
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => a.add b :: iadd p q

def ineg : List I → List I
  | [] => []
  | a :: p => a.neg :: ineg p

def iscal (c : I) : List I → List I
  | [] => []
  | a :: p => c.mul a :: iscal c p

def imagSum : List I → Nat
  | [] => 0
  | a :: p => Nat.add (imag a) (imagSum p)

/-- `Σ_i R[i] · mono(i, d - i)` -/
def hRange (D : Dom) (d : Nat) : Nat → List I → I
  | _, [] => I.zero
  | i, r :: rs => (r.mul (mono D i (d - i))).add (hRange D d (i + 1) rs)

def eRange (D : Dom) : Nat → List (List I) → I
  | _, [] => I.zero
  | d, r :: rs => (hRange D d 0 r).add (eRange D (d + 1) rs)

/-- `Σ_p H_p · mono(p, M - p)` -/
def topRange (D : Dom) : Nat → List I → I
  | _, [] => I.zero
  | p, h :: hs => (h.mul (mono D p (D.M - p))).add (topRange D (p + 1) hs)

/-- an enclosure of `u` on the box -/
def TF.range (D : Dom) (u : TF) : I :=
  let hr := mmul u.Hr (rpow D (D.M + 1))
  let e := (eRange D 0 (erng D u.E)).add (topRange D 0 u.H)
  ⟨Nat.add e.L hr, Nat.add e.H hr⟩

/-- `Σ_i |R[i]|` for each degree -/
def kcomp : List (List I) → List Nat
  | [] => []
  | r :: rs => imagSum r :: kcomp rs

/-- `Σ_{d ≥ 1} KC[d] ρ^(d-1)`, a bound for `|P - P₀₀| / m` -/
def k1 (D : Dom) : Nat → List Nat → Nat
  | _, [] => 0
  | d, k :: ks => Nat.add (sel (Nat.beq d 0) 0 (mmul k (rpow D (d - 1)))) (k1 D (d + 1) ks)

/-- add `x` to the top in slot `p` -/
def addAt : Nat → I → List I → List I
  | _, _, [] => []
  | 0, x, h :: hs => h.add x :: hs
  | p + 1, x, h :: hs => h :: addAt p x hs

/-- the degree-`M` overflow of `R1[i1] ⊗ R2[i2]` (`d1 + d2 = M`), into slot `i1 + i2` -/
def ovInner (a : I) (i1 : Nat) : Nat → List I → List I → List I
  | _, [], H => H
  | i2, r :: rs, H => ovInner a i1 (i2 + 1) rs (addAt (i1 + i2) (a.mul r) H)

def ovOuter (r2 : List I) : Nat → List I → List I → List I
  | _, [], H => H
  | i1, a :: as, H => ovOuter r2 (i1 + 1) as (ovInner a i1 0 r2 H)

/-- per-slot overflow (`d1 + d2 = M`) and radial overflow magnitude (`d1 + d2 > M`) for the part
`d1` of the first factor against all parts of the second -/
def ovRow (D : Dom) (d1 : Nat) (r1 : List I) (k1v : Nat) :
    Nat → List (List I) → List Nat → List I × Nat → List I × Nat
  | _, [], _, acc => acc
  | _, _ :: _, [], acc => acc
  | d2, r2 :: rs, k2 :: ks, acc =>
    ovRow D d1 r1 k1v (d2 + 1) rs ks
      (sel (Nat.beq (d1 + d2) D.M) (ovOuter r2 0 r1 acc.1, acc.2)
        (sel (Nat.ble (D.M + 1) (d1 + d2))
          (acc.1, Nat.add acc.2 (mmul (mmul k1v k2) (rpow D (d1 + d2 - (D.M + 1))))) acc))

def ovAll (D : Dom) (R2 : List (List I)) (K2 : List Nat) :
    Nat → List (List I) → List Nat → List I × Nat → List I × Nat
  | _, [], _, acc => acc
  | _, _ :: _, [], acc => acc
  | d1, r1 :: rs, k1v :: ks, acc => ovAll D R2 K2 (d1 + 1) rs ks (ovRow D d1 r1 k1v 0 R2 K2 acc)

def rget : List I → Nat → I
  | [], _ => I.zero
  | a :: _, 0 => a
  | _ :: p, n + 1 => rget p n

def rrow : List (List I) → Nat → List I
  | [], _ => []
  | a :: _, 0 => a
  | _ :: p, n + 1 => rrow p n

/-- the shape conditions, folded into `ok` -/
def TF.shape (D : Dom) (E : Ex) (H : List I) : Bool :=
  sel (wfE 0 E) (Nat.beq H.length (D.M + 1)) false

def TF.mk' (D : Dom) (E : Ex) (H : List I) (Hr : Nat) (ok : Bool) : TF :=
  ⟨E, H, Hr, sel ok (TF.shape D E H) false⟩

def TF.add (D : Dom) (u v : TF) : TF :=
  TF.mk' D (eadd u.E v.E) (iadd u.H v.H) (Nat.add u.Hr v.Hr) (u.ok && v.ok)

def TF.neg (u : TF) : TF := ⟨eneg u.E, ineg u.H, u.Hr, u.ok⟩

def TF.sub (D : Dom) (u v : TF) : TF := TF.add D u v.neg

def TF.mul (D : Dom) (u v : TF) : TF :=
  let Eq := ediv S (emulR D.M u.E v.E)
  let R1 := erng D u.E
  let R2 := erng D v.E
  let K1 := kcomp R1
  let K2 := kcomp R2
  let ov := ovAll D R2 K2 0 R1 K1 (zeroH D.M, 0)
  let c1 := rget (rrow R1 0) 0
  let c2 := rget (rrow R2 0) 0
  let H := iadd ov.1 (iadd (iscal c1 v.H) (iscal c2 u.H))
  let hu := imagSum u.H
  let hv := imagSum v.H
  let Hr := Nat.add ov.2 (Nat.add (Nat.add (mmul (k1 D 0 K1) hv) (mmul (k1 D 0 K2) hu))
    (Nat.add (mmul (mmul hu hv) (rpow D (D.M - 1)))
      (Nat.add (mmul u.Hr (imag (TF.range D v))) (mmul v.Hr (imag (TF.range D u))))))
  TF.mk' D Eq.1 H Hr (u.ok && v.ok && Eq.2)

def TF.cst (D : Dom) (q : QP) : TF := ⟨[[q]], zeroH D.M, 0, true⟩
def TF.varB (D : Dom) : TF := ⟨[[], [[], [(S : Int)]]], zeroH D.M, 0, true⟩
def TF.varG (D : Dom) : TF := ⟨[[], [[(S : Int)], []]], zeroH D.M, 0, true⟩

/-- the constant coefficient of the exact part, if it does not depend on `δ` -/
def TF.c00 (u : TF) : Option Int :=
  match (eget u.E 0).headD [] with
  | [] => some 0
  | a :: p => sel (qzero p) (some a) none

/-- `Y + res · X`, for a residual `res` with vanishing exact part and an enclosure `X` -/
def finishRes (D : Dom) (Y : Ex) (res : TF) (X : Option I) : Option TF :=
  match X with
  | some x =>
    sel (ezero res.E) (some (TF.mk' D Y (iscal x res.H) (mmul res.Hr (imag x)) res.ok)) none
  | none => none

/-- the series inverse of `u` (data only) -/
def TF.invY (D : Dom) (u : TF) (n0 : Int) : Ex :=
  einvGo u.E n0 (D.M - 1) 1 [[[Int.ediv ((S : Int) * S) n0]]]

def TF.inv (D : Dom) (u : TF) : Option TF :=
  match u.c00 with
  | some n0 =>
    sel (n0 == 0) none
      (let Y := TF.invY D u n0
       finishRes D Y (TF.sub D (TF.cst D [(S : Int)]) (TF.mul D u (TF.mk' D Y (zeroH D.M) 0 true)))
         (u.range D).inv)
  | none => none

/-- the series root of `u` (data only) -/
def TF.sqrtY (D : Dom) (u : TF) (y0 : Nat) : Ex :=
  esqrtGo u.E y0 (D.M - 1) 1 [[[(y0 : Int)]]]

/-- the exact Taylor form of a polynomial (no tops) -/
def TF.ex (D : Dom) (Y : Ex) : TF := TF.mk' D Y (zeroH D.M) 0 true

/-- the root from `Y` and an enclosure of `√u` (if any) -/
def TF.sqrtFin (D : Dom) (Y : Ex) (u : TF) : Option I → Option TF
  | some su =>
    finishRes D Y (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y))) (su.add ((TF.ex D Y).range D)).inv
  | none => none

def TF.sqrtCore (D : Dom) (u : TF) (y0 : Nat) : Option TF :=
  TF.sqrtFin D (TF.sqrtY D u y0) u (u.range D).sqrt

def TF.sqrt (D : Dom) (u : TF) : Option TF :=
  match u.c00 with
  | some (.ofNat n0) => TF.sqrtCore D u (I.isq (Nat.mul n0 S))
  | _ => none

/-- Taylor-form arithmetic on the box `D` -/
@[instance_reducible] def tfOps (D : Dom) : Ops (Option TF) where
  add x y := match x, y with | some a, some b => some (TF.add D a b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (TF.sub D a b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (TF.mul D a b) | _, _ => none
  div x y := match x, y with
    | some a, some b => (TF.inv D b).map fun ib => TF.mul D a ib
    | _, _ => none
  neg x := match x with | some a => some a.neg | none => none
  sqrt x := match x with | some a => TF.sqrt D a | none => none
  sq x := match x with | some a => some (TF.mul D a a) | none => none
  ofInt n := some (TF.cst D [n * (S : Int)])

/-! ## the corner check for one `α`-box -/

/-- the data of one `α`-box: the box, the root polynomial `Ξ` (in `δ`), the multiplier
`1 + p b + q g`, the bound `λ`, the `ξ`-interval of the root and the localisation hint -/
structure Hint where
  M : Nat
  rb : Nat
  wm : Nat
  s : Nat
  ac : Int
  xi : Ex
  p : Int
  q : Int
  lam : Int
  xlo : Int
  xhi : Int
  loc : Nat

def Hint.dom (h : Hint) : Dom := ⟨h.M, h.wm, h.s, h.rb⟩

/-- `ρ S` and `w S` -/
def Hint.rhoS (h : Hint) : Int := Int.ediv (S : Int) (2 ^ h.rb)
def Hint.wS (h : Hint) : Int := Int.ediv ((h.wm : Int) * S) (2 ^ h.s)

/-- the 3-box `[0, ρ] × [α_c - w, α_c + w] × [1 - ρ, 1 + ρ]` of `(b, α, γ)` -/
def Hint.box (h : Hint) : Box :=
  ⟨ivS 0 h.rhoS, ivS (h.ac - h.wS) (h.ac + h.wS), ivS ((S : Int) - h.rhoS) ((S : Int) + h.rhoS)⟩

/-- the jet variable `i` on `X`, enclosing its value at every point of `X` -/
def jvR (X : I) (i : Nat) : J :=
  ⟨X, X, if i = 0 then I.one else I.zero, if i = 1 then I.one else I.zero,
    if i = 2 then I.one else I.zero, if i = 3 then I.one else I.zero⟩

/-- the width of `X` (offset) -/
def wid (X : I) : Nat := Nat.sub (Nat.add X.L X.H) B2

/-- every element of `A` is `> 0` -/
def posI (A : I) : Bool := Nat.blt A.L Bb

/-- `X ⊆ Y` -/
def within (X Y : I) : Bool := sel (Nat.ble X.L Y.L) (Nat.ble X.H Y.H) false

def allWithin (Y : I) : List I → Bool
  | [] => true
  | X :: Xs => sel (within X Y) (allWithin Y Xs) false

/-- every feasible zero of `P̂` in the box lies in `XB` -/
def locOK (B : Box) (XB : I) (h : Nat) : Bool :=
  ((xrange chMode B).bind fun X =>
    sel (I.isEmpty X) (some true) ((locH chMode B 4096 h [X] []).map fun r => allWithin XB r.1))
    == some true

/-- `Σ_{d=3}^{M-1} KC[d] ρ^(d-2)` -/
def lossE (D : Dom) : Nat → List Nat → Nat
  | _, [] => 0
  | d, k :: ks => Nat.add (sel (Nat.ble 3 d) (mmul k (rpow D (d - 2))) 0) (lossE D (d + 1) ks)

/-- the quadratic coefficients of `b²`, `b g`, `g²` (ranges) -/
def fA (D : Dom) (F : TF) : I := rget (rrow (erng D F.E) 2) 2
def fB (D : Dom) (F : TF) : I := rget (rrow (erng D F.E) 2) 1
def fC (D : Dom) (F : TF) : I := rget (rrow (erng D F.E) 2) 0

/-- `Σ_{d≥3} KC[d] ρ^(d-2) + (Σ |H_p|) ρ^(M-2) + Hr ρ^(M-1)` -/
def lossF (D : Dom) (F : TF) : Nat :=
  Nat.add (lossE D 0 (kcomp (erng D F.E)))
    (Nat.add (mmul (imagSum F.H) (rpow D (D.M - 2))) (mmul F.Hr (rpow D (D.M - 1))))

/-- `1/4` -/
def quarterI : I := ivS (Int.ediv (S : Int) 4) (Int.ediv (S : Int) 4)

/-- the positivity test: no constant or linear part, quadratic part `≥ λ (b² + g²)`, and `λ`
above the higher terms on the disc of radius `ρ` -/
def finalOK (D : Dom) (F : TF) (lam : Int) : Bool :=
  F.ok && hzero (eget F.E 0) && hzero (eget F.E 1) &&
    posI ((fA D F).sub (ivS lam lam)) && posI ((fC D F).sub (ivS lam lam)) &&
    posI ((((fA D F).sub (ivS lam lam)).mul ((fC D F).sub (ivS lam lam))).sub
      (((fB D F).sq).mul quarterI)) &&
    posI ((ivS lam lam).sub ⟨Nat.add Bb (lossF D F), Nat.add Bb (lossF D F)⟩)

/-- the multiplier `1 + p b + q g` -/
def TF.mult (D : Dom) (p q : Int) : TF :=
  TF.add D (TF.cst D [(S : Int)]) (TF.add D (TF.mul D (TF.cst D [p]) (TF.varB D))
    (TF.mul D (TF.cst D [q]) (TF.varG D)))

/-- the final tests, from the Taylor forms of `det` and `tr` -/
def midOf (h : Hint) : Option TF → Option TF → Bool
  | some det, some tr =>
    tr.ok && posI (tr.range h.dom) && posI ((TF.mult h.dom h.p h.q).range h.dom) &&
      finalOK h.dom (TF.mul h.dom det (TF.mult h.dom h.p h.q)) h.lam
  | _, _ => false

/-- the root `ξ* = Ξ - F/s` as a Taylor form, from the residual `F` and `iS ∋ 1/s` -/
def rootTF (h : Hint) (F : TF) (iS : I) : TF :=
  TF.mk' h.dom h.xi (iscal iS.neg F.H) (mmul F.Hr (imag iS.neg)) F.ok

/-- the radii of the 4-box `B × XB` for jets centred anywhere in it -/
abbrev radOf (B : Box) (XB : I) : Rad := ⟨wid B.X0, wid B.X1, wid B.X2, wid XB⟩

def slopeOf : Option J → Option I
  | some j => j.s3.inv
  | none => none

/-- the slope of `P̂` in `ξ` over the 4-box (`none` if it may vanish) -/
def slopeInv (B : Box) (XB : I) : Option I :=
  slopeOf (@chP _ (jetOps (radOf B XB)) (some (jvR B.X0 0)) (some (jvR B.X1 1))
    (some (jvR B.X2 2)) (some (jvR XB 3)))

/-- the exact Taylor form of the root polynomial -/
def Hint.xiTF (h : Hint) : TF := TF.mk' h.dom h.xi (zeroH h.M) 0 true

/-! ## the staged chart test

The let-chain of `chYIn` (`C4Check.Formulas2`) and the body of `midY`, cut into levels whose
composition is, by `rfl`, the original formula (`chYInS_eq`, `midYS_eq`).  A corner certificate
evaluates one level at a time on literal Taylor forms. -/

deriving instance DecidableEq for Six
deriving instance DecidableEq for YIn

section staged
variable {α : Type} [Ops α]

/-- level 1: the constraints, the squared distances and the simple products -/
@[ext] structure CL1 (α : Type) where
  h : Six α
  x : α
  a : α
  c : α
  R12 : α
  R14 : α
  R23 : α
  rho2 : α
  r13 : α
  R13 : α
  b4 : α
deriving DecidableEq

/-- level 2: the square roots and the products of level 1 -/
@[ext] structure CL2 (α : Type) where
  r12 : α
  r14 : α
  r23 : α
  rho : α
  r24 : α
  R24 : α
  k : α
  X2 : α
  X4 : α
  p : α
  px : α
deriving DecidableEq

/-- level 3: the weights -/
@[ext] structure CL3 (α : Type) where
  Dl13 : α
  Dl24 : α
  E14 : α
  E23 : α
  E34h : α
deriving DecidableEq

/-- level 4: their combinations -/
@[ext] structure CL4 (α : Type) where
  denh : α
  P12 : α
  D1 : α
  D2 : α
deriving DecidableEq

def cl1 (b al ga xi : α) : CL1 α :=
  let x := 1 / 2 + b * xi
  ⟨chG b al ga xi, x, 1 + b * al, b * ga, 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi)),
    1 + b * (ga * (b * ga + 2 * x)), 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b),
    1 - 2 * ga * x + Ops.sq ga, 1 + b, Ops.sq (1 + b), Ops.sq (Ops.sq b)⟩

def cl2 (ga : α) (s : CL1 α) : CL2 α :=
  ⟨Ops.sqrt s.R12, Ops.sqrt s.R14, Ops.sqrt s.R23, Ops.sqrt s.rho2, s.a + s.c, Ops.sq (s.a + s.c),
    s.r13 * (s.a + s.c), s.a * s.x, s.c * s.x, s.a * ga, s.a * ga * s.x⟩

def cl3 (b : α) (s : CL1 α) (t : CL2 α) : CL3 α :=
  ⟨s.h.x1 * hdr s.R12 t.r12 s.R13 s.r13, s.h.x2 * hdr s.R12 t.r12 t.R24 t.r24,
    t.r24 * s.h.x3 * hdr s.R14 t.r14 s.R12 t.r12, s.r13 * s.h.x4 * hdr s.R23 t.r23 s.R12 t.r12,
    1 / (s.rho2 * t.rho) - b * b * b / (s.R12 * t.r12)⟩

def cl4 (s : CL1 α) (u : CL3 α) : CL4 α :=
  ⟨u.E34h + s.b4 * (u.Dl13 + u.Dl24), u.Dl13 * u.Dl24, u.E34h + s.b4 * u.Dl13,
    u.E34h + s.b4 * u.Dl24⟩

def cl5 (b ga : α) (s : CL1 α) (t : CL2 α) (u : CL3 α) (v : CL4 α) : YIn α :=
  ⟨1 - Ops.sq s.x, -t.p, t.px, 1 - t.px * s.x, v.denh * Ops.sq (t.k * t.p),
    s.b4 * b * v.P12 * (ga * t.k) * (Ops.sq s.R12 * t.r12),
    u.Dl13 * v.D1 * t.R24 * (Ops.sq s.R13 * s.r13),
    (v.denh * u.E14 + s.b4 * v.P12) * (s.a * t.k) * (Ops.sq s.R14 * t.r14),
    (v.denh * u.E23 + s.b4 * v.P12) * (ga * t.k) * (Ops.sq s.R23 * t.r23),
    u.Dl24 * v.D2 * (s.a * ga * s.R13) * (Ops.sq t.R24 * t.r24),
    v.D1 * v.D2 * (s.a * t.k) * (Ops.sq s.rho2 * t.rho),
    1 + t.X2, 1 - b, 1 - t.X4, t.X2 - b, t.X2 - t.X4, -b - t.X4, s.a, 0, -s.c, s.a - s.c⟩

/-- `chYIn` by levels -/
def chYInS (b al ga xi : α) : YIn α :=
  cl5 b ga (cl1 b al ga xi) (cl2 ga (cl1 b al ga xi)) (cl3 b (cl1 b al ga xi) (cl2 ga (cl1 b al ga xi)))
    (cl4 (cl1 b al ga xi) (cl3 b (cl1 b al ga xi) (cl2 ga (cl1 b al ga xi))))

theorem chYInS_eq (b al ga xi : α) : chYInS b al ga xi = chYIn b al ga xi := rfl

/-- `chP`, level 1 -/
@[ext] structure PL1 (α : Type) where
  h : Six α
  x : α
  a : α
  c : α
  R12 : α
  R13 : α
  R14 : α
  R23 : α
  R24 : α
  rho2 : α
  b4 : α
deriving DecidableEq

/-- `chP`, level 2: the square roots -/
@[ext] structure PL2 (α : Type) where
  r12 : α
  r13 : α
  r14 : α
  r23 : α
  r24 : α
  rho : α
deriving DecidableEq

/-- `chP`, level 3: the weights -/
@[ext] structure PL3 (α : Type) where
  Dl13 : α
  Dl24 : α
  E14 : α
  E23 : α
  E34h : α
deriving DecidableEq

def pl1 (b al ga xi : α) : PL1 α :=
  let x := 1 / 2 + b * xi
  ⟨chG b al ga xi, x, 1 + b * al, b * ga, 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi)),
    1 + b * (2 + b), 1 + b * (ga * (b * ga + 2 * x)),
    1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b),
    1 + b * (2 * (al + ga) + b * Ops.sq (al + ga)), 1 - 2 * ga * x + Ops.sq ga, Ops.sq (Ops.sq b)⟩

def pl2 (s : PL1 α) : PL2 α :=
  ⟨Ops.sqrt s.R12, Ops.sqrt s.R13, Ops.sqrt s.R14, Ops.sqrt s.R23, Ops.sqrt s.R24, Ops.sqrt s.rho2⟩

def pl3 (b : α) (s : PL1 α) (t : PL2 α) : PL3 α :=
  ⟨s.h.x1 * hdr s.R12 t.r12 s.R13 t.r13, s.h.x2 * hdr s.R12 t.r12 s.R24 t.r24,
    (s.a + s.c) * s.h.x3 * hdr s.R14 t.r14 s.R12 t.r12, (1 + b) * s.h.x4 * hdr s.R23 t.r23 s.R12 t.r12,
    1 / (s.rho2 * t.rho) - b * b * b / (s.R12 * t.r12)⟩

def plF (s : PL1 α) (u : PL3 α) : α :=
  let denh := u.E34h + s.b4 * (u.Dl13 + u.Dl24)
  u.E14 * u.E23 * denh + u.Dl13 * u.Dl24 * (s.b4 * (u.E14 + u.E23) - u.E34h)

/-- `chP` by levels -/
def chPS (b al ga xi : α) : α :=
  plF (pl1 b al ga xi) (pl3 b (pl1 b al ga xi) (pl2 (pl1 b al ga xi)))

theorem chPS_eq (b al ga xi : α) : chPS b al ga xi = chP b al ga xi := rfl

/-- `midY`, level 1: the mean -/
@[ext] structure ML1 (α : Type) where
  iW : α
  mx : α
  me : α
deriving DecidableEq

/-- `midY`, level 2: the weighted moments of the edges -/
@[ext] structure ML2 (α : Type) where
  z12 : α × α × α
  z13 : α × α × α
  z14 : α × α × α
  z23 : α × α × α
  z24 : α × α × α
  z34 : α × α × α
  iF : α
deriving DecidableEq

def ml1 (A : YIn α) : ML1 α :=
  let iW := 1 / (A.d12 + A.d13 + A.d14 + A.d23 + A.d24 + A.d34)
  ⟨iW, (A.d12 * A.u12x + A.d13 * A.u13x + A.d14 * A.u14x + A.d23 * A.u23x + A.d24 * A.u24x +
      A.d34 * A.u34x) * iW,
    ((A.d12 + A.d23) * A.u12e + A.d13 * A.u13e + (A.d14 + A.d34) * A.u14e + A.d24 * A.u24e) * iW⟩

def ml2 (A : YIn α) (m : ML1 α) : ML2 α :=
  ⟨zz A.Axx A.Axe A.Aee A.d12 (A.u12x - m.mx) (A.u12e - m.me),
    zz A.Axx A.Axe A.Aee A.d13 (A.u13x - m.mx) (A.u13e - m.me),
    zz A.Axx A.Axe A.Aee A.d14 (A.u14x - m.mx) (A.u14e - m.me),
    zz A.Axx A.Axe A.Aee A.d23 (A.u23x - m.mx) (A.u12e - m.me),
    zz A.Axx A.Axe A.Aee A.d24 (A.u24x - m.mx) (A.u24e - m.me),
    zz A.Axx A.Axe A.Aee A.d34 (A.u34x - m.mx) (A.u14e - m.me), 1 / A.F⟩

def ml3 (A : YIn α) (n : ML2 α) : α × α :=
  let Yxx := 1 - (n.z12.1 + n.z13.1 + n.z14.1 + n.z23.1 + n.z24.1 + n.z34.1) * n.iF
  let Xxe := (n.z12.2.1 + n.z13.2.1 + n.z14.2.1 + n.z23.2.1 + n.z24.2.1 + n.z34.2.1) * n.iF
  let Yee := A.s2 - (n.z12.2.2 + n.z13.2.2 + n.z14.2.2 + n.z23.2.2 + n.z24.2.2 + n.z34.2.2) * n.iF
  (Yxx * Yee - Ops.sq Xxe, Yxx + Yee)

/-- `midY` by levels -/
def midYS (A : YIn α) : α × α := ml3 A (ml2 A (ml1 A))

theorem midYS_eq (A : YIn α) : midYS A = A.Y := rfl

end staged

/-! ## staged certificates of one `α`-box -/

/-- the literal data of a staged corner certificate -/
structure SHint where
  h : Hint
  P1 : PL1 (Option TF)
  P2 : PL2 (Option TF)
  P3 : PL3 (Option TF)
  F : TF
  iS : I
  L1 : CL1 (Option TF)
  L2 : CL2 (Option TF)
  L3 : CL3 (Option TF)
  L4 : CL4 (Option TF)
  Y : YIn (Option TF)
  M1 : ML1 (Option TF)
  M2 : ML2 (Option TF)
  det : TF
  tr : TF

namespace SHint
variable (s : SHint)

abbrev oB : Option TF := some (TF.varB s.h.dom)
abbrev oA : Option TF := some (TF.cst s.h.dom [s.h.ac, (S : Int)])
abbrev oG : Option TF := some (TF.add s.h.dom (TF.cst s.h.dom [(S : Int)]) (TF.varG s.h.dom))
abbrev oR : Option TF := some (rootTF s.h s.F s.iS)

/-- localisation, the root polynomial, the residual's shape and the slope -/
abbrev c0 : Prop :=
  (locOK s.h.box (ivS s.h.xlo s.h.xhi) s.h.loc && s.h.xiTF.ok &&
    within (s.h.xiTF.range s.h.dom) (ivS s.h.xlo s.h.xhi) && s.F.ok && ezero s.F.E) = true ∧
  slopeInv s.h.box (ivS s.h.xlo s.h.xhi) = some s.iS
abbrev oX : Option TF := some s.h.xiTF
/-- the residual `P̂(Ξ)`, by levels -/
abbrev cP1 : Prop := @pl1 _ (tfOps s.h.dom) s.oB s.oA s.oG s.oX = s.P1
abbrev cP2 : Prop := @pl2 _ (tfOps s.h.dom) s.P1 = s.P2
abbrev cP3 : Prop := @pl3 _ (tfOps s.h.dom) s.oB s.P1 s.P2 = s.P3
abbrev cP4 : Prop := @plF _ (tfOps s.h.dom) s.P1 s.P3 = some s.F
abbrev c1 : Prop := @cl1 _ (tfOps s.h.dom) s.oB s.oA s.oG s.oR = s.L1
abbrev c2 : Prop := @cl2 _ (tfOps s.h.dom) s.oG s.L1 = s.L2
abbrev c3 : Prop := @cl3 _ (tfOps s.h.dom) s.oB s.L1 s.L2 = s.L3
abbrev c4 : Prop := @cl4 _ (tfOps s.h.dom) s.L1 s.L3 = s.L4
abbrev c5 : Prop := @cl5 _ (tfOps s.h.dom) s.oB s.oG s.L1 s.L2 s.L3 s.L4 = s.Y
abbrev c6 : Prop := @ml1 _ (tfOps s.h.dom) s.Y = s.M1
abbrev c7 : Prop := @ml2 _ (tfOps s.h.dom) s.Y s.M1 = s.M2
abbrev c8 : Prop := @ml3 _ (tfOps s.h.dom) s.Y s.M2 = (some s.det, some s.tr)
/-- the final tests -/
abbrev c9 : Prop := midOf s.h (some s.det) (some s.tr) = true

end SHint

theorem six_ext {β : Type} {u v : Six β} (h1 : u.x1 = v.x1) (h2 : u.x2 = v.x2) (h3 : u.x3 = v.x3)
    (h4 : u.x4 = v.x4) (h5 : u.x5 = v.x5) (h6 : u.x6 = v.x6) : u = v := by
  cases u; cases v; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; rfl

theorem yin_ext {β : Type} {u v : YIn β} (h1 : u.s2 = v.s2) (h2 : u.Axx = v.Axx) (h3 : u.Axe = v.Axe)
    (h4 : u.Aee = v.Aee) (h5 : u.F = v.F) (h6 : u.d12 = v.d12) (h7 : u.d13 = v.d13)
    (h8 : u.d14 = v.d14) (h9 : u.d23 = v.d23) (h10 : u.d24 = v.d24) (h11 : u.d34 = v.d34)
    (h12 : u.u12x = v.u12x) (h13 : u.u13x = v.u13x) (h14 : u.u14x = v.u14x) (h15 : u.u23x = v.u23x)
    (h16 : u.u24x = v.u24x) (h17 : u.u34x = v.u34x) (h18 : u.u12e = v.u12e) (h19 : u.u13e = v.u13e)
    (h20 : u.u14e = v.u14e) (h21 : u.u24e = v.u24e) : u = v := by
  cases u; cases v
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9; cases h10
  cases h11; cases h12; cases h13; cases h14; cases h15; cases h16; cases h17; cases h18; cases h19
  cases h20; cases h21; rfl

/-- all certificate conditions of a staged box -/
structure SHint.Valid (s : SHint) : Prop where
  c0 : s.c0
  cP1 : s.cP1
  cP2 : s.cP2
  cP3 : s.cP3
  cP4 : s.cP4
  c1 : s.c1
  c2 : s.c2
  c3 : s.c3
  c4 : s.c4
  c5 : s.c5
  c6 : s.c6
  c7 : s.c7
  c8 : s.c8
  c9 : s.c9

theorem S_eq : S = 2 ^ 48 * 6561 := by decide

end CTF
end C4
