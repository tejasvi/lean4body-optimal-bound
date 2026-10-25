module

public import C4.Defs

@[expose] public section

/-!
# Shared pieces of the Taylor-form soundness proofs

Used by `C4/TFSound.lean` (the fixed-point models of the bulk) and `C4/CornerSound.lean` (the exact
corner forms).

* `inv_resid`, `sqrt_resid`: the residual identities behind `1/v` and `√v`.  Both engines form
  a polynomial `Y` (a truncated series, never proved), compute the residual `1 - vY` or `v - Y²`
  in model arithmetic, and enclose `(1 - vY)/v` or `(v - Y²)/(√v + Y)` by a range.
* `OpsSound P T Enc`: soundness of each operation of an `Ops (Option T)` instance for an
  enclosure predicate `Enc : (P → ℝ) → T → Prop`.
* `Carrier P T Enc` and `carrierOps h`: a real function, an optional checker value and a proof
  that the value (if any) encloses the function.  The operations are pointwise real arithmetic
  on the function (the operations of `opsReal`) and the checker's own operations on the value,
  so a generic formula evaluated at carriers yields, by `rfl`, both the checker's evaluation
  (`.o`) and the real formula (`.f`), together with the enclosure (`.ok`).
-/

namespace C4

noncomputable section

/-! ## the residual identities -/

/-- `1/v = Y + (1 - vY)/v` for every `Y` -/
theorem inv_resid {v : ℝ} (hv : v ≠ 0) (Y : ℝ) : v⁻¹ = Y + (1 - v * Y) * v⁻¹ := by
  field_simp
  ring

/-- `√v = Y + (v - Y²)/(√v + Y)` for every `Y` with `√v + Y ≠ 0` -/
theorem sqrt_resid {v : ℝ} (hv : 0 ≤ v) (Y : ℝ) (h : Real.sqrt v + Y ≠ 0) :
    Real.sqrt v = Y + (v - Y ^ 2) * (Real.sqrt v + Y)⁻¹ := by
  have hs : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  have e : v - Y ^ 2 = (Real.sqrt v - Y) * (Real.sqrt v + Y) := by linear_combination (-1 : ℝ) * hs
  rw [e, mul_assoc, mul_inv_cancel₀ h, mul_one]
  ring

/-! ## a generic carrier -/

/-- the optional checker value `o` (if any) encloses `f` -/
def OEncG {P T : Type} (Enc : (P → ℝ) → T → Prop) (f : P → ℝ) (o : Option T) : Prop :=
  ∀ t, o = some t → Enc f t

theorem OEncG.of_some {P T : Type} {Enc : (P → ℝ) → T → Prop} {f : P → ℝ} {t : T}
    (h : Enc f t) : OEncG Enc f (some t) := fun _ ht => by cases ht; exact h

theorem OEncG.none {P T : Type} {Enc : (P → ℝ) → T → Prop} {f : P → ℝ} :
    OEncG Enc f (none : Option T) := fun _ ht => by cases ht

/-- soundness of the operations of `Ops (Option T)` for the enclosure predicate `Enc` -/
structure OpsSound (P T : Type) [Ops (Option T)] (Enc : (P → ℝ) → T → Prop) : Prop where
  add : ∀ (f g : P → ℝ) (x y : Option T), OEncG Enc f x → OEncG Enc g y →
    OEncG Enc (fun z => f z + g z) (x + y)
  sub : ∀ (f g : P → ℝ) (x y : Option T), OEncG Enc f x → OEncG Enc g y →
    OEncG Enc (fun z => f z - g z) (x - y)
  mul : ∀ (f g : P → ℝ) (x y : Option T), OEncG Enc f x → OEncG Enc g y →
    OEncG Enc (fun z => f z * g z) (x * y)
  div : ∀ (f g : P → ℝ) (x y : Option T), OEncG Enc f x → OEncG Enc g y →
    OEncG Enc (fun z => f z / g z) (x / y)
  neg : ∀ (f : P → ℝ) (x : Option T), OEncG Enc f x → OEncG Enc (fun z => -f z) (-x)
  sqrt : ∀ (f : P → ℝ) (x : Option T), OEncG Enc f x →
    OEncG Enc (fun z => Real.sqrt (f z)) (Ops.sqrt x)
  sq : ∀ (f : P → ℝ) (x : Option T), OEncG Enc f x → OEncG Enc (fun z => f z ^ 2) (Ops.sq x)
  ofInt : ∀ n : ℤ, OEncG Enc (fun _ => (n : ℝ)) (Ops.ofInt n : Option T)

/-- a real function with an optional checker value that encloses it -/
structure Carrier (P T : Type) (Enc : (P → ℝ) → T → Prop) where
  f : P → ℝ
  o : Option T
  ok : OEncG Enc f o

/-- the carrier of `t`, given `Enc f t` -/
def Carrier.of {P T : Type} {Enc : (P → ℝ) → T → Prop} {f : P → ℝ} {t : T} (h : Enc f t) :
    Carrier P T Enc :=
  ⟨f, some t, OEncG.of_some h⟩

/-- carrier arithmetic: `opsReal` pointwise on the function, the checker's `Ops` on the value -/
@[instance_reducible] def carrierOps {P T : Type} [Ops (Option T)] {Enc : (P → ℝ) → T → Prop}
    (h : OpsSound P T Enc) : Ops (Carrier P T Enc) where
  add x y := ⟨fun z => x.f z + y.f z, x.o + y.o, h.add _ _ _ _ x.ok y.ok⟩
  sub x y := ⟨fun z => x.f z - y.f z, x.o - y.o, h.sub _ _ _ _ x.ok y.ok⟩
  mul x y := ⟨fun z => x.f z * y.f z, x.o * y.o, h.mul _ _ _ _ x.ok y.ok⟩
  div x y := ⟨fun z => x.f z / y.f z, x.o / y.o, h.div _ _ _ _ x.ok y.ok⟩
  neg x := ⟨fun z => -x.f z, -x.o, h.neg _ _ x.ok⟩
  sqrt x := ⟨fun z => Real.sqrt (x.f z), Ops.sqrt x.o, h.sqrt _ _ x.ok⟩
  sq x := ⟨fun z => x.f z ^ 2, Ops.sq x.o, h.sq _ _ x.ok⟩
  ofInt n := ⟨fun _ => (n : ℝ), Ops.ofInt n, h.ofInt n⟩

end

end C4
