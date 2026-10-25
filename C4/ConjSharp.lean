module

public import C4.NormalForm2
public import C4.Symmetry
public import C4.Cap2
public import C4.SharpCap
public import C4.Normalize
public import C4.NormalForm
public import C4.Dziobek

@[expose] public section

/-!
# Conjecture 7.3: `Q ≥ (2/3) K` at every strictly convex central configuration

The chain of the paper's proof of Theorem B, with the sharp majorant in place of the trace majorant:
normalize (`normalize`); Dziobek's relations with `σ < 0` (`dziobek_convex`); the region `𝒞`
(`inC_of_dziobek`); the midpoint test `T ≻ 0` from the certified caps, which cover only `a ≤ 1`
(`SharpCapT`), and from them at `ι p = (1/a, c/a, b/a, x)` when `a > 1` (`C4.Symmetry`); a family
`u` that represents `L` and has `S[w] < |w|² / 3` (`midpoint_test`); and `majorant_sharp` with
`λ = 1/3`.

* `SharpCapT`: the midpoint test `T ≻ 0` at every central configuration in normal form with
  `a ≤ 1`, in geometric terms.  `capT_of_capN` derives it from the certified caps `SharpCapN` of
  `C4.Cap2` (the normalized test `dirMidN`), through `nfN_Tform_pos`.
* `sharp_qd`: `Q ≥ (2/3) K`, strict where `K > 0`, at every central configuration in normal form.
* `conj_sharp_of_capT`, `conj_sharp_strict_of_capT`: Conjecture 7.3, from `SharpCapT`.
* `conj_sharp`, `conj_sharp_strict`: Conjecture 7.3, the theorems of `Challenge.lean`, from the
  certified caps `sharp_cap` of `C4.SharpCap`.
-/

namespace C4

noncomputable section

/-- the midpoint test `T ≻ 0` at every central configuration in normal form with `a ≤ 1` -/
def SharpCapT : Prop :=
  ∀ m : Masses, (∀ i, 0 < m i) → ∀ a b c x : ℝ, InC a b c x → a ≤ 1 →
    ∀ σ : ℝ, σ < 0 → DziobekRel m (qd a b c x) σ → ∀ u : V2, u ≠ 0 →
      0 < Tform (qd a b c x) (fun i j => Dgeo m (qd a b c x) i j * taugeo (qd a b c x) i j ^ 2) u

/-- the caps of the normalized checker give the midpoint test -/
theorem capT_of_capN (hcap : SharpCapN) : SharpCapT := by
  intro m hm a b c x hC ha1 σ hσ hD u hu
  obtain ⟨hP, -⟩ := normal_form m hm a b c x hC σ hσ hD
  obtain ⟨h1, h2⟩ := hcap a b c x hC hP ha1
  exact nfN_Tform_pos m hm a b c x hC σ hσ hD h1 h2 u hu

/-- the sharp bound at a central configuration in normal form with `a ≤ 1` -/
private theorem sharp_le1 (hcap : SharpCapT) (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ)
    (hC : InC a b c x) (ha1 : a ≤ 1) (σ : ℝ) (hσ : σ < 0) (hD : DziobekRel m (qd a b c x) σ) :
    (∀ v : Conf, 2 / 3 * hessK m (qd a b c x) v ≤ hessQ m (qd a b c x) v) ∧
      ∀ v : Conf, 0 < hessK m (qd a b c x) v →
        2 / 3 * hessK m (qd a b c x) v < hessQ m (qd a b c x) v := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  obtain ⟨hcf, hconv, -⟩ := qd_props a b c x ha hb hc hx1 hx2
  have hA := convex_area_ne _ hconv
  obtain ⟨u, hu, hS⟩ := midpoint_test m hm _ hcf σ hσ hD hA (hcap m hm a b c x hC ha1 σ hσ hD)
  have hS' : ∀ w : V2, Sform m (qd a b c x) u w ≤ 1 / 3 * dot w w := by
    intro w
    by_cases hw : w = 0
    · subst hw
      have hdot0 : ∀ y : V2, dot y 0 = 0 := fun y => by
        simp only [dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero]
      have h0 : Sform m (qd a b c x) u 0 = 0 := by
        simp only [Sform, esum, hdot0]
        ring
      rw [h0, hdot0, mul_zero]
    · exact (hS w hw).le
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have h := majorant_sharp m hm _ hcf σ hσ hD hA u hu (1 / 3) (by norm_num) hS' v
    linarith
  · have h := majorant_sharp_strict m hm _ hcf σ hσ hD hA u hu (1 / 3) (by norm_num) hS v hv
    linarith

/-- **The sharp bound in normal form.**  At every central configuration `qd a b c x` with
`(a, b, c, x) ∈ 𝒞`, `Q ≥ (2/3) K`, strictly where `K > 0`; for `a > 1` through `ι`. -/
theorem sharp_qd (hcap : SharpCapT) (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ)
    (hC : InC a b c x) (hcc : IsCC m (qd a b c x)) :
    (∀ v : Conf, 2 / 3 * hessK m (qd a b c x) v ≤ hessQ m (qd a b c x) v) ∧
      ∀ v : Conf, 0 < hessK m (qd a b c x) v →
        2 / 3 * hessK m (qd a b c x) v < hessQ m (qd a b c x) v := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  rcases le_or_gt a 1 with ha1 | ha1
  · obtain ⟨-, hconv, -⟩ := qd_props a b c x ha hb hc hx1 hx2
    obtain ⟨σ, hσ, hD⟩ := dziobek_convex m hm _ hcc hconv
    exact sharp_le1 hcap m hm a b c x hC ha1 σ hσ hD
  · -- the symmetry `ι`: certify at `(1/a, c/a, b/a, x)`, with the masses relabelled
    have hC' := inC_iota hC
    have hm' : ∀ i, 0 < (m ∘ iotaPerm) i := fun i => hm _
    have hcc' := isCC_iota hm ha hx1 hx2 hcc
    obtain ⟨ha', hb', hc', hx1', hx2', -⟩ := id hC'
    obtain ⟨-, hconv', -⟩ := qd_props (1 / a) (c / a) (b / a) x ha' hb' hc' hx1' hx2'
    obtain ⟨σ, hσ, hD⟩ := dziobek_convex _ hm' _ hcc' hconv'
    have ha1' : 1 / a ≤ 1 := by rw [div_le_one ha]; exact ha1.le
    obtain ⟨h1, h2⟩ := sharp_le1 hcap _ hm' _ _ _ _ hC' ha1' σ hσ hD
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · obtain ⟨v', hQ, hK⟩ := hess_iota m hm ha hx1 hx2 v
      have h := h1 v'
      rw [hQ, hK] at h
      have h3 : a * (2 / 3 * hessK m (qd a b c x) v) ≤ a * hessQ m (qd a b c x) v := by linarith
      exact le_of_mul_le_mul_left h3 ha
    · obtain ⟨v', hQ, hK⟩ := hess_iota m hm ha hx1 hx2 v
      have hv' : 0 < hessK (m ∘ iotaPerm) (qd (1 / a) (c / a) (b / a) x) v' := by
        rw [hK]; exact mul_pos ha hv
      have h := h2 v' hv'
      rw [hQ, hK] at h
      have h3 : a * (2 / 3 * hessK m (qd a b c x) v) < a * hessQ m (qd a b c x) v := by linarith
      exact lt_of_mul_lt_mul_left h3 ha.le

/-- **Conjecture 7.3**, from the midpoint test: `Q ≥ (2/3) K` at every strictly convex central
configuration of four positive masses. -/
theorem conj_sharp_of_capT (hcap : SharpCapT) (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf)
    (hcc : IsCC m q) (hconv : IsConvex q) (v : Conf) : 2 / 3 * hessK m q v ≤ hessQ m q v := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc', h14, h23, hv⟩ :=
    normalize m hm q hcc hconv
  obtain ⟨-, hconv', -⟩ := qd_props a b c x ha hb hc hx1 hx2
  obtain ⟨σ, hσ, hD⟩ := dziobek_convex m' hm' _ hcc' hconv'
  have hC := inC_of_dziobek m' hm' a b c x ha hb hc hx1 hx2 σ hσ hD h14 h23
  obtain ⟨v', hQ, hK⟩ := hv v
  have h := (sharp_qd hcap m' hm' a b c x hC hcc').1 v'
  rw [hQ, hK] at h
  have h2 : k * (2 / 3 * hessK m q v) ≤ k * hessQ m q v := by linarith
  exact le_of_mul_le_mul_left h2 hk

/-- **Conjecture 7.3, strict form**, from the midpoint test: `Q > (2/3) K` wherever `K > 0`. -/
theorem conj_sharp_strict_of_capT (hcap : SharpCapT) (m : Masses) (hm : ∀ i, 0 < m i)
    (q : Conf) (hcc : IsCC m q) (hconv : IsConvex q) (v : Conf) (hv0 : 0 < hessK m q v) :
    2 / 3 * hessK m q v < hessQ m q v := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc', h14, h23, hv⟩ :=
    normalize m hm q hcc hconv
  obtain ⟨-, hconv', -⟩ := qd_props a b c x ha hb hc hx1 hx2
  obtain ⟨σ, hσ, hD⟩ := dziobek_convex m' hm' _ hcc' hconv'
  have hC := inC_of_dziobek m' hm' a b c x ha hb hc hx1 hx2 σ hσ hD h14 h23
  obtain ⟨v', hQ, hK⟩ := hv v
  have hK' : 0 < hessK m' (qd a b c x) v' := by rw [hK]; exact mul_pos hk hv0
  have h := (sharp_qd hcap m' hm' a b c x hC hcc').2 v' hK'
  rw [hQ, hK] at h
  have h2 : k * (2 / 3 * hessK m q v) < k * hessQ m q v := by linarith
  exact lt_of_mul_lt_mul_left h2 hk.le

/-! ## The theorems of `Challenge.lean` -/

/-- **Conjecture 7.3.**  At every strictly convex central configuration `q` of four positive
masses `m`, `Q_q(v) ≥ (2/3) K_q(v)` for every variation `v`. -/
theorem conj_sharp (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) : 2 / 3 * hessK m q v ≤ hessQ m q v :=
  conj_sharp_of_capT (capT_of_capN sharp_cap) m hm q hcc hconv v

/-- **Conjecture 7.3, strict form**, equivalent to `λ_max(G) < 1/3`: the inequality is strict for
every `v` with `K_q(v) > 0`. -/
theorem conj_sharp_strict (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) (hv : 0 < hessK m q v) :
    2 / 3 * hessK m q v < hessQ m q v :=
  conj_sharp_strict_of_capT (capT_of_capN sharp_cap) m hm q hcc hconv v hv

end

end C4
