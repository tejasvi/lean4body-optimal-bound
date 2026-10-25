module

public import C4.Defs

@[expose] public section

/-!
# The symmetry `ι : (a, b, c, x) ↦ (1/a, c/a, b/a, x)`

`qd (1/a) (c/a) (b/a) x` is the image of `qd a b c x` under the relabelling `(1 2)(3 4)` of the
paper (`iotaPerm`: bodies `0 ↔ 1`, `2 ↔ 3` here), followed by the orientation-reversing similarity
`z ↦ R z / a` with `R = [[x, s], [s, -x]]`, `s = √(1 - x²)`.  Hence:
* `isCC_iota`: central configurations go to central configurations, with the masses relabelled;
* `inC_iota`: `ι` maps `𝒞` into `𝒞` (`g₁ ↔ g₂ / a²`, `g₃ ↔ g₄ / a`, `g₅ ↔ g₆ / a`);
* `hess_iota`: `Q` and `K` are multiplied by the same factor `a > 0`.
So the certificates need cover only `a ≤ 1`.

The helper lemmas `sy_*` are copies of the private relabelling and similarity lemmas of
`C4.Normalize`, which is kept verbatim.
-/

namespace C4

noncomputable section


private lemma sy_Rs_symm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma sy_rr_symm (q : Conf) (i j : Fin 4) : rr q i j = rr q j i := by
  unfold rr; rw [sy_Rs_symm]

private lemma sy_ss_symm (q : Conf) (i j : Fin 4) : ss q i j = ss q j i := by
  unfold ss; rw [sy_Rs_symm, sy_rr_symm]

private lemma sy_dr_symm (q v : Conf) (i j : Fin 4) : dr q v i j = dr q v j i := by
  unfold dr; rw [sy_rr_symm]; congr 1; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma sy_mtot_eq (m : Masses) : mtot m = ∑ i, m i := by
  simp [mtot, Fin.sum_univ_four]


/-! ## relabeling the bodies -/

/-- `esum g = ½ Σ_{i ≠ j} g i j` for symmetric `g` -/
private lemma sy_esum_half (g : Fin 4 → Fin 4 → ℝ) (hg : ∀ i j, g i j = g j i) :
    esum g = (∑ i, ∑ j, if i = j then 0 else g i j) / 2 := by
  simp only [esum, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) = 1) = False by decide, show ((0 : Fin 4) = 2) = False by decide,
    show ((0 : Fin 4) = 3) = False by decide, show ((1 : Fin 4) = 0) = False by decide,
    show ((1 : Fin 4) = 2) = False by decide, show ((1 : Fin 4) = 3) = False by decide,
    show ((2 : Fin 4) = 0) = False by decide, show ((2 : Fin 4) = 1) = False by decide,
    show ((2 : Fin 4) = 3) = False by decide, show ((3 : Fin 4) = 0) = False by decide,
    show ((3 : Fin 4) = 1) = False by decide, show ((3 : Fin 4) = 2) = False by decide,
    ite_false, ite_true]
  rw [hg 1 0, hg 2 0, hg 3 0, hg 2 1, hg 3 1, hg 3 2]; ring

private lemma sy_esum_perm (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Fin 4 → ℝ)
    (hf : ∀ i j, f i j = f j i) : esum (fun i j => f (σ i) (σ j)) = esum f := by
  rw [sy_esum_half _ (fun i j => hf _ _), sy_esum_half f hf]
  congr 1
  have h : ∀ i j, (if i = j then (0 : ℝ) else f (σ i) (σ j)) =
      (fun a b => if a = b then (0 : ℝ) else f a b) (σ i) (σ j) := by
    intro i j; simp [σ.injective.eq_iff]
  simp_rw [h]
  rw [Equiv.sum_comp σ (fun a => ∑ j, (fun a b => if a = b then (0 : ℝ) else f a b) a (σ j))]
  congr 1; ext a
  exact Equiv.sum_comp σ (fun b => if a = b then (0 : ℝ) else f a b)

private lemma sy_mtot_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) : mtot (m ∘ σ) = mtot m := by
  rw [sy_mtot_eq, sy_mtot_eq]; exact Equiv.sum_comp σ m

private lemma sy_cm_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    cm (m ∘ σ) (q ∘ σ) = cm m q := by
  unfold cm; rw [sy_mtot_perm]; congr 1; exact Equiv.sum_comp σ (fun i => m i • q i)

private lemma sy_Iner_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    Iner (m ∘ σ) (q ∘ σ) = Iner m q := by
  unfold Iner; rw [sy_cm_perm]
  exact Equiv.sum_comp σ (fun i => m i * dot (q i - cm m q) (q i - cm m q))

private lemma sy_Upot_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    Upot (m ∘ σ) (q ∘ σ) = Upot m q := by
  unfold Upot
  exact sy_esum_perm σ (fun i j => m i * m j / rr q i j) (fun i j => by rw [sy_rr_symm]; ring)

private lemma sy_lamC_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    lamC (m ∘ σ) (q ∘ σ) = lamC m q := by
  unfold lamC; rw [sy_Upot_perm, sy_Iner_perm]

private lemma sy_hessK_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q v : Conf) :
    hessK (m ∘ σ) (q ∘ σ) (v ∘ σ) = hessK m q v := by
  unfold hessK
  exact sy_esum_perm σ (fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2)
    (fun i j => by rw [sy_ss_symm, sy_dr_symm]; ring)

private lemma sy_hessQ_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q v : Conf) :
    hessQ (m ∘ σ) (q ∘ σ) (v ∘ σ) = hessQ m q v := by
  unfold hessQ
  rw [sy_hessK_perm]
  simp only [wgeo, sy_lamC_perm, sy_mtot_perm]
  congr 1
  exact sy_esum_perm σ
    (fun i j => m i * m j * (ss q i j - lamC m q / mtot m) * dot (v i - v j) (v i - v j))
    (fun i j => by
      rw [sy_ss_symm]
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring)

private lemma sy_isCC_perm (σ : Equiv.Perm (Fin 4)) {m : Masses} {q : Conf} (h : IsCC m q) :
    IsCC (m ∘ σ) (q ∘ σ) := by
  obtain ⟨hcf, lam, hlam⟩ := h
  refine ⟨fun i j hij => hcf (σ i) (σ j) (σ.injective.ne hij), lam, fun i => ?_⟩
  rw [sy_cm_perm]
  have := hlam (σ i)
  rw [← Equiv.sum_comp σ (fun j => (m (σ i) * m j * ss q (σ i) j) • (q j - q (σ i)))] at this
  exact this

/-! ## similarities of the plane -/


/-- the linear part `(u₁, u₂) ↦ (A u₁ - e B u₂, B u₁ + e A u₂)`; conformal when `e² = 1` -/
private def sy_L (A B e : ℝ) : V2 →ₗ[ℝ] V2 where
  toFun u := (A * u.1 - e * B * u.2, B * u.1 + e * A * u.2)
  map_add' u w := by
    ext <;> simp <;> ring
  map_smul' c u := by
    ext <;> simp <;> ring

private lemma sy_L_apply (A B e : ℝ) (u : V2) :
    sy_L A B e u = (A * u.1 - e * B * u.2, B * u.1 + e * A * u.2) := rfl

private lemma sy_dot_L {A B e : ℝ} (he : e ^ 2 = 1) (u w : V2) :
    dot (sy_L A B e u) (sy_L A B e w) = (A ^ 2 + B ^ 2) * dot u w := by
  simp only [sy_L_apply, dot]
  linear_combination (A ^ 2 + B ^ 2) * u.2 * w.2 * he

/-- the similarity `z ↦ L (z - p)` applied to a configuration -/
private def sy_simC (A B e : ℝ) (p : V2) (q : Conf) : Conf := fun i => sy_L A B e (q i - p)

private lemma sy_simC_sub (A B e : ℝ) (p : V2) (q : Conf) (i j : Fin 4) :
    sy_simC A B e p q i - sy_simC A B e p q j = sy_L A B e (q i - q j) := by
  simp only [sy_simC, ← map_sub, sub_sub_sub_cancel_right]

private lemma sy_cm_simC (A B e : ℝ) (p : V2) {m : Masses} (hM : mtot m ≠ 0) (q : Conf) :
    cm m (sy_simC A B e p q) = sy_L A B e (cm m q - p) := by
  have h1 : ∑ i, m i • (q i - p) = ∑ i, m i • q i - (mtot m) • p := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sy_mtot_eq]
  have h2 : ∑ i, m i • sy_simC A B e p q i = sy_L A B e (∑ i, m i • (q i - p)) := by
    rw [map_sum]; simp only [map_smul, sy_simC]
  unfold cm
  rw [h2, ← map_smul, h1, smul_sub, smul_smul, inv_mul_cancel₀ hM, one_smul]

private lemma sy_simC_sub_cm (A B e : ℝ) (p : V2) {m : Masses} (hM : mtot m ≠ 0) (q : Conf)
    (i : Fin 4) : sy_simC A B e p q i - cm m (sy_simC A B e p q) = sy_L A B e (q i - cm m q) := by
  rw [sy_cm_simC A B e p hM]; simp only [sy_simC, ← map_sub, sub_sub_sub_cancel_right]

private lemma sy_dot_self_eq_zero {u : V2} (h : dot u u = 0) : u = 0 := by
  unfold dot at h
  have h1 : u.1 * u.1 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
  have h2 : u.2 * u.2 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

section sim

variable {A B e s : ℝ} (p : V2)

private lemma sy_Rs_simC (he : e ^ 2 = 1) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf) (i j : Fin 4) :
    Rs (sy_simC A B e p q) i j = s ^ 2 * Rs q i j := by
  unfold Rs; rw [sy_simC_sub, sy_dot_L he, hN]

private lemma sy_rr_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf)
    (i j : Fin 4) : rr (sy_simC A B e p q) i j = s * rr q i j := by
  unfold rr; rw [sy_Rs_simC p he hN, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]

private lemma sy_ss_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf)
    (i j : Fin 4) : ss (sy_simC A B e p q) i j = ss q i j / s ^ 3 := by
  unfold ss; rw [sy_Rs_simC p he hN, sy_rr_simC p he hs hN]; ring

private lemma sy_Iner_simC (he : e ^ 2 = 1) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) : Iner m (sy_simC A B e p q) = s ^ 2 * Iner m q := by
  unfold Iner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sy_simC_sub_cm A B e p hM, sy_dot_L he, hN]; ring

private lemma sy_Upot_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (m : Masses)
    (q : Conf) : Upot m (sy_simC A B e p q) = Upot m q / s := by
  simp only [Upot, esum, sy_rr_simC p he hs hN]; ring

private lemma sy_lamC_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) : lamC m (sy_simC A B e p q) = lamC m q / s ^ 3 := by
  unfold lamC; rw [sy_Upot_simC p he hs hN, sy_Iner_simC p he hN hM]; ring

private lemma sy_wgeo_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) (i j : Fin 4) :
    wgeo m (sy_simC A B e p q) i j = wgeo m q i j / s ^ 3 := by
  unfold wgeo; rw [sy_ss_simC p he hs hN, sy_lamC_simC p he hs hN hM]; ring

private lemma sy_dr_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q v : Conf)
    (i j : Fin 4) : dr (sy_simC A B e p q) (fun k => sy_L A B e (v k)) i j = s * dr q v i j := by
  unfold dr
  rw [sy_simC_sub, ← map_sub, sy_dot_L he, hN, sy_rr_simC p he hs hN]
  have : s ≠ 0 := hs.ne'
  rcases eq_or_ne (rr q i j) 0 with h | h
  · simp [h]
  · field_simp

/-- `K` scales by `1/s` (with `v' = L v`) -/
private lemma sy_hessK_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (m : Masses)
    (q v : Conf) : hessK m (sy_simC A B e p q) (fun k => sy_L A B e (v k)) = hessK m q v / s := by
  simp only [hessK, esum, sy_ss_simC p he hs hN, sy_dr_simC p he hs hN]
  have : s ≠ 0 := hs.ne'
  field_simp

/-- `Q` scales by `1/s` (with `v' = L v`) -/
private lemma sy_hessQ_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q v : Conf) :
    hessQ m (sy_simC A B e p q) (fun k => sy_L A B e (v k)) = hessQ m q v / s := by
  unfold hessQ
  rw [sy_hessK_simC p he hs hN]
  simp only [esum, sy_wgeo_simC p he hs hN hM, ← map_sub, sy_dot_L he, hN]
  have : s ≠ 0 := hs.ne'
  field_simp

/-- a similarity maps central configurations to central configurations (`λ ↦ λ / s³`) -/
private lemma sy_isCC_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) {q : Conf} (h : IsCC m q) : IsCC m (sy_simC A B e p q) := by
  obtain ⟨hcf, lam, hlam⟩ := h
  refine ⟨fun i j hij heq => hcf i j hij ?_, lam / s ^ 3, fun i => ?_⟩
  · have h0 : sy_L A B e (q i - q j) = 0 := by rw [← sy_simC_sub, heq, sub_self]
    have h1 : s ^ 2 * dot (q i - q j) (q i - q j) = 0 := by
      rw [← hN, ← sy_dot_L he, h0]; simp [dot]
    have h2 : dot (q i - q j) (q i - q j) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (by positivity)
      · exact h
    exact sub_eq_zero.mp (sy_dot_self_eq_zero h2)
  · have key : (∑ j, (m i * m j * ss (sy_simC A B e p q) i j) • (sy_simC A B e p q j - sy_simC A B e
      p q i))
        + (lam / s ^ 3 * m i) • (sy_simC A B e p q i - cm m (sy_simC A B e p q))
        = sy_L A B e ((s ^ 3)⁻¹ • ((∑ j, (m i * m j * ss q i j) • (q j - q i))
            + (lam * m i) • (q i - cm m q))) := by
      rw [map_smul, map_add, map_sum, smul_add, Finset.smul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_smul, sy_ss_simC p he hs hN, sy_simC_sub]
        congr 1; ring
      · rw [map_smul, smul_smul, sy_simC_sub_cm A B e p hM]
        congr 1; ring
    rw [key, hlam i, smul_zero, map_zero]

end sim

/-! ## oriented areas -/

/-! ## the symmetry -/

/-- the relabelling `(1 2)(3 4)` of the paper: bodies `0 ↔ 1`, `2 ↔ 3` -/
def iotaPerm : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

private lemma sy_qd0 (a b c x : ℝ) : qd a b c x 0 = (1, 0) := rfl
private lemma sy_qd1 (a b c x : ℝ) : qd a b c x 1 = (a * x, a * Real.sqrt (1 - x ^ 2)) := rfl
private lemma sy_qd2 (a b c x : ℝ) : qd a b c x 2 = (-b, 0) := rfl
private lemma sy_qd3 (a b c x : ℝ) :
    qd a b c x 3 = (-(c * x), -(c * Real.sqrt (1 - x ^ 2))) := rfl

private lemma sy_p0 : iotaPerm 0 = 1 := rfl
private lemma sy_p1 : iotaPerm 1 = 0 := rfl
private lemma sy_p2 : iotaPerm 2 = 3 := rfl
private lemma sy_p3 : iotaPerm 3 = 2 := rfl

/-- `qd (ι p)` is the relabelled `qd p` under the similarity `z ↦ R z / a` -/
private lemma sy_qd_iota {a b c x : ℝ} (ha : 0 < a) (hx1 : -1 < x) (hx2 : x < 1) :
    qd (1 / a) (c / a) (b / a) x =
      sy_simC (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) 0 (qd a b c x ∘ iotaPerm) := by
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha0 : a ≠ 0 := ha.ne'
  have h0 : qd (1 / a) (c / a) (b / a) x 0 =
      sy_simC (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) 0 (qd a b c x ∘ iotaPerm) 0 := by
    simp only [sy_simC, sy_L_apply, Function.comp, sub_zero, sy_qd0, sy_qd1, sy_p0]
    refine Prod.ext ?_ ?_
    · field_simp
      linear_combination -hs2
    · field_simp
      ring
  have h1 : qd (1 / a) (c / a) (b / a) x 1 =
      sy_simC (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) 0 (qd a b c x ∘ iotaPerm) 1 := by
    simp only [sy_simC, sy_L_apply, Function.comp, sub_zero, sy_qd0, sy_qd1, sy_p1]
    refine Prod.ext ?_ ?_ <;> field_simp <;> ring
  have h2 : qd (1 / a) (c / a) (b / a) x 2 =
      sy_simC (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) 0 (qd a b c x ∘ iotaPerm) 2 := by
    simp only [sy_simC, sy_L_apply, Function.comp, sub_zero, sy_qd2, sy_qd3, sy_p2]
    refine Prod.ext ?_ ?_
    · field_simp
      linear_combination c * hs2
    · field_simp
      ring
  have h3 : qd (1 / a) (c / a) (b / a) x 3 =
      sy_simC (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) 0 (qd a b c x ∘ iotaPerm) 3 := by
    simp only [sy_simC, sy_L_apply, Function.comp, sub_zero, sy_qd2, sy_qd3, sy_p3]
    refine Prod.ext ?_ ?_ <;> field_simp <;> ring
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

private lemma sy_norm {a x : ℝ} (ha : 0 < a) (hx1 : -1 < x) (hx2 : x < 1) :
    (x / a) ^ 2 + (Real.sqrt (1 - x ^ 2) / a) ^ 2 = (1 / a) ^ 2 := by
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  linear_combination hs2

private lemma sy_mtot_ne {m : Masses} (hm : ∀ i, 0 < m i) : mtot (m ∘ iotaPerm) ≠ 0 := by
  have := hm (iotaPerm 0); have := hm (iotaPerm 1); have := hm (iotaPerm 2)
  have := hm (iotaPerm 3)
  unfold mtot
  simp only [Function.comp]
  positivity

/-- `ι` maps central configurations to central configurations, with the masses relabelled -/
theorem isCC_iota {m : Masses} (hm : ∀ i, 0 < m i) {a b c x : ℝ} (ha : 0 < a) (hx1 : -1 < x)
    (hx2 : x < 1) (h : IsCC m (qd a b c x)) :
    IsCC (m ∘ iotaPerm) (qd (1 / a) (c / a) (b / a) x) := by
  rw [sy_qd_iota ha hx1 hx2]
  exact sy_isCC_simC 0 (by norm_num) (by positivity) (sy_norm ha hx1 hx2) (sy_mtot_ne hm)
    (sy_isCC_perm iotaPerm h)

/-- `ι` multiplies `Q` and `K` by the same factor `a` -/
theorem hess_iota (m : Masses) (hm : ∀ i, 0 < m i) {a b c x : ℝ} (ha : 0 < a) (hx1 : -1 < x)
    (hx2 : x < 1) (v : Conf) :
    ∃ v' : Conf, hessQ (m ∘ iotaPerm) (qd (1 / a) (c / a) (b / a) x) v' =
        a * hessQ m (qd a b c x) v ∧
      hessK (m ∘ iotaPerm) (qd (1 / a) (c / a) (b / a) x) v' = a * hessK m (qd a b c x) v := by
  have ha0 : a ≠ 0 := ha.ne'
  refine ⟨fun k => sy_L (x / a) (Real.sqrt (1 - x ^ 2) / a) (-1) ((v ∘ iotaPerm) k), ?_, ?_⟩
  · rw [sy_qd_iota ha hx1 hx2, sy_hessQ_simC 0 (by norm_num) (by positivity)
      (sy_norm ha hx1 hx2) (sy_mtot_ne hm), sy_hessQ_perm]
    field_simp
  · rw [sy_qd_iota ha hx1 hx2, sy_hessK_simC 0 (by norm_num) (by positivity)
      (sy_norm ha hx1 hx2), sy_hessK_perm]
    field_simp

/-- `ι` maps `𝒞` into `𝒞`: `g₁ ↔ g₂ / a²`, `g₃ ↔ g₄ / a`, `g₅ ↔ g₆ / a` -/
theorem inC_iota {a b c x : ℝ} (h : InC a b c x) : InC (1 / a) (c / a) (b / a) x := by
  obtain ⟨ha, hb, hc, hx1, hx2, g1, g2, g3, g4, g5, g6⟩ := h
  have ht := mul_one_div_cancel ha.ne'
  have e1 : (dirGR (1 / a) (c / a) (b / a) x).x1 = (dirGR a b c x).x2 * (1 / a) ^ 2 := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div c a]
    generalize 1 / a = t at ht ⊢
    linear_combination (-(2 * c * t + 2 * x * t)) * ht
  have e2 : (dirGR (1 / a) (c / a) (b / a) x).x2 = (dirGR a b c x).x1 * (1 / a) ^ 2 := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div b a]
    generalize 1 / a = t at ht ⊢
    linear_combination (a * t + 1 - 2 * x * t) * ht
  have e3 : (dirGR (1 / a) (c / a) (b / a) x).x3 = (dirGR a b c x).x4 * (1 / a) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div b a]
    generalize 1 / a = t at ht ⊢
    linear_combination (2 * x) * ht
  have e4 : (dirGR (1 / a) (c / a) (b / a) x).x4 = (dirGR a b c x).x3 * (1 / a) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div c a]
    generalize 1 / a = t at ht ⊢
    linear_combination (-1) * ht
  have e5 : (dirGR (1 / a) (c / a) (b / a) x).x5 = (dirGR a b c x).x6 * (1 / a) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div c a, div_eq_mul_one_div b a]
    generalize 1 / a = t at ht ⊢
    linear_combination (0) * ht
  have e6 : (dirGR (1 / a) (c / a) (b / a) x).x6 = (dirGR a b c x).x5 * (1 / a) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]
    push_cast
    simp only [div_eq_mul_one_div c a, div_eq_mul_one_div b a]
    generalize 1 / a = t at ht ⊢
    linear_combination (-1) * ht
  have hi : 0 < 1 / a := by positivity
  exact ⟨hi, by positivity, by positivity, hx1, hx2,
    by rw [e1]; exact mul_pos g2 (by positivity), by rw [e2]; exact mul_pos g1 (by positivity),
    by rw [e3]; exact mul_nonneg g4 hi.le, by rw [e4]; exact mul_nonneg g3 hi.le,
    by rw [e5]; exact mul_nonneg g6 hi.le, by rw [e6]; exact mul_nonneg g5 hi.le⟩

end

end C4
