module

public import C4.MajorantSharp

@[expose] public section

/-!
# The midpoint test

Let `M₂ = Σ_l A_l q_l q_lᵀ`, `n_e = q_i + q_j` (twice the midpoint of the edge `e = ij`) and
`ω_e = A_i A_j ⟨q_i - q_j, v_i - v_j⟩`.

* `M2_star`: `Σ_e ω_e n_e = -M₂ L(v)` for every `q` and `v`, a polynomial identity; also
  `Σ_e ω_e = 0` (`A_i A_j` is a self-stress, `omg_selfstress`) and `det M₂ = -4 A₁ A₂ A₃ A₄`
  (`M2det_eq`).
* `midpoint_rep`: hence, for every `z`, the family `u_e = τ_e M₂⁻¹ (z - n_e)` represents `L`:
  `L(v) = Σ_e ṙ_e(v) u_e`, because `ṙ_e τ_e = ω_e`.  (Since `β_e + τ_e y` represents `L` too, this
  is the midpoint identity `β_e / τ_e = -2 M₂⁻¹ m_e + c`; it is not needed below.)
* `midpoint_test`: with `d_e = D_e τ_e²`, `W = Σ_e d_e`, `t = Σ_e d_e n_e` and `z = t / W`, and
  `T[u] = W |M₂ u|² - 3 (W Σ_e d_e ⟨n_e, u⟩² - ⟨t, u⟩²)` (`Tform`), one has
  `W (|w|² - 3 S[w]) = T[M₂⁻¹ w]`.  So if `T ≻ 0`, then `S[w] < |w|² / 3` for every `w ≠ 0`.
  (`T` is the matrix `W M₂² - 12 (W Σ_e d_e m_e m_eᵀ - t' t'ᵀ)`, `t' = t / 2`.)
-/

namespace C4

noncomputable section

/-! ## `M₂ = Σ_l A_l q_l q_lᵀ` -/

/-- the entry `(1,1)` of `M₂ = Σ_l A_l q_l q_lᵀ` -/
def M2a (q : Conf) : ℝ := ∑ l, area q l * (q l).1 ^ 2

/-- the entry `(1,2)` of `M₂` -/
def M2b (q : Conf) : ℝ := ∑ l, area q l * ((q l).1 * (q l).2)

/-- the entry `(2,2)` of `M₂` -/
def M2c (q : Conf) : ℝ := ∑ l, area q l * (q l).2 ^ 2

/-- `M₂ u` -/
def M2mul (q : Conf) (u : V2) : V2 := (M2a q * u.1 + M2b q * u.2, M2b q * u.1 + M2c q * u.2)

/-- `det M₂` -/
def M2det (q : Conf) : ℝ := M2a q * M2c q - M2b q ^ 2

/-- `M₂⁻¹ w` -/
def M2inv (q : Conf) (w : V2) : V2 :=
  ((M2c q * w.1 - M2b q * w.2) / M2det q, (M2a q * w.2 - M2b q * w.1) / M2det q)

private lemma mp_area0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
private lemma mp_area1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
private lemma mp_area2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
private lemma mp_area3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

/-- `det M₂ = -4 A₁ A₂ A₃ A₄` -/
theorem M2det_eq (q : Conf) :
    M2det q = -4 * (area q 0 * area q 1 * area q 2 * area q 3) := by
  simp only [M2det, M2a, M2b, M2c, Fin.sum_univ_four, mp_area0, mp_area1, mp_area2, mp_area3,
    tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

theorem M2det_ne (q : Conf) (hA : ∀ l, area q l ≠ 0) : M2det q ≠ 0 := by
  rw [M2det_eq]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (hA 0) (hA 1)) (hA 2)) (hA 3))

theorem M2mul_inv (q : Conf) (h : M2det q ≠ 0) (w : V2) : M2mul q (M2inv q w) = w := by
  have e : M2det q = M2a q * M2c q - M2b q ^ 2 := rfl
  refine Prod.ext ?_ ?_
  · simp only [M2mul, M2inv]
    field_simp
    linear_combination (-w.1) * e
  · simp only [M2mul, M2inv]
    field_simp
    linear_combination (-w.2) * e

/-- `⟨M₂⁻¹ a, w⟩ = ⟨a, M₂⁻¹ w⟩` -/
theorem dot_M2inv (q : Conf) (a w : V2) : dot (M2inv q a) w = dot a (M2inv q w) := by
  simp only [dot, M2inv]
  ring

/-! ## the identity `Σ_e ω_e n_e = -M₂ L(v)` -/

/-- `ω_e = A_i A_j ⟨q_i - q_j, v_i - v_j⟩` -/
def omg (q v : Conf) (i j : Fin 4) : ℝ := area q i * area q j * dot (q i - q j) (v i - v j)

/-- `A_i A_j` is a self-stress: `Σ_e ω_e = 0` -/
theorem omg_selfstress (q v : Conf) : esum (omg q v) = 0 := by
  simp only [esum, omg, mp_area0, mp_area1, mp_area2, mp_area3, tri, cross, dot, Prod.fst_sub,
    Prod.snd_sub]
  ring

/-- `Σ_e ω_e n_e = -M₂ L(v)` -/
theorem M2_star (q v : Conf) :
    esumV (fun i j => omg q v i j • (q i + q j)) = -M2mul q (Lvec q v) := by
  refine Prod.ext ?_ ?_
  · simp only [esumV, omg, M2mul, M2a, M2b, M2c, Lvec, Fin.sum_univ_four, Prod.fst_add,
      Prod.fst_neg, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mp_area0, mp_area1,
      mp_area2, mp_area3, tri, cross, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  · simp only [esumV, omg, M2mul, M2a, M2b, M2c, Lvec, Fin.sum_univ_four, Prod.fst_add,
      Prod.snd_neg, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mp_area0, mp_area1,
      mp_area2, mp_area3, tri, cross, dot, Prod.fst_sub, Prod.snd_sub]
    ring

/-! ## the representation `u_e = τ_e M₂⁻¹ (z - n_e)` -/

private lemma mp_rr_pos (q : Conf) (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) :
    0 < rr q i j := by
  have h0 : 0 ≤ Rs q i j := by
    unfold Rs dot
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  refine Real.sqrt_pos.mpr (h0.lt_of_ne fun h' => hq i j h ?_)
  have e : (q i - q j).1 * (q i - q j).1 + (q i - q j).2 * (q i - q j).2 = 0 := h'.symm
  have hx : (q i - q j).1 * (q i - q j).1 = 0 := by
    linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
  have hy : (q i - q j).2 * (q i - q j).2 = 0 := by
    linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
  exact sub_eq_zero.mp (Prod.ext (mul_self_eq_zero.mp hx) (mul_self_eq_zero.mp hy))

/-- `τ_e ≠ 0` -/
theorem taugeo_ne (q : Conf) (hq : CollisionFree q) (hA : ∀ l, area q l ≠ 0) {i j : Fin 4}
    (h : i ≠ j) : taugeo q i j ≠ 0 :=
  mul_ne_zero (mul_ne_zero (hA i) (hA j)) (mp_rr_pos q hq h).ne'

/-- `ṙ_e τ_e = ω_e` -/
private lemma mp_dr_tau (q v : Conf) (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) :
    dr q v i j * taugeo q i j = omg q v i j := by
  have hr := (mp_rr_pos q hq h).ne'
  unfold dr taugeo omg
  field_simp

/-- **The midpoint representation.**  For every `z`, `u_e = τ_e M₂⁻¹ (z - n_e)` represents `L`:
`L(v) = Σ_e ṙ_e(v) u_e`. -/
theorem midpoint_rep (q : Conf) (hq : CollisionFree q) (hA : ∀ l, area q l ≠ 0) (z : V2)
    (v : Conf) :
    Lvec q v = esumV fun i j => dr q v i j • (taugeo q i j • M2inv q (z - (q i + q j))) := by
  have hdet := M2det_ne q hA
  have e : M2det q = M2a q * M2c q - M2b q ^ 2 := rfl
  have hs := omg_selfstress q v
  have hst := M2_star q v
  have he : ∀ i j : Fin 4, i ≠ j → dr q v i j • (taugeo q i j • M2inv q (z - (q i + q j))) =
      omg q v i j • M2inv q (z - (q i + q j)) := by
    intro i j h
    rw [smul_smul, mp_dr_tau q v hq h]
  simp only [esumV]
  rw [he 0 1 (by decide), he 0 2 (by decide), he 0 3 (by decide), he 1 2 (by decide),
    he 1 3 (by decide), he 2 3 (by decide)]
  have hst1 := congrArg Prod.fst hst
  have hst2 := congrArg Prod.snd hst
  simp only [esumV, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_neg, Prod.snd_neg, M2mul] at hst1 hst2
  simp only [esum] at hs
  generalize Lvec q v = L at hst1 hst2 ⊢
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, smul_eq_mul, M2inv, Prod.fst_sub,
      Prod.snd_sub]
    field_simp
    linear_combination L.1 * e + (-(M2c q) * z.1 + M2b q * z.2) * hs + M2c q * hst1 -
      M2b q * hst2
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul, M2inv, Prod.fst_sub,
      Prod.snd_sub]
    field_simp
    linear_combination L.2 * e + (-(M2a q) * z.2 + M2b q * z.1) * hs + M2a q * hst2 -
      M2b q * hst1

/-! ## the quadratic form of the test -/

/-- the quadratic form `T[u] = W |M₂ u|² - 3 (W Σ_e d_e ⟨n_e, u⟩² - ⟨t, u⟩²)` of the midpoint
test, for weights `d` on the edges, `W = Σ_e d_e`, `t = Σ_e d_e n_e` -/
def Tform (q : Conf) (d : Fin 4 → Fin 4 → ℝ) (u : V2) : ℝ :=
  esum d * dot (M2mul q u) (M2mul q u) -
    3 * (esum d * esum (fun i j => d i j * dot (q i + q j) u ^ 2) -
      (esum fun i j => d i j * dot (q i + q j) u) ^ 2)

/-- the weighted variance: `W Σ_e d_e (x̄ - x_e)² = W Σ_e d_e x_e² - (Σ_e d_e x_e)²` with
`x̄ = Σ_e d_e x_e / W` -/
private lemma mp_var (d1 d2 d3 d4 d5 d6 x1 x2 x3 x4 x5 x6 : ℝ)
    (hW : d1 + d2 + d3 + d4 + d5 + d6 ≠ 0) :
    (d1 + d2 + d3 + d4 + d5 + d6) *
        (d1 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x1) ^ 2 +
          d2 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x2) ^ 2 +
          d3 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x3) ^ 2 +
          d4 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x4) ^ 2 +
          d5 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x5) ^ 2 +
          d6 * ((d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) /
            (d1 + d2 + d3 + d4 + d5 + d6) - x6) ^ 2) =
      (d1 + d2 + d3 + d4 + d5 + d6) *
          (d1 * x1 ^ 2 + d2 * x2 ^ 2 + d3 * x3 ^ 2 + d4 * x4 ^ 2 + d5 * x5 ^ 2 + d6 * x6 ^ 2) -
        (d1 * x1 + d2 * x2 + d3 * x3 + d4 * x4 + d5 * x5 + d6 * x6) ^ 2 := by
  field_simp
  ring

private lemma mp_dot_sub (a b c : V2) : dot (a - b) c = dot a c - dot b c := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma mp_dot_smul (r : ℝ) (a c : V2) : dot (r • a) c = r * dot a c := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

private lemma mp_dot_esumV (f : Fin 4 → Fin 4 → V2) (c : V2) :
    dot (esumV f) c = esum fun i j => dot (f i j) c := by
  simp only [dot, esumV, esum, Prod.fst_add, Prod.snd_add]; ring

/-- **The midpoint test.**  If `T ≻ 0` for the weights `d_e = D_e τ_e²`, then some family
representing `L` has `S[w] < |w|² / 3` for every `w ≠ 0`. -/
theorem midpoint_test (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q)
    (σ : ℝ) (hσ : σ < 0) (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0)
    (hT : ∀ u : V2, u ≠ 0 → 0 < Tform q (fun i j => Dgeo m q i j * taugeo q i j ^ 2) u) :
    ∃ u : Fin 4 → Fin 4 → V2, (∀ v : Conf, Lvec q v = esumV fun i j => dr q v i j • u i j) ∧
      ∀ w : V2, w ≠ 0 → Sform m q u w < 1 / 3 * dot w w := by
  have hdet := M2det_ne q hA
  set d : Fin 4 → Fin 4 → ℝ := fun i j => Dgeo m q i j * taugeo q i j ^ 2 with hd_def
  have hd : ∀ i j : Fin 4, i ≠ j → 0 < d i j := by
    intro i j h
    have h1 := Dgeo_pos m hm q hq σ hσ hD hA h
    have h2 := taugeo_ne q hq hA h
    simp only [hd_def]
    positivity
  have hW : 0 < esum d := by
    have := hd 0 1 (by decide); have := hd 0 2 (by decide); have := hd 0 3 (by decide)
    have := hd 1 2 (by decide); have := hd 1 3 (by decide); have := hd 2 3 (by decide)
    simp only [esum]
    linarith
  set W := esum d with hW_def
  set t : V2 := esumV fun i j => d i j • (q i + q j) with ht_def
  set z : V2 := (1 / W) • t with hz_def
  refine ⟨fun i j => taugeo q i j • M2inv q (z - (q i + q j)), fun v => midpoint_rep q hq hA z v,
    fun w hw => ?_⟩
  set S := Sform m q (fun i j => taugeo q i j • M2inv q (z - (q i + q j))) w with hS_def
  have hwu : M2mul q (M2inv q w) = w := M2mul_inv q hdet w
  have hu0 : M2inv q w ≠ 0 := by
    intro h
    apply hw
    rw [← hwu, h]
    simp [M2mul]
  have key := hT (M2inv q w) hu0
  -- `S = Σ_e d_e ⟨z - n_e, M₂⁻¹ w⟩²`
  have hS : S = esum fun i j => d i j * dot (z - (q i + q j)) (M2inv q w) ^ 2 := by
    simp only [hS_def, Sform, esum, mp_dot_smul, dot_M2inv, hd_def]
    ring
  -- `⟨z - n_e, u⟩ = ⟨t, u⟩ / W - ⟨n_e, u⟩`
  have hx : ∀ i j : Fin 4, dot (z - (q i + q j)) (M2inv q w) =
      (esum fun k l => d k l * dot (q k + q l) (M2inv q w)) / W -
        dot (q i + q j) (M2inv q w) := by
    intro i j
    rw [mp_dot_sub, hz_def, mp_dot_smul, ht_def, mp_dot_esumV]
    simp only [mp_dot_smul]
    ring
  have hWS : W * S = W * esum (fun i j => d i j * dot (q i + q j) (M2inv q w) ^ 2) -
      (esum fun i j => d i j * dot (q i + q j) (M2inv q w)) ^ 2 := by
    rw [hS]
    simp only [hx]
    have hW' : W = d 0 1 + d 0 2 + d 0 3 + d 1 2 + d 1 3 + d 2 3 := hW_def
    simp only [esum]
    rw [hW']
    exact mp_var _ _ _ _ _ _ _ _ _ _ _ _ (by rw [← hW']; exact hW.ne')
  -- `T[M₂⁻¹ w] = W (|w|² - 3 S)`
  have hT' : Tform q d (M2inv q w) = W * (dot w w - 3 * S) := by
    unfold Tform
    rw [hwu, ← hW_def]
    linear_combination 3 * hWS
  rw [hT'] at key
  have h3 : (0 : ℝ) < dot w w - 3 * S :=
    lt_of_mul_lt_mul_left (by rw [mul_zero]; exact key) hW.le
  linarith

end

end C4
