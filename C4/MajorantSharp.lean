module

public import C4.Majorant

@[expose] public section

/-!
# The sharp majorant

`majorant` applies Cauchy-Schwarz to the vectors `u_e = β_e + τ_e y` and so pays the trace:
`Q ≥ (1 - tr S(y)) K`.  Applied to the scalars `⟨u_e, L⟩` instead, it pays only the largest
eigenvalue.  Let `u` be any family of vectors on the edges that represents `L`, that is
`L(v) = Σ_e ṙ_e(v) u_e` for every `v` (by `L_beta`, `u_e = β_e + τ_e y` is one), and let
`S[w] = Σ_e D_e ⟨u_e, w⟩²`.  Then `|L|² = Σ_e ṙ_e ⟨u_e, L⟩`, and Cauchy-Schwarz with the weights
`k_e = 3 m_i m_j s_e = -σ / D_e` gives `|L|⁴ ≤ K Σ_e ⟨u_e, L⟩² / k_e = K S[L] / (-σ)`.

* `majorant_sharp`: if `S[w] ≤ λ |w|²` for every `w`, then `(1 - λ) K ≤ Q`;
* `majorant_sharp_strict`: if `S[w] < λ |w|²` for every `w ≠ 0`, then `(1 - λ) K < Q` where
  `K > 0`;
* `quad_pos`: a symmetric `2 × 2` matrix with positive determinant and trace is positive definite.
-/

namespace C4

noncomputable section

/-- `S[w] = Σ_e D_e ⟨u_e, w⟩²` for a family `u` of vectors on the edges -/
def Sform (m : Masses) (q : Conf) (u : Fin 4 → Fin 4 → V2) (w : V2) : ℝ :=
  esum fun i j => Dgeo m q i j * dot (u i j) w ^ 2

/-- a symmetric `2 × 2` matrix `[[p, r], [r, t]]` with `p t - r² > 0` and `p + t > 0` is positive
definite -/
theorem quad_pos {p r t : ℝ} (hdet : 0 < p * t - r ^ 2) (htr : 0 < p + t) {z1 z2 : ℝ}
    (hz : z1 ≠ 0 ∨ z2 ≠ 0) : 0 < p * z1 ^ 2 + 2 * r * z1 * z2 + t * z2 ^ 2 := by
  have hp : 0 < p := by
    by_contra h
    have ht : 0 < t := by linarith
    nlinarith [sq_nonneg r]
  have key : p * (p * z1 ^ 2 + 2 * r * z1 * z2 + t * z2 ^ 2) =
      (p * z1 + r * z2) ^ 2 + (p * t - r ^ 2) * z2 ^ 2 := by ring
  have hpos : 0 < (p * z1 + r * z2) ^ 2 + (p * t - r ^ 2) * z2 ^ 2 := by
    by_cases h2 : z2 = 0
    · have h1 : z1 ≠ 0 := hz.resolve_right (not_not.mpr h2)
      subst h2
      have : p * z1 ≠ 0 := mul_ne_zero hp.ne' h1
      have : 0 < (p * z1) ^ 2 := by positivity
      simpa using this
    · have : 0 < z2 ^ 2 := by positivity
      nlinarith [sq_nonneg (p * z1 + r * z2)]
  rw [← key] at hpos
  nlinarith

/-! ## the edge quantities -/

private lemma ms_Rs_pos (q : Conf) {i j : Fin 4} (h : q i ≠ q j) : 0 < Rs q i j := by
  have h0 : 0 ≤ Rs q i j := by
    unfold Rs dot
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  rcases h0.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have e : (q i - q j).1 * (q i - q j).1 + (q i - q j).2 * (q i - q j).2 = 0 := h'.symm
    have hx : (q i - q j).1 * (q i - q j).1 = 0 := by
      linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
    have hy : (q i - q j).2 * (q i - q j).2 = 0 := by
      linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
    exact h (sub_eq_zero.mp (Prod.ext (mul_self_eq_zero.mp hx) (mul_self_eq_zero.mp hy)))

private lemma ms_ss_pos (q : Conf) {i j : Fin 4} (h : q i ≠ q j) : 0 < ss q i j := by
  unfold ss
  exact one_div_pos.mpr (mul_pos (ms_Rs_pos q h) (Real.sqrt_pos.mpr (ms_Rs_pos q h)))

/-- `D_e k_e = -σ` with `k_e = 3 m_i m_j s_e > 0` -/
theorem Dgeo_mul_k (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q) (σ : ℝ)
    (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0) {i j : Fin 4} (h : i ≠ j) :
    0 < 3 * m i * m j * ss q i j ∧ Dgeo m q i j * (3 * m i * m j * ss q i j) = -σ := by
  refine ⟨mul_pos (mul_pos (mul_pos (by norm_num) (hm i)) (hm j)) (ms_ss_pos q (hq i j h)), ?_⟩
  have hij := hD i j h
  have hden : 3 * ss q i j * area q i * area q j ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero three_ne_zero (ms_ss_pos q (hq i j h)).ne') (hA i)) (hA j)
  unfold Dgeo
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  linear_combination (-3 * ss q i j) * hij

/-- `D_e > 0` at a configuration with Dziobek's relations and `σ < 0` -/
theorem Dgeo_pos (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q) (σ : ℝ)
    (hσ : σ < 0) (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0) {i j : Fin 4} (h : i ≠ j) :
    0 < Dgeo m q i j := by
  obtain ⟨hk, hDk⟩ := Dgeo_mul_k m hm q hq σ hD hA h
  by_contra hn
  have : Dgeo m q i j * (3 * m i * m j * ss q i j) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) hk.le
  linarith

/-! ## Cauchy-Schwarz on the scalars `⟨u_e, L⟩` -/

/-- weighted Cauchy-Schwarz for six terms (Lagrange's identity) -/
private lemma ms_wcs6 (k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 a6 c1 c2 c3 c4 c5 c6 : ℝ)
    (h1 : 0 ≤ k1) (h2 : 0 ≤ k2) (h3 : 0 ≤ k3) (h4 : 0 ≤ k4) (h5 : 0 ≤ k5) (h6 : 0 ≤ k6) :
    (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 + k6 * a6 * c6) ^ 2 ≤
      (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 + k6 * c6 ^ 2) := by
  have key :
      (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 + k6 * c6 ^ 2) -
      (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 +
        k6 * a6 * c6) ^ 2 =
      k1 * k2 * (a1 * c2 - a2 * c1) ^ 2 + k1 * k3 * (a1 * c3 - a3 * c1) ^ 2 +
      k1 * k4 * (a1 * c4 - a4 * c1) ^ 2 + k1 * k5 * (a1 * c5 - a5 * c1) ^ 2 +
      k1 * k6 * (a1 * c6 - a6 * c1) ^ 2 + k2 * k3 * (a2 * c3 - a3 * c2) ^ 2 +
      k2 * k4 * (a2 * c4 - a4 * c2) ^ 2 + k2 * k5 * (a2 * c5 - a5 * c2) ^ 2 +
      k2 * k6 * (a2 * c6 - a6 * c2) ^ 2 + k3 * k4 * (a3 * c4 - a4 * c3) ^ 2 +
      k3 * k5 * (a3 * c5 - a5 * c3) ^ 2 + k3 * k6 * (a3 * c6 - a6 * c3) ^ 2 +
      k4 * k5 * (a4 * c5 - a5 * c4) ^ 2 + k4 * k6 * (a4 * c6 - a6 * c4) ^ 2 +
      k5 * k6 * (a5 * c6 - a6 * c5) ^ 2 := by ring
  have hpos : 0 ≤
      k1 * k2 * (a1 * c2 - a2 * c1) ^ 2 + k1 * k3 * (a1 * c3 - a3 * c1) ^ 2 +
      k1 * k4 * (a1 * c4 - a4 * c1) ^ 2 + k1 * k5 * (a1 * c5 - a5 * c1) ^ 2 +
      k1 * k6 * (a1 * c6 - a6 * c1) ^ 2 + k2 * k3 * (a2 * c3 - a3 * c2) ^ 2 +
      k2 * k4 * (a2 * c4 - a4 * c2) ^ 2 + k2 * k5 * (a2 * c5 - a5 * c2) ^ 2 +
      k2 * k6 * (a2 * c6 - a6 * c2) ^ 2 + k3 * k4 * (a3 * c4 - a4 * c3) ^ 2 +
      k3 * k5 * (a3 * c5 - a5 * c3) ^ 2 + k3 * k6 * (a3 * c6 - a6 * c3) ^ 2 +
      k4 * k5 * (a4 * c5 - a5 * c4) ^ 2 + k4 * k6 * (a4 * c6 - a6 * c4) ^ 2 +
      k5 * k6 * (a5 * c6 - a6 * c5) ^ 2 := by positivity
  linarith

/-- the Cauchy-Schwarz step: with `L = Σ_e a_e u_e`, `K = Σ_e k_e a_e²` and
`S[L] = Σ_e D_e ⟨u_e, L⟩²`, `-σ |L|⁴ ≤ K S[L]` -/
private lemma ms_cs (σ : ℝ) (hσ : σ < 0)
    (k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 : ℝ) (u1 u2 u3 u4 u5 u6 : V2)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hk3 : 0 < k3) (hk4 : 0 < k4) (hk5 : 0 < k5) (hk6 : 0 < k6)
    (hD1 : D1 * k1 = -σ) (hD2 : D2 * k2 = -σ) (hD3 : D3 * k3 = -σ) (hD4 : D4 * k4 = -σ)
    (hD5 : D5 * k5 = -σ) (hD6 : D6 * k6 = -σ) (L : V2)
    (hL : L = a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6) :
    -σ * dot L L ^ 2 ≤
      (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (D1 * dot u1 L ^ 2 + D2 * dot u2 L ^ 2 + D3 * dot u3 L ^ 2 + D4 * dot u4 L ^ 2 +
          D5 * dot u5 L ^ 2 + D6 * dot u6 L ^ 2) := by
  -- `|L|² = Σ_e a_e ⟨u_e, L⟩`
  have hLL : dot L L = a1 * dot u1 L + a2 * dot u2 L + a3 * dot u3 L + a4 * dot u4 L +
      a5 * dot u5 L + a6 * dot u6 L := by
    conv_lhs => arg 1; rw [hL]
    simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  -- `⟨u_e, L⟩ = k_e c_e`
  obtain ⟨c1, e1⟩ : ∃ c, dot u1 L = k1 * c := ⟨dot u1 L / k1, by field_simp⟩
  obtain ⟨c2, e2⟩ : ∃ c, dot u2 L = k2 * c := ⟨dot u2 L / k2, by field_simp⟩
  obtain ⟨c3, e3⟩ : ∃ c, dot u3 L = k3 * c := ⟨dot u3 L / k3, by field_simp⟩
  obtain ⟨c4, e4⟩ : ∃ c, dot u4 L = k4 * c := ⟨dot u4 L / k4, by field_simp⟩
  obtain ⟨c5, e5⟩ : ∃ c, dot u5 L = k5 * c := ⟨dot u5 L / k5, by field_simp⟩
  obtain ⟨c6, e6⟩ : ∃ c, dot u6 L = k6 * c := ⟨dot u6 L / k6, by field_simp⟩
  have cs := ms_wcs6 k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 a6 c1 c2 c3 c4 c5 c6
    hk1.le hk2.le hk3.le hk4.le hk5.le hk6.le
  -- `D_e ⟨u_e, L⟩² = -σ k_e c_e²`
  have hS : D1 * dot u1 L ^ 2 + D2 * dot u2 L ^ 2 + D3 * dot u3 L ^ 2 + D4 * dot u4 L ^ 2 +
      D5 * dot u5 L ^ 2 + D6 * dot u6 L ^ 2 =
      -σ * (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 +
        k6 * c6 ^ 2) := by
    rw [e1, e2, e3, e4, e5, e6]
    linear_combination (k1 * c1 ^ 2) * hD1 + (k2 * c2 ^ 2) * hD2 + (k3 * c3 ^ 2) * hD3 +
      (k4 * c4 ^ 2) * hD4 + (k5 * c5 ^ 2) * hD5 + (k6 * c6 ^ 2) * hD6
  rw [hS, hLL, e1, e2, e3, e4, e5, e6]
  have hσ' : -σ * (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 +
      k6 * a6 * c6) ^ 2 ≤ -σ *
      ((k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 + k6 * c6 ^ 2)) := by
    exact mul_le_mul_of_nonneg_left cs (by linarith)
  calc -σ * (a1 * (k1 * c1) + a2 * (k2 * c2) + a3 * (k3 * c3) + a4 * (k4 * c4) +
          a5 * (k5 * c5) + a6 * (k6 * c6)) ^ 2
      = -σ * (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 +
          k6 * a6 * c6) ^ 2 := by ring
    _ ≤ _ := hσ'
    _ = _ := by ring

private lemma ms_div {s X K lam : ℝ} (hX : 0 ≤ X) (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (h : s * X ^ 2 ≤ lam * K * X) : s * X ≤ lam * K := by
  rcases hX.eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact mul_nonneg hlam hK
  · refine le_of_mul_le_mul_right ?_ h0
    calc s * X * X = s * X ^ 2 := by ring
      _ ≤ lam * K * X := h

private lemma ms_div_strict {s X K lam : ℝ} (hX : 0 < X) (h : s * X ^ 2 < lam * K * X) :
    s * X < lam * K := by
  refine lt_of_mul_lt_mul_right ?_ hX.le
  calc s * X * X = s * X ^ 2 := by ring
    _ < lam * K * X := h

private lemma ms_dot_nonneg (L : V2) : 0 ≤ dot L L := by
  simp only [dot]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private lemma ms_dot_pos {L : V2} (h : L ≠ 0) : 0 < dot L L := by
  simp only [dot]
  rcases (not_and_or.mp (fun h' => h (Prod.ext h'.1 h'.2))) with h1 | h1
  · exact add_pos_of_pos_of_nonneg (mul_self_pos.mpr h1) (mul_self_nonneg _)
  · exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.mpr h1)

/-- the majorant in terms of the edge quantities -/
private lemma ms_core (σ : ℝ) (hσ : σ < 0) (lam : ℝ) (hlam : 0 ≤ lam)
    (k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 : ℝ) (u1 u2 u3 u4 u5 u6 : V2)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hk3 : 0 < k3) (hk4 : 0 < k4) (hk5 : 0 < k5) (hk6 : 0 < k6)
    (hD1 : D1 * k1 = -σ) (hD2 : D2 * k2 = -σ) (hD3 : D3 * k3 = -σ) (hD4 : D4 * k4 = -σ)
    (hD5 : D5 * k5 = -σ) (hD6 : D6 * k6 = -σ)
    (hS : ∀ w : V2, D1 * dot u1 w ^ 2 + D2 * dot u2 w ^ 2 + D3 * dot u3 w ^ 2 +
      D4 * dot u4 w ^ 2 + D5 * dot u5 w ^ 2 + D6 * dot u6 w ^ 2 ≤ lam * dot w w) :
    (1 - lam) *
        (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) ≤
      k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2 +
        σ * dot (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6)
          (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6) := by
  set L := a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6 with hL
  set K := k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2
    with hK
  have cs := ms_cs σ hσ k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 u1 u2 u3 u4 u5 u6
    hk1 hk2 hk3 hk4 hk5 hk6 hD1 hD2 hD3 hD4 hD5 hD6 L hL
  rw [← hK] at cs
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have h1 : -σ * dot L L ^ 2 ≤ lam * K * dot L L :=
    calc -σ * dot L L ^ 2 ≤ K * (D1 * dot u1 L ^ 2 + D2 * dot u2 L ^ 2 + D3 * dot u3 L ^ 2 +
          D4 * dot u4 L ^ 2 + D5 * dot u5 L ^ 2 + D6 * dot u6 L ^ 2) := cs
      _ ≤ K * (lam * dot L L) := mul_le_mul_of_nonneg_left (hS L) hK0
      _ = lam * K * dot L L := by ring
  have h2 := ms_div (ms_dot_nonneg L) hK0 hlam h1
  linarith only [h2]

/-- the strict form: `S[w] < λ |w|²` for `w ≠ 0` and `K > 0` -/
private lemma ms_core_strict (σ : ℝ) (hσ : σ < 0) (lam : ℝ) (hlam : 0 < lam)
    (k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 : ℝ) (u1 u2 u3 u4 u5 u6 : V2)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hk3 : 0 < k3) (hk4 : 0 < k4) (hk5 : 0 < k5) (hk6 : 0 < k6)
    (hD1 : D1 * k1 = -σ) (hD2 : D2 * k2 = -σ) (hD3 : D3 * k3 = -σ) (hD4 : D4 * k4 = -σ)
    (hD5 : D5 * k5 = -σ) (hD6 : D6 * k6 = -σ)
    (hS : ∀ w : V2, w ≠ 0 → D1 * dot u1 w ^ 2 + D2 * dot u2 w ^ 2 + D3 * dot u3 w ^ 2 +
      D4 * dot u4 w ^ 2 + D5 * dot u5 w ^ 2 + D6 * dot u6 w ^ 2 < lam * dot w w)
    (hKpos : 0 < k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 +
      k6 * a6 ^ 2) :
    (1 - lam) *
        (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) <
      k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2 +
        σ * dot (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6)
          (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6) := by
  set L := a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6 with hL
  set K := k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2
    with hK
  have cs := ms_cs σ hσ k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 u1 u2 u3 u4 u5 u6
    hk1 hk2 hk3 hk4 hk5 hk6 hD1 hD2 hD3 hD4 hD5 hD6 L hL
  rw [← hK] at cs
  by_cases hL0 : L = 0
  · have h0 : dot L L = 0 := by rw [hL0]; simp [dot]
    have h1 : 0 < lam * K := mul_pos hlam hKpos
    rw [h0]
    linarith only [h1]
  · have h1 : -σ * dot L L ^ 2 < lam * K * dot L L :=
      calc -σ * dot L L ^ 2 ≤ K * (D1 * dot u1 L ^ 2 + D2 * dot u2 L ^ 2 + D3 * dot u3 L ^ 2 +
            D4 * dot u4 L ^ 2 + D5 * dot u5 L ^ 2 + D6 * dot u6 L ^ 2) := cs
        _ < K * (lam * dot L L) := mul_lt_mul_of_pos_left (hS L hL0) hKpos
        _ = lam * K * dot L L := by ring
    have h2 := ms_div_strict (ms_dot_pos hL0) h1
    linarith only [h2]

/-- **The sharp majorant.**  If the family `u` represents `L` and `S[w] ≤ λ |w|²` for every
`w`, then `(1 - λ) K ≤ Q`. -/
theorem majorant_sharp (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q)
    (σ : ℝ) (hσ : σ < 0) (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0)
    (u : Fin 4 → Fin 4 → V2) (hu : ∀ v : Conf, Lvec q v = esumV fun i j => dr q v i j • u i j)
    (lam : ℝ) (hlam : 0 ≤ lam) (hS : ∀ w : V2, Sform m q u w ≤ lam * dot w w) (v : Conf) :
    (1 - lam) * hessK m q v ≤ hessQ m q v := by
  have hk := fun i j (h : i ≠ j) => Dgeo_mul_k m hm q hq σ hD hA h
  rw [hessQ_identity m q σ hD v, hu v]
  simp only [Sform, esum] at hS
  simp only [hessK, esum, esumV]
  exact ms_core σ hσ lam hlam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hk 0 1 (by decide)).1 (hk 0 2 (by decide)).1 (hk 0 3 (by decide)).1 (hk 1 2 (by decide)).1
    (hk 1 3 (by decide)).1 (hk 2 3 (by decide)).1
    (hk 0 1 (by decide)).2 (hk 0 2 (by decide)).2 (hk 0 3 (by decide)).2 (hk 1 2 (by decide)).2
    (hk 1 3 (by decide)).2 (hk 2 3 (by decide)).2 hS

/-- **The sharp majorant, strict form.**  If the family `u` represents `L`, `S[w] < λ |w|²` for
every `w ≠ 0` and `λ > 0`, then `(1 - λ) K < Q` wherever `K > 0`. -/
theorem majorant_sharp_strict (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q)
    (σ : ℝ) (hσ : σ < 0) (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0)
    (u : Fin 4 → Fin 4 → V2) (hu : ∀ v : Conf, Lvec q v = esumV fun i j => dr q v i j • u i j)
    (lam : ℝ) (hlam : 0 < lam) (hS : ∀ w : V2, w ≠ 0 → Sform m q u w < lam * dot w w)
    (v : Conf) (hv : 0 < hessK m q v) :
    (1 - lam) * hessK m q v < hessQ m q v := by
  have hk := fun i j (h : i ≠ j) => Dgeo_mul_k m hm q hq σ hD hA h
  rw [hessQ_identity m q σ hD v, hu v]
  simp only [Sform, esum] at hS
  simp only [hessK, esum] at hv
  simp only [hessK, esum, esumV]
  exact ms_core_strict σ hσ lam hlam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hk 0 1 (by decide)).1 (hk 0 2 (by decide)).1 (hk 0 3 (by decide)).1 (hk 1 2 (by decide)).1
    (hk 1 3 (by decide)).1 (hk 2 3 (by decide)).1
    (hk 0 1 (by decide)).2 (hk 0 2 (by decide)).2 (hk 0 3 (by decide)).2 (hk 1 2 (by decide)).2
    (hk 1 3 (by decide)).2 (hk 2 3 (by decide)).2 hS hv

end

end C4
