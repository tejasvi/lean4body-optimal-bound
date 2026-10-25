module

public import C4.Corner
public import C4Cert.CornerBox0
public import C4Cert.CornerBox1
public import C4Cert.CornerBox2

@[expose] public section

/-!
# The corner theorem

`corner_cap`: in the corner disc `b² + (ga - 1)² ≤ (1/128)²`, `al ≤ 0`, every feasible zero of `P̂`
passes the normalized midpoint test `chMidN` (`det > 0`, `tr > 0`).  The three staged
certificates `C4Cert.CornerBox0..2` cover `-17/32 ≤ al ≤ 0`, which holds there (`alpha_range`).
-/

namespace C4
namespace CTF

noncomputable section

/-- **The corner theorem**, from three staged boxes covering `-17/32 ≤ al ≤ 0` (the box of `s0`
is `[-17/32, -3/8]`, that of `s1` is `[-3/8, -1/8]`, that of `s2` is `[-1/8, 0]`). -/
theorem corner_cap_of {s0 s1 s2 : SHint} (v0 : s0.Valid) (v1 : s1.Valid) (v2 : s2.Valid)
    (e0 : s0.h = hint0) (e1 : s1.h = hint1) (e2 : s2.h = hint2) :
    ∀ b al ga xi : ℝ, 0 < b → al ≤ 0 → b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2 →
      InC (1 + b * al) b (b * ga) (1 / 2 + b * xi) → chPR b al ga xi = 0 →
      0 < (@chMidN ℝ opsReal b al ga xi).det ∧ 0 < (@chMidN ℝ opsReal b al ga xi).tr := by
  intro b al ga xi hb hal hr hC hP
  have hal1 := alpha_range hb hal hr hC
  have hb1 : b ≤ 1 / 2 ^ 7 := by norm_num; exact disc_b hb hr
  have hg : |ga - 1| ≤ 1 / 2 ^ 7 := by norm_num; exact disc_g hr
  rcases le_total al (-3 / 8) with k1 | k1
  · have e : (hint0.ac : ℝ) / S = -29 / 64 :=
      ac_val (n := -29) (m := 64) (by norm_num) (by norm_num) (by decide)
    have ew : (hint0.wm : ℝ) / 2 ^ hint0.s = 5 / 64 := by
      change ((5 : ℕ) : ℝ) / 2 ^ 6 = 5 / 64; norm_num
    refine staged_box_cap v0 (by rw [e0]; decide) (by rw [e0]; decide) (by rw [e0]; decide) hb
      (by rw [e0]; exact hb1) (by rw [e0]; exact hg) ?_ hC hP
    rw [e0, e, ew, abs_le]; constructor <;> linarith
  rcases le_total al (-1 / 8) with k2 | k2
  · have e : (hint1.ac : ℝ) / S = -1 / 4 :=
      ac_val (n := -1) (m := 4) (by norm_num) (by norm_num) (by decide)
    have ew : (hint1.wm : ℝ) / 2 ^ hint1.s = 1 / 8 := by
      change ((1 : ℕ) : ℝ) / 2 ^ 3 = 1 / 8; norm_num
    refine staged_box_cap v1 (by rw [e1]; decide) (by rw [e1]; decide) (by rw [e1]; decide) hb
      (by rw [e1]; exact hb1) (by rw [e1]; exact hg) ?_ hC hP
    rw [e1, e, ew, abs_le]; constructor <;> linarith
  · have e : (hint2.ac : ℝ) / S = -1 / 16 :=
      ac_val (n := -1) (m := 16) (by norm_num) (by norm_num) (by decide)
    have ew : (hint2.wm : ℝ) / 2 ^ hint2.s = 1 / 16 := by
      change ((1 : ℕ) : ℝ) / 2 ^ 4 = 1 / 16; norm_num
    refine staged_box_cap v2 (by rw [e2]; decide) (by rw [e2]; decide) (by rw [e2]; decide) hb
      (by rw [e2]; exact hb1) (by rw [e2]; exact hg) ?_ hC hP
    rw [e2, e, ew, abs_le]; constructor <;> linarith


/-- **The corner theorem** (`CornerCapN` of `C4.Cap2`, with `chMidNR` unfolded). -/
theorem corner_cap : ∀ b al ga xi : ℝ, 0 < b → al ≤ 0 → b ^ 2 + (ga - 1) ^ 2 ≤ (1 / 128) ^ 2 →
    InC (1 + b * al) b (b * ga) (1 / 2 + b * xi) → chPR b al ga xi = 0 →
    0 < (@chMidN ℝ opsReal b al ga xi).det ∧ 0 < (@chMidN ℝ opsReal b al ga xi).tr :=
  corner_cap_of sb0_valid sb1_valid sb2_valid rfl rfl rfl

end

end CTF
end C4
