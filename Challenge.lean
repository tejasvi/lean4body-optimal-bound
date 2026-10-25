module

public import Mathlib

/-!
# The sharp Hessian bound for four bodies: the statement

Conjecture 7.3 of the paper *Uniqueness of four-body convex central configurations for all masses*
(arXiv:2609.35632), stated with `sorry`. At every strictly convex central configuration of four
positive masses, the Hessian form `Q` dominates `(2/3) K`, where `K` is its radial part
(`conj_sharp`), and the inequality is strict wherever `K > 0` (`conj_sharp_strict`). The strict
form is equivalent to the paper's `λ_max(G) < 1/3`. `Solution.lean` imports the proofs and
`comparator.json` lists the compared theorems.

The definitions are copied verbatim from `C4/Defs.lean` (the same definitions as in the registered
development lean4body-uniqueness, PALOMAR-2026-10-02-000011); Comparator checks that the copies are
identical to the definitions the proofs use.

Bodies are indexed by `Fin 4`, so the paper's bodies `1, 2, 3, 4` are `0, 1, 2, 3` here. The
plane is `ℝ × ℝ`. Division is Lean's total division, with `x / 0 = 0`; the quantities divided by
below (the distances `r_ij` for `i ≠ j`, the moment of inertia and the total mass) are nonzero at
every collision-free configuration of positive masses.
-/

@[expose] public section

noncomputable section

namespace C4

/-! ## The plane and configurations -/

/-- the plane `ℝ²` -/
abbrev V2 := ℝ × ℝ

/-- the Euclidean inner product of `ℝ²` -/
def dot (u v : V2) : ℝ := u.1 * v.1 + u.2 * v.2

/-- `det (u, v)` -/
def cross (u v : V2) : ℝ := u.1 * v.2 - u.2 * v.1

/-- positions of the four bodies -/
abbrev Conf := Fin 4 → V2
/-- the four masses -/
abbrev Masses := Fin 4 → ℝ

/-- the sum over the six edges `ij`, `i < j` -/
def esum (f : Fin 4 → Fin 4 → ℝ) : ℝ := f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3

section
variable (q : Conf)

/-- `R_ij = r_ij²`, the squared distance between bodies `i` and `j` -/
def Rs (i j : Fin 4) : ℝ := dot (q i - q j) (q i - q j)

/-- `r_ij`, the distance between bodies `i` and `j` -/
noncomputable def rr (i j : Fin 4) : ℝ := Real.sqrt (Rs q i j)

/-- `s_ij = r_ij⁻³` -/
noncomputable def ss (i j : Fin 4) : ℝ := 1 / (Rs q i j * rr q i j)

/-- the oriented area `[ijk] = ½ det (q_j - q_i, q_k - q_i)` -/
def tri (i j k : Fin 4) : ℝ := cross (q j - q i) (q k - q i) / 2

/-- `A_1 = [234], A_2 = -[134], A_3 = [124], A_4 = -[123]` (paper numbering) -/
def area (l : Fin 4) : ℝ :=
  match l with
  | 0 => tri q 1 2 3
  | 1 => -tri q 0 2 3
  | 2 => tri q 0 1 3
  | 3 => -tri q 0 1 2

/-- no two bodies are at the same point -/
def CollisionFree : Prop := ∀ i j, i ≠ j → q i ≠ q j

/-- `q` is a strictly convex quadrilateral: two of the oriented areas are positive and two are
negative (paper, Lemma 2.3(d)).  The three disjuncts are the three pairs of diagonals. -/
def IsConvex : Prop :=
  (0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0) ∨
  (0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0) ∨
  (0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0)

end

section
variable (m : Masses) (q : Conf)

/-- the total mass `M` -/
def mtot : ℝ := m 0 + m 1 + m 2 + m 3

/-- the centre of mass -/
noncomputable def cm : V2 := (mtot m)⁻¹ • ∑ i, m i • q i

/-- the potential `U = Σ m_i m_j / r_ij` -/
noncomputable def Upot : ℝ := esum fun i j => m i * m j / rr q i j

/-- the moment of inertia about the centre of mass -/
noncomputable def Iner : ℝ := ∑ i, m i * dot (q i - cm m q) (q i - cm m q)

/-- central configuration: `∇_{q_i} U + λ m_i (q_i - c) = 0` for some `λ` (the term `j = i` of
the sum vanishes) -/
def IsCC : Prop :=
  CollisionFree q ∧
    ∃ lam : ℝ, ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q) = 0


/-- `λ = U / I` -/
noncomputable def lamC : ℝ := Upot m q / Iner m q

/-- `w_ij = s_ij - λ'`, `λ' = λ / M` -/
noncomputable def wgeo (i j : Fin 4) : ℝ := ss q i j - lamC m q / mtot m

/-- the first variation `ṙ_ij(v) = ⟨q_i - q_j, v_i - v_j⟩ / r_ij` -/
noncomputable def dr (v : Conf) (i j : Fin 4) : ℝ := dot (q i - q j) (v i - v j) / rr q i j

/-- `K(v) = Σ_e 3 m_i m_j s_e ṙ_e(v)²` -/
noncomputable def hessK (v : Conf) : ℝ := esum fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2

/-- `Q(v) = D²(U + λ I / 2)(q)[v, v] = K(v) - Σ_e m_i m_j w_e |v_i - v_j|²`, with `λ = U / I`
held fixed (paper, Lemma 2.1(a)) -/
noncomputable def hessQ (v : Conf) : ℝ :=
  hessK m q v - esum fun i j => m i * m j * wgeo m q i j * dot (v i - v j) (v i - v j)

end

/-! ## The theorems -/

/-- **Conjecture 7.3.**  At every strictly convex central configuration `q` of four positive
masses `m`, `Q_q(v) ≥ (2/3) K_q(v)` for every variation `v`. -/
theorem conj_sharp (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) : 2 / 3 * hessK m q v ≤ hessQ m q v := by
  sorry

/-- **Conjecture 7.3, strict form**, equivalent to `λ_max(G) < 1/3`: the inequality is strict for
every `v` with `K_q(v) > 0`. -/
theorem conj_sharp_strict (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) (hv : 0 < hessK m q v) :
    2 / 3 * hessK m q v < hessQ m q v := by
  sorry

end C4

end
