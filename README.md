# The optimal Hessian bound for convex four-body central configurations, in Lean

A Lean 4 + Mathlib formalization of Conjecture 7.3 of the paper *Uniqueness of four-body convex
central configurations for all masses* by Tejasvi S. Tomar
([arXiv:2609.35632](https://arxiv.org/abs/2609.35632)): at every strictly convex central
configuration of four positive masses, the Hessian form `Q` of `U + (λ/2) I` satisfies
`Q ≥ (2/3) K`, where `K` is its radial part, and the inequality is strict wherever `K > 0`. The
numbers of theorems and sections below refer to the paper.

In the paper's notation the conjecture reads `λ_max(G) < 1/3`, where `G` is the explicit `2 × 2`
matrix of Proposition 3.5. By Proposition 3.5(c) the generalized eigenvalues of the pair `(Q, K)`
are `1, 1, 1, 1 - μ₁, 1 - μ₂`, where `μ₁ ≥ μ₂ ≥ 0` are the eigenvalues of `G`, so
`λ_max(G) < 1/3` holds exactly when `Q > (2/3) K` on every variation with `K > 0`, which is the
strict statement proved here. By Proposition 7.2(d) of the paper the constant `2/3` cannot be
improved. The statement sharpens Theorem B of the paper, `Q ≥ K/4`.

**Relation to earlier formalizations.** The paper cites
[tejasvi/lean4body](https://github.com/tejasvi/lean4body), release v1.0, which formalizes Theorems A
and B (with the constant `1/4`). The registered development
[lean4body-uniqueness](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000011&version=1)
(Palomar `PALOMAR-2026-10-02-000011`) formalizes Theorem A, with the bound `Q ≥ K/128` in its
version 1 and with Theorem B, `Q ≥ K/4`, in its version 2. This repository takes the definitions
and the reduction to the normal form of its version 1 unchanged, and proves the optimal bound with a
new computer-assisted step: a different test, a different checker, an exact theorem at the corner
where the margin of the test vanishes, and a symmetry that halves the region (see
[Proof outline](#proof-outline) and
[Relation to lean4body-uniqueness](#relation-to-lean4body-uniqueness)).

The development contains no `sorry`, and the proofs use only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The computer-assisted part is checked by Lean's
kernel with `decide +kernel`; the trusted base is Lean's kernel, including its built-in arithmetic
on natural-number literals (see [Trust base](#trust-base)).

## Main statements

### Definitions

The definitions are in [`C4/Defs.lean`](C4/Defs.lean), copied verbatim from lean4body-uniqueness,
and [`Challenge.lean`](Challenge.lean) copies them again. Bodies are indexed by `Fin 4`, so the
paper's bodies 1, 2, 3, 4 are `0, 1, 2, 3` here. A configuration is `q : Conf`, where
`Conf = Fin 4 → V2` and `V2 = ℝ × ℝ`, and masses are `m : Masses = Fin 4 → ℝ`. The statements use
these definitions (`m` and `q` are variables of the section):

```lean
-- C4/Defs.lean
def CollisionFree : Prop := ∀ i j, i ≠ j → q i ≠ q j

def IsCC : Prop :=
  CollisionFree q ∧
    ∃ lam : ℝ, ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q) = 0

def IsConvex : Prop :=
  (0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0) ∨
  (0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0) ∨
  (0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0)

noncomputable def hessK (v : Conf) : ℝ := esum fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2

noncomputable def hessQ (v : Conf) : ℝ :=
  hessK m q v - esum fun i j => m i * m j * wgeo m q i j * dot (v i - v j) (v i - v j)
```

* `ss q i j = r_ij⁻³`, `cm m q` is the centre of mass `c`, and `area q l` is the oriented area
  `A_{l+1}` of the paper: `A₁ = [234]`, `A₂ = -[134]`, `A₃ = [124]`, `A₄ = -[123]`, where
  `[ijk] = ½ det(q_j - q_i, q_k - q_i)`. `esum` is the sum over the six pairs `i < j`,
  `dr q v i j` is `ṙ_ij(v) = ⟨q_i - q_j, v_i - v_j⟩ / r_ij`, and `wgeo m q i j = r_ij⁻³ - λ/M`,
  with `λ = U/I` and `M` the total mass.
* `IsCC m q` means that `q` is collision free and that for some `λ` every body satisfies
  equation (1.1), `∇_{q_i} U + λ m_i (q_i - c) = 0`. The sum over `j` is `∇_{q_i} U`; its term
  `j = i` vanishes.
* `IsConvex q` means that two of the oriented areas are positive and two are negative. Its three
  disjuncts are the three ways of pairing the bodies into diagonals. lean4body-uniqueness proves
  that this holds exactly when the bodies are the vertices of a strictly convex quadrilateral
  (`isConvex_iff_order`, Lemma 2.3(d)).
* `hessK` and `hessQ` are the forms `K` and `Q` of the paper. `hessQ` is defined by the formula of
  Lemma 2.1(a); lean4body-uniqueness proves (`hessian_Phi`) that for positive masses and every
  collision-free `q` it is the Hessian at `q` of `U + (λ/2) I` with `λ` held fixed.
* Division in Lean is total, with `x / 0 = 0`. The quantities divided by in these definitions
  (`r_ij` for `i ≠ j`, `I` and `M`) are nonzero at every collision-free configuration of positive
  masses.

### The theorems

```lean
-- C4/ConjSharp.lean
theorem conj_sharp (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) : 2 / 3 * hessK m q v ≤ hessQ m q v

theorem conj_sharp_strict (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) (hv : 0 < hessK m q v) :
    2 / 3 * hessK m q v < hessQ m q v
```

`conj_sharp` is the inequality `Q ≥ (2/3) K` of Conjecture 7.3 and `conj_sharp_strict` its strict
form; as explained above, the strict form is equivalent to `λ_max(G) < 1/3`. Both theorems have no
hypotheses beyond those of the paper.

### Not formalized

* The optimality of `2/3` (Proposition 7.2(d)), which needs the limits of the central
  configurations at the corner where two masses tend to zero.
* The matrix `G` and the equivalence of Proposition 3.5(c): the theorems are stated through `Q`
  and `K` directly.

## Proof outline

The proof follows the paper's proof of Theorem B, with a sharper majorant, an exact test in place
of the trace, and new certificates.

1. **Reduction to the normal form** (from lean4body-uniqueness, unchanged). `normalize` relabels
   the bodies and applies a similarity, which multiplies `Q` and `K` by the same positive factor,
   to bring the configuration to the normal form `qd a b c x` of Corbera, Cors and Roberts
   (Lemma 4.2). `dziobek_convex` gives Dziobek's relations with `σ < 0`, and `inC_of_dziobek` and
   `normal_form` put `(a, b, c, x)` in the region `𝒞` on which the Dziobek function `P` vanishes
   (Lemma 4.1).
2. **The sharp majorant** ([`C4/MajorantSharp.lean`](C4/MajorantSharp.lean)). By Proposition 3.1,
   `Q = K + σ |L|²` with `L(v) = Σ_l A_l v_l`. If a family of vectors `u_e` on the six edges
   represents `L`, that is `L(v) = Σ_e ṙ_e(v) u_e` for every `v`, and
   `S[w] = Σ_e D_e ⟨u_e, w⟩² ≤ λ |w|²` for every `w`, then the Cauchy–Schwarz inequality applied
   to the scalars `⟨u_e, L(v)⟩` gives `|σ| |L|² ≤ λ K`, hence `Q ≥ (1 - λ) K` (`majorant_sharp`,
   and `majorant_sharp_strict` for the strict form). With `u_e = β_e + τ_e y` this is
   Proposition 3.5(a) with `λ_max` in place of the trace.
3. **The midpoint representation** ([`C4/Midpoint.lean`](C4/Midpoint.lean)). A polynomial
   identity, `Σ_e A_i A_j ⟨q_i - q_j, v_i - v_j⟩ (q_i + q_j) = -M₂ L(v)` with
   `M₂ = Σ_l A_l q_l q_lᵀ`, and `det M₂ = -4 A₁A₂A₃A₄ ≠ 0` show that
   `u_e = τ_e M₂⁻¹ (z - q_i - q_j)` represents `L` for every `z ∈ ℝ²` (`midpoint_rep`). For the
   best `z`, `|w|² - 3 S[w]` is a positive multiple of the quadratic form of
   `T = W M₂² - 3 (W Σ_e d_e n_e n_eᵀ - t tᵀ)` at `M₂⁻¹ w`, where `d_e = D_e τ_e²`,
   `n_e = q_i + q_j`, `W = Σ_e d_e` and `t = Σ_e d_e n_e` (`midpoint_test`). So `T ≻ 0` gives
   `S[w] < |w|²/3`. The family `u` is the paper's `β_e + τ_e y*`, so `T ≻ 0` is exactly
   `λ_max(G) < 1/3`; neither `β_e` nor any inverse of an area enters the test.
4. **The normalized test** ([`C4Check/Formulas2.lean`](C4Check/Formulas2.lean),
   [`C4/NormalForm2.lean`](C4/NormalForm2.lean)). The certificates check `det Y > 0` and
   `tr Y > 0` for the `2 × 2` matrix `Y = diag(1, s²) - M̃⁻¹ C̃ M̃⁻¹`, `s = √(1 - x²)`, which is `T`
   in the frame scaled by `diag(1, s)` and normalized; it is computed from `(a, b, c, x)` without
   `√(1 - x²)`, and its matrix `C̃` is a sum of positive semidefinite terms. At a point of `𝒞` that
   carries Dziobek's relations, the weights of the formula are a positive multiple of
   `D_e τ_e²`, edge by edge (`nf2_weights`), and `T[u] = 3 λ² den W Y[k N (u₁, s u₂)]` with
   positive `λ`, `den` and `W` (`nfN_Tform_pos`). In the blow-up chart `a = 1 + b α`, `c = b γ`,
   `x = 1/2 + b ξ` the same matrix is computed with every power of `b` cancelled
   ([`C4/Chart2.lean`](C4/Chart2.lean), `ch2N_eq_inC`).
5. **The symmetry** ([`C4/Symmetry.lean`](C4/Symmetry.lean)). The map
   `(a, b, c, x) ↦ (1/a, c/a, b/a, x)` is the relabelling `(1 2)(3 4)` followed by an
   orientation-reversing similarity of ratio `1/a`. It maps central configurations to central
   configurations with the masses relabelled (`isCC_iota`), maps `𝒞` into `𝒞` (`inC_iota`), and
   multiplies `Q` and `K` by the same factor (`hess_iota`). So the certificates need to cover only
   `a ≤ 1`.
6. **The caps** ([`C4/Cap2.lean`](C4/Cap2.lean)). Every point of `𝒞` with `P = 0` and `a ≤ 1`
   lies in the direct region `b ≥ 1/2`, in the coordinates `(a, b, c)`; in one of three regions
   of the blow-up chart `0 < b ≤ 1/2`, in the coordinates `(b, α, γ)`; or in the corner disc
   `b² + (γ - 1)² ≤ (1/128)²`. Root grids cover these regions: 28 cells of side `1/4` in the
   direct region, and 20, 20 and 24 cells in the chart for `1/4 ≤ b ≤ 1/2`, `1/8 ≤ b ≤ 1/4`
   and `0 < b ≤ 1/8` ([`C4Check/Grid2.lean`](C4Check/Grid2.lean)). A certificate splits a cell
   into pieces and gives each piece a hint. On a piece the dependent coordinate is written as
   `x = X(z) + e t₃`, with a quadratic hint polynomial `X` and a band of width `e`, and the
   checker computes in fixed-point Taylor models of order 3 in four variables with an interval
   remainder ([`C4Check/TF.lean`](C4Check/TF.lean)). A root phase shows, in at most two Newton
   steps, that every zero of `P` over the piece lies in the band; a test phase shows `tr Y > 0`
   and `det Y > μ g` on the band, where `μ ≥ 0` and `g ≥ 0` is one of the six inequalities
   that define `𝒞` (or `μ = 0`). In the 212 piece modules of [`C4Cert/`](C4Cert), 5,924 theorems
   check pieces of cells and 20 check runs of 48 whole cells, all by `decide +kernel`; 13 theorems
   assemble them into covers, and [`C4Cert/Gen2_Cover.lean`](C4Cert/Gen2_Cover.lean) chains these
   into one cover theorem per root grid. At the corner `b = 0`, `γ = 1` the margin of the test
   vanishes to second order, so no interval enclosure on cells can reach it; `corner_cap`
   ([`C4/Corner.lean`](C4/Corner.lean), [`C4Cert/CornerCap.lean`](C4Cert/CornerCap.lean)) proves the
   test there with Taylor forms whose coefficients are exact polynomials in `α`
   ([`C4Check/CornerTF.lean`](C4Check/CornerTF.lean)). In the disc the conditions on a central
   configuration give `α ≥ -17/32`, and three staged certificates (`C4Cert/CornerBox0`–`2`, 39
   theorems) cover `-17/32 ≤ α ≤ 0`. In each, the root `ξ` of `P̂` is localized, a slope of `P̂`
   relates it to an exact polynomial, and the Taylor-form evaluation of the test gives `det > 0`
   and `tr > 0`.
7. **Assembly** ([`C4/ConjSharp.lean`](C4/ConjSharp.lean)). `sharp_qd` combines the caps with the
   bridge of step 4 for `a ≤ 1` and with the symmetry for `a > 1`, and `midpoint_test` and
   `majorant_sharp` give `Q ≥ (2/3) K` at the normal form, which `normalize` transfers back.

## Trust base

[`Axioms.lean`](Axioms.lean) prints the axioms of `conj_sharp`, `conj_sharp_strict` and `sharp_cap`,
and of seventeen intermediate results: the sharp majorant, the midpoint test, the bridges of the
normal form and the chart, the symmetry and the assembly. The covers and the corner theorem enter
through `sharp_cap`. In the final build each of its twenty lines names exactly these three axioms,
for example `'C4.conj_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]`.

The only `sorry` is in the two statements of `Challenge.lean`, the statement file the comparator
checks the solution against; no other file uses one. No source file uses `admit`, `axiom`,
`native_decide`, `implemented_by`, `extern`, `unsafe`, `partial` or `opaque`, and no `debug` option
is set. The options set in the sources affect elaboration only: `Elab.async false`,
`exponentiation.threshold`, `hygiene false` (for local notation), `maxHeartbeats` and
`maxRecDepth`.

**The certificates.** The 212 piece modules `C4Cert/Gen2_Dir*`, `Gen2_ChA*`, `Gen2_ChB*` and
`Gen2_ChC*` hold 5,957 theorems: 5,924 check, with `decide +kernel`, that the checker accepts a
piece of a cell of a root grid with its hint, 20 check runs of 48 whole cells in the same way, and
13 assemble the pieces and the runs into covers along the recorded splits. The three modules
`C4Cert/CornerBox0`–`2` hold the 36 staged checks of the corner and 3 theorems that assemble them.
`decide +kernel` has the kernel evaluate a Boolean expression, so the certificates add no axiom.
[`C4Cert/Gen2_Cover.lean`](C4Cert/Gen2_Cover.lean) assembles the covers `dir2Cover`, `chACover`,
`chBCover` and `chCCover`, and [`C4/Cap2.lean`](C4/Cap2.lean) proves that every point of `𝒞` with
`P = 0` and `a ≤ 1` lies in a cell of one of their grids or in the corner disc.

**What is proved.** The checker in [`C4Check/`](C4Check) is proved sound in Lean, and the formulas
it evaluates are written once, generically over an `Ops α` class
([`C4Check/Formulas2.lean`](C4Check/Formulas2.lean)). The mathematics uses the same formulas at
`ℝ`, and [`C4/NormalForm2.lean`](C4/NormalForm2.lean) and [`C4/Chart2.lean`](C4/Chart2.lean)
prove that they equal the geometric quantities. So there is no unverified transcription step
between the checked formulas and the theorem.

**What is trusted.** Lean's kernel, including its built-in arithmetic of natural numbers, which
uses GMP. Beyond that, a reader has to check that the definitions in
[`C4/Defs.lean`](C4/Defs.lean) and the statements above say what the paper says.

## Building

The toolchain is `leanprover/lean4:v4.35.0-rc3`, with Mathlib at the matching tag.

```bash
lake exe cache get                 # fetch the Mathlib build cache
lake build C4 Solution Challenge   # the library, the proofs and the statement file
lake env lean Axioms.lean          # print the axioms of the main theorems
```

On the build machine (16 cores, `LEAN_NUM_THREADS=16`, a memory cap of 31 GiB),
`lake build Solution Challenge`, the targets the registry builds, takes 380 s of wall time from a
clean copy with Mathlib's prebuilt cache, and at most 6.6 GB of memory. The root module `C4`, which
`Axioms.lean` imports, adds one file of imports to that build.

## Comparator

[`Challenge.lean`](Challenge.lean) is the statement file. It imports only Mathlib, copies the
definitions that the statements use, and states, without proofs, the two theorems that
`lake comparator` checks: `C4.conj_sharp` and `C4.conj_sharp_strict`.
[`Solution.lean`](Solution.lean) imports their proofs, and [`comparator.json`](comparator.json)
names them. `lake comparator` builds the two modules, checks that the statements and every
definition they reach are the same in the two, that the proofs use only the three standard axioms,
and replays the Solution in Lean's kernel and in the type checker nanoda. In the registry's words,
its runner "additionally attempts con-ron after those mandatory checks pass", and "the entry names
only the independent kernels that accepted its exact export".
[`formalization.yaml`](formalization.yaml) describes the project for the Palomar registry. The
workflow [`.github/workflows/palomar-preflight.yml`](.github/workflows/palomar-preflight.yml) runs
the registry's official verification job, pinned to a commit, on this repository, with the same
kernels and the same comparator check as a submission; its result is a prediction, not a submission.

On the build machine, with the kernels run in the registry's order and settings, the exports take
3.4 s (Challenge) and 15.3 s (Solution, 402 MB). `lake comparator`'s statement and axiom checks
pass on byte-identical copies of these exports: the statements and the definitions they use match
`Challenge.lean`, and the only axioms are `propext`, `Classical.choice` and `Quot.sound`. con-ron
(16 workers), nanoda (4 threads) and leanchecker (Lean's kernel, one thread) each accept the
Solution export: con-ron in 1,085 s with a peak of 9.0 GB, nanoda in 863 s with a peak of 1.8 GB,
and leanchecker in 4,975 s with a peak of 0.9 GB. con-ron accepts 29,607 declarations and nanoda
checks 30,853. Run one after another, as the registry runs them, the three kernels take 6,923 s;
with the exports and the 380 s build, the whole job takes 7,322 s.

## Negative controls

Two negative controls show that the comparator rejects what it must. With a `sorry` in place of a
proof in the Solution, `lake comparator` stops with `error: Illegal axiom detected: 'sorryAx'`.
With the statement of `conj_sharp` changed from `2/3` to `1/2` in the Solution, it stops with
`Challenge and solution theorem statement do not match: 'C4.conj_sharp'`.

## Regenerating the certificates

The hints were found by an unverified search program, which is not published with this repository
and is not part of the trusted base; the kernel checks every certificate, so the hints need not be
trusted.

## Relation to lean4body-uniqueness

The files [`C4/Defs.lean`](C4/Defs.lean), [`C4/Normalize.lean`](C4/Normalize.lean),
[`C4/NormalForm.lean`](C4/NormalForm.lean), [`C4/Chart.lean`](C4/Chart.lean),
[`C4/Dziobek.lean`](C4/Dziobek.lean), [`C4/Majorant.lean`](C4/Majorant.lean), the interval
arithmetic and slope jets of `C4Check` (`Num`, `Jet`, `Formulas`, `Grid`, `Search`) and their
soundness proofs (`NumSound`, `JetSound`, `Carrier`, `ModeSound`, `SearchSound`) are verbatim copies
from version 1 of lean4body-uniqueness. They keep their original comments, so a few of these refer
to modules of version 1 that this repository does not contain. The other files are new:

* the sharp majorant, the midpoint test and its identification with the formulas of the checker
  (`MajorantSharp`, `Midpoint`, `NormalForm2`, `Chart2`);
* the symmetry (`Symmetry`) and the assembly (`Cap2`, `ConjSharp`);
* the normalized test and the new checker (`C4Check/Formulas2`, `C4Check/Search2`,
  `C4Check/Grid2`, `C4/ModeSound2`, `C4/SearchSound2`);
* the fixed-point Taylor models and their soundness (`C4Check/TF`, `C4/TFCommon`, `C4/TFSound`,
  `C4/TFSoundF4`, `C4/Kits`), and the caps (`C4/SharpCap`);
* the corner theorem (`C4Check/CornerTF`, `C4/CornerSound`, `C4/Corner`);
* the certificates in [`C4Cert/`](C4Cert).

The statements compared by `lake comparator` use only definitions of `C4/Defs.lean`, in the same
order as in lean4body-uniqueness.
