module

public import C4.NumSound

@[expose] public section

/-!
# Soundness of `C4Check.CornerTF`

The exact data of a Taylor form are evaluated at a point `(b, g, δ)`:
* `qev p δ = Σ_k p_k δ^k` (the integer coefficients stand for multiples of `1/S`);
* `hev h i n = Σ_k qev h_k · b^(i+k) g^(n-i-k)` (a homogeneous part of degree `n` whose entries
  start at the power `i` of `b`);
* `eev E k = Σ_j hev E_j 0 (k + j)` (the part `E_j` has degree `k + j`);
* `tev hs p M = Σ_k hs_k b^(p+k) g^(M-p-k)` (the tops).

`TFEncAt D b g d u t`: if `t.ok`, the shapes are right and, at the point `(b, g, d)`,
`u = eev t.E 0 / S + tev hs 0 M + h_r m^(M+1)` for some `hs ∈ t.H`, `|h_r| ≤ t.Hr / 2^96`.
Every operation of `tfOps D` preserves this at a point of the box (`*_at`).  (`C4.Corner` packs
these as `OpsSound` for the generic carrier of `C4.TFCommon`.)
-/

namespace C4
namespace CTF

noncomputable section

/-! ## polynomials in `δ` -/

/-- `Σ_k p_k δ^k` -/
def qev : QP → ℝ → ℝ
  | [], _ => 0
  | a :: p, d => (a : ℝ) + d * qev p d

@[simp] theorem qev_nil (d : ℝ) : qev [] d = 0 := rfl
@[simp] theorem qev_cons (a : Int) (p : QP) (d : ℝ) : qev (a :: p) d = a + d * qev p d := rfl

theorem qev_qadd : ∀ (p q : QP) (d : ℝ), qev (qadd p q) d = qev p d + qev q d
  | [], q, d => by simp [qadd]
  | a :: p, [], d => by simp [qadd]
  | a :: p, b :: q, d => by
    simp only [qadd, qev_cons, qev_qadd p q d, Int.cast_add]; ring

theorem qev_qneg : ∀ (p : QP) (d : ℝ), qev (qneg p) d = -qev p d
  | [], d => by simp [qneg]
  | a :: p, d => by simp only [qneg, qev_cons, qev_qneg p d, Int.cast_neg]; ring

theorem qev_qsc (c : Int) : ∀ (p : QP) (d : ℝ), qev (qsc c p) d = c * qev p d
  | [], d => by simp [qsc]
  | a :: p, d => by simp only [qsc, qev_cons, qev_qsc c p d, Int.cast_mul]; ring

theorem qev_qmulR : ∀ (p q : QP) (d : ℝ), qev (qmulR p q) d = qev p d * qev q d
  | [], q, d => by simp [qmulR]
  | a :: p, q, d => by
    simp only [qmulR, qev_qadd, qev_qsc, qev_cons, qev_qmulR p q d, Int.cast_zero]; ring

theorem qev_qtrim : ∀ (p : QP) (d : ℝ), qev (qtrim p) d = qev p d
  | [], d => rfl
  | a :: p, d => by
    have ih := qev_qtrim p d
    rw [qtrim.eq_2]
    rcases hq : qtrim p with _ | ⟨c, cs⟩
    · rw [hq] at ih
      simp only [sel_eq]
      split
      · next ha =>
        have ha' : a = 0 := by simpa using ha
        simp [ha', ← ih]
      · simp [← ih]
    · rw [hq] at ih
      simp only [qev_cons] at ih ⊢
      rw [ih]

theorem qev_qdiv (k : Nat) : ∀ (p : QP) (d : ℝ), (qdiv k p).2 = true →
    qev (qdiv k p).1 d * k = qev p d
  | [], d, _ => by simp [qdiv]
  | a :: p, d, h => by
    simp only [qdiv, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have ih := qev_qdiv k p d h2
    simp only [idiv, beq_iff_eq] at h1 ⊢
    have hdvd : (k : Int) ∣ a := Int.dvd_of_emod_eq_zero h1
    have e1 : Int.ediv a k * k = a := Int.ediv_mul_cancel hdvd
    have e : ((Int.ediv a k : Int) : ℝ) * k = a := by exact_mod_cast e1
    simp only [qev_cons]
    rw [add_mul, e, mul_assoc, ih]

theorem qzero_sound : ∀ (p : QP), qzero p = true → ∀ d, qev p d = 0
  | [], _, d => rfl
  | a :: p, h, d => by
    simp only [qzero, sel_eq] at h
    split at h
    · next ha =>
      have ha' : a = 0 := by simpa using ha
      simp [ha', qzero_sound p h d]
    · exact absurd h Bool.false_ne_true

/-! ## homogeneous parts -/

/-- `Σ_k h_k(δ) b^(i+k) g^(n-i-k)` -/
def hev : Hom → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _ => 0
  | c :: h, i, n, b, g, d => qev c d * (b ^ i * g ^ (n - i)) + hev h (i + 1) n b g d

@[simp] theorem hev_nil (i n : ℕ) (b g d : ℝ) : hev [] i n b g d = 0 := rfl
theorem hev_cons (c : QP) (h : Hom) (i n : ℕ) (b g d : ℝ) :
    hev (c :: h) i n b g d = qev c d * (b ^ i * g ^ (n - i)) + hev h (i + 1) n b g d := rfl

variable {b g d : ℝ}

theorem hev_hadd : ∀ (x y : Hom) (i n : ℕ), hev (hadd x y) i n b g d = hev x i n b g d + hev y i n b g d
  | [], y, i, n => by simp [hadd]
  | a :: x, [], i, n => by simp [hadd]
  | a :: x, c :: y, i, n => by
    simp only [hadd, hev_cons, qev_qadd, hev_hadd x y (i + 1) n]; ring

theorem hev_hneg : ∀ (x : Hom) (i n : ℕ), hev (hneg x) i n b g d = -hev x i n b g d
  | [], i, n => by simp [hneg]
  | a :: x, i, n => by simp only [hneg, hev_cons, qev_qneg, hev_hneg x (i + 1) n]; ring

theorem hev_hscal (a : QP) : ∀ (x : Hom) (i n : ℕ),
    hev (hscal a x) i n b g d = qev a d * hev x i n b g d
  | [], i, n => by simp [hscal]
  | c :: x, i, n => by simp only [hscal, hev_cons, qev_qmulR, hev_hscal a x (i + 1) n]; ring

theorem hev_shiftNil (x : Hom) (i n : ℕ) : hev ([] :: x) i n b g d = hev x (i + 1) n b g d := by
  simp [hev_cons]

/-- multiplying by `b^i g^(n-i)` shifts a homogeneous part -/
theorem hev_shift {i n : ℕ} (hin : i ≤ n) : ∀ (h : Hom) (i2 n2 : ℕ), h.length + i2 ≤ n2 + 1 →
    hev h (i + i2) (n + n2) b g d = b ^ i * g ^ (n - i) * hev h i2 n2 b g d
  | [], i2, n2, _ => by simp
  | c :: h, i2, n2, hl => by
    simp only [List.length_cons] at hl
    have ih := hev_shift hin h (i2 + 1) n2 (by omega)
    rw [hev_cons, hev_cons, show i + i2 + 1 = i + (i2 + 1) by omega, ih,
      show n + n2 - (i + i2) = (n - i) + (n2 - i2) by omega, pow_add, pow_add]
    ring

/-- the product of homogeneous parts -/
theorem hev_hmulR : ∀ (p q : Hom) (i1 i2 n1 n2 : ℕ), p.length + i1 ≤ n1 + 1 →
    q.length + i2 ≤ n2 + 1 →
    hev (hmulR p q) (i1 + i2) (n1 + n2) b g d = hev p i1 n1 b g d * hev q i2 n2 b g d
  | [], q, i1, i2, n1, n2, _, _ => by simp [hmulR]
  | a :: p, q, i1, i2, n1, n2, hp, hq => by
    simp only [List.length_cons] at hp
    have ih := hev_hmulR p q (i1 + 1) i2 n1 n2 (by omega) hq
    simp only [hmulR, hev_hadd, hev_hscal, hev_shiftNil]
    rw [show i1 + i2 + 1 = i1 + 1 + i2 by omega, ih, hev_shift (by omega) q i2 n2 hq, hev_cons]
    ring

theorem hev_hdiv (k : Nat) : ∀ (x : Hom) (i n : ℕ), (hdiv k x).2 = true →
    hev (hdiv k x).1 i n b g d * k = hev x i n b g d
  | [], i, n, _ => by simp [hdiv]
  | a :: x, i, n, h => by
    simp only [hdiv, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    simp only [hev_cons, qev_qtrim]
    rw [add_mul, ← hev_hdiv k x (i + 1) n h2, ← qev_qdiv k a d h1]
    ring

theorem hzero_sound : ∀ (x : Hom), hzero x = true → ∀ i n, hev x i n b g d = 0
  | [], _, i, n => rfl
  | a :: x, h, i, n => by
    simp only [hzero, sel_eq] at h
    split at h
    · next ha => rw [hev_cons, qzero_sound a ha d, hzero_sound x h (i + 1) n]; ring
    · exact absurd h Bool.false_ne_true

/-! ## exact parts -/

/-- `Σ_j hev E_j 0 (k + j)` -/
def eev : Ex → ℕ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | a :: p, k, b, g, d => hev a 0 k b g d + eev p (k + 1) b g d

@[simp] theorem eev_nil (k : ℕ) (b g d : ℝ) : eev [] k b g d = 0 := rfl
theorem eev_cons (a : Hom) (p : Ex) (k : ℕ) (b g d : ℝ) :
    eev (a :: p) k b g d = hev a 0 k b g d + eev p (k + 1) b g d := rfl

/-- the parts have the right lengths (`E_j` has at most `k + j + 1` entries) -/
def WFo : Ex → ℕ → Prop
  | [], _ => True
  | a :: p, k => a.length ≤ k + 1 ∧ WFo p (k + 1)

theorem wfE_sound : ∀ (E : Ex) (k : ℕ), wfE k E = true → WFo E k
  | [], _, _ => trivial
  | a :: p, k, h => by
    simp only [wfE, sel_eq] at h
    split at h
    · next ha => exact ⟨Nat.le_of_ble_eq_true ha, wfE_sound p (k + 1) h⟩
    · exact absurd h Bool.false_ne_true

theorem WFo.mono : ∀ (E : Ex) {k k' : ℕ}, k ≤ k' → WFo E k → WFo E k'
  | [], _, _, _, _ => trivial
  | a :: p, _, _, hk, ⟨h1, h2⟩ => ⟨by omega, WFo.mono p (by omega) h2⟩

theorem eev_eadd : ∀ (x y : Ex) (k : ℕ), eev (eadd x y) k b g d = eev x k b g d + eev y k b g d
  | [], y, k => by simp [eadd]
  | a :: x, [], k => by simp [eadd]
  | a :: x, c :: y, k => by
    simp only [eadd, eev_cons, hev_hadd, eev_eadd x y (k + 1)]; ring

theorem eev_eneg : ∀ (x : Ex) (k : ℕ), eev (eneg x) k b g d = -eev x k b g d
  | [], k => by simp [eneg]
  | a :: x, k => by simp only [eneg, eev_cons, hev_hneg, eev_eneg x (k + 1)]; ring

theorem eev_ediv (q : Nat) : ∀ (x : Ex) (k : ℕ), (ediv q x).2 = true →
    eev (ediv q x).1 k b g d * q = eev x k b g d
  | [], k, _ => by simp [ediv]
  | a :: x, k, h => by
    simp only [ediv, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    simp only [eev_cons]
    rw [add_mul, hev_hdiv q a 0 k h1, eev_ediv q x (k + 1) h2]

theorem ezero_sound : ∀ (x : Ex), ezero x = true → ∀ k, eev x k b g d = 0
  | [], _, k => rfl
  | a :: x, h, k => by
    simp only [ezero, sel_eq] at h
    split at h
    · next ha => rw [eev_cons, hzero_sound a ha 0 k, ezero_sound x h (k + 1)]; ring
    · exact absurd h Bool.false_ne_true

/-- the first `n` parts of `B` -/
def eevT : Ex → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | _, _, 0, _, _, _ => 0
  | [], _, _ + 1, _, _, _ => 0
  | c :: p, m, n + 1, b, g, d => hev c 0 m b g d + eevT p (m + 1) n b g d

/-- the parts of `B` from index `n` on -/
def eevU : Ex → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | B, m, 0, b, g, d => eev B m b g d
  | [], _, _ + 1, _, _, _ => 0
  | _ :: p, m, n + 1, b, g, d => eevU p (m + 1) n b g d

theorem eevT_add_eevU : ∀ (B : Ex) (m n : ℕ), eevT B m n b g d + eevU B m n b g d = eev B m b g d
  | B, m, 0 => by simp [eevT, eevU]
  | [], m, n + 1 => by simp [eevT, eevU]
  | c :: p, m, n + 1 => by
    simp only [eevT, eevU, eev_cons]
    rw [← eevT_add_eevU p (m + 1) n]; ring

/-- `a ⊛ B` on the first `n` parts -/
theorem eev_ehscal (a : Hom) {k : ℕ} (ha : a.length ≤ k + 1) :
    ∀ (n : ℕ) (B : Ex) (m : ℕ), WFo B m →
      eev (ehscal a n B) (k + m) b g d = hev a 0 k b g d * eevT B m n b g d
  | 0, B, m, _ => by simp [ehscal, eevT]
  | n + 1, [], m, _ => by simp [ehscal, eevT]
  | n + 1, c :: B, m, ⟨hc, hB⟩ => by
    simp only [ehscal, eev_cons, eevT]
    rw [show k + m + 1 = k + (m + 1) by omega, eev_ehscal a ha n B (m + 1) hB,
      show (0 : ℕ) = 0 + 0 from rfl, hev_hmulR a c 0 0 k m (by omega) (by omega)]
    ring

/-- the overflow of the product (pairs of parts with total degree `≥ M`) -/
def ovRowS (a : Hom) (d1 : ℕ) : Ex → ℕ → ℕ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _ => 0
  | c :: B, d2, M, b, g, d =>
    (if M ≤ d1 + d2 then hev a 0 d1 b g d * hev c 0 d2 b g d else 0) +
      ovRowS a d1 B (d2 + 1) M b g d

def ovAllS : Ex → ℕ → Ex → ℕ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _, _ => 0
  | a :: A, d1, B, M, b, g, d => ovRowS a d1 B 0 M b g d + ovAllS A (d1 + 1) B M b g d

theorem ovRowS_eq (a : Hom) (d1 : ℕ) : ∀ (B : Ex) (d2 M : ℕ),
    ovRowS a d1 B d2 M b g d = hev a 0 d1 b g d * eevU B d2 (M - (d1 + d2)) b g d
  | [], d2, M => by
    rcases h : M - (d1 + d2) with _ | n <;> simp [ovRowS, eevU]
  | c :: B, d2, M => by
    have ih := ovRowS_eq a d1 B (d2 + 1) M
    simp only [ovRowS, ih]
    by_cases hM : M ≤ d1 + d2
    · rw [if_pos hM, show M - (d1 + d2) = 0 by omega, show M - (d1 + (d2 + 1)) = 0 by omega]
      simp only [eevU, eev_cons]; ring
    · rw [if_neg hM, show M - (d1 + d2) = (M - (d1 + (d2 + 1))) + 1 by omega]
      simp only [eevU]; ring

theorem ovAllS_all : ∀ (A : Ex) (d1 : ℕ) (B : Ex) (M : ℕ), M ≤ d1 →
    ovAllS A d1 B M b g d = eev A d1 b g d * eev B 0 b g d
  | [], _, B, M, _ => by simp [ovAllS]
  | a :: A, d1, B, M, h => by
    simp only [ovAllS, eev_cons, ovRowS_eq, ovAllS_all A (d1 + 1) B M (by omega),
      show M - (d1 + 0) = 0 by omega, eevU]
    ring

/-- the truncated Cauchy product plus the overflow is the product -/
theorem eev_emulR : ∀ (A B : Ex) (k n : ℕ), WFo A k → WFo B 0 →
    eev A k b g d * eev B 0 b g d = eev (emulR n A B) k b g d + ovAllS A k B (k + n) b g d
  | [], B, k, n, _, _ => by cases n <;> simp [emulR, ovAllS]
  | a :: A, B, k, 0, ⟨ha, hA⟩, hB => by
    have hall := ovAllS_all A (k + 1) B k (by omega) (b := b) (g := g) (d := d)
    have hrow := ovRowS_eq a k B 0 k (b := b) (g := g) (d := d)
    rw [show k - (k + 0) = 0 by omega] at hrow
    simp only [eevU] at hrow
    simp only [emulR, eev_nil, ovAllS, eev_cons, Nat.add_zero]
    rw [hrow, hall]
    ring
  | a :: A, B, k, n + 1, ⟨ha, hA⟩, hB => by
    have ih := eev_emulR A B (k + 1) n hA hB
    have h1 : eev (ehscal a (n + 1) B) (k + 0) b g d = hev a 0 k b g d * eevT B 0 (n + 1) b g d :=
      eev_ehscal a ha (n + 1) B 0 hB
    have h2 := eevT_add_eevU B 0 (n + 1) (b := b) (g := g) (d := d)
    have hrow := ovRowS_eq a k B 0 (k + (n + 1)) (b := b) (g := g) (d := d)
    rw [show k + (n + 1) - (k + 0) = n + 1 by omega] at hrow
    change eev (ehscal a (n + 1) B) k b g d = _ at h1
    simp only [emulR, eev_eadd, eev_cons, hev_nil, zero_add, ovAllS]
    rw [h1, hrow, show k + (n + 1) = k + 1 + n by omega]
    linear_combination ih - hev a 0 k b g d * h2


/-! ## fixed point -/

theorem S_pos : (0 : ℝ) < S := by
  have h : 0 < S := by unfold S; norm_num
  exact_mod_cast h

theorem upS_ge (n : Int) : (n : ℝ) / S ≤ val (upS n) := by
  have hS0 : 0 < S := by unfold S; norm_num
  have h2 := S_pos
  rcases n with k | k
  · show ((Int.ofNat k : ℤ) : ℝ) / S ≤ val (Nat.add Bb (I.cdiv (Nat.shiftLeft k 96) S))
    rw [val_addB']
    have h1 : ((Nat.shiftLeft k 96 : ℕ) : ℝ) ≤ (I.cdiv (Nat.shiftLeft k 96) S : ℝ) * S := by
      exact_mod_cast I.le_cdiv_mul _ S hS0
    rw [cast_shl] at h1
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [div_le_div_iff₀ h2 (by positivity)]
    linarith
  · show ((Int.negSucc k : ℤ) : ℝ) / S ≤
      val (Nat.sub Bb (Nat.div (Nat.shiftLeft (Nat.succ k) 96) S))
    have h1 := val_subB (Nat.div (Nat.shiftLeft (Nat.succ k) 96) S)
    have h3 : ((Nat.div (Nat.shiftLeft (Nat.succ k) 96) S : ℕ) : ℝ) ≤
        ((Nat.shiftLeft (Nat.succ k) 96 : ℕ) : ℝ) / S := Nat.cast_div_le
    rw [cast_shl, le_div_iff₀ h2] at h3
    rw [Int.cast_negSucc]
    refine le_trans ?_ h1
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) h2]
    push_cast at h3 ⊢
    linarith

theorem ivS_mem {lo hi : Int} {x : ℝ} (h1 : (lo : ℝ) / S ≤ x) (h2 : x ≤ (hi : ℝ) / S) :
    I.mem x (ivS lo hi) := by
  refine ⟨?_, le_trans h2 (upS_ge hi)⟩
  show -x ≤ val (upS (-lo))
  have := upS_ge (-lo)
  push_cast at this
  rw [neg_div] at this
  linarith

theorem shiftRight_ge (x sh : ℕ) : (x : ℝ) / 2 ^ sh ≤ (Nat.succ (Nat.shiftRight x sh) : ℝ) := by
  show (x : ℝ) / 2 ^ sh ≤ (Nat.succ (x >>> sh) : ℝ)
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.lt_div_mul_add (a := x) (b := 2 ^ sh) (by positivity)
  have h' : (x : ℝ) < (x / 2 ^ sh : ℕ) * 2 ^ sh + 2 ^ sh := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

/-- the tail bound behind `qrng` -/
theorem qtailS_ge (wm s : ℕ) {δ : ℝ} (hd : |δ| ≤ wm / 2 ^ s) :
    ∀ (p : QP) (pw sh acc k : ℕ), |δ| ^ k ≤ pw / 2 ^ sh →
      (acc : ℝ) + |δ ^ k * qev p δ| ≤ qtailS wm s p pw sh acc
  | [], pw, sh, acc, k, _ => by simp [qtailS]
  | a :: p, pw, sh, acc, k, hk => by
    have hk1 : |δ| ^ (k + 1) ≤ (Nat.mul pw wm : ℕ) / 2 ^ (sh + s) := by
      rw [pow_succ, cast_mul, pow_add, mul_div_mul_comm]
      exact mul_le_mul hk hd (abs_nonneg _) (by positivity)
    have ih := qtailS_ge wm s hd p (Nat.mul pw wm) (sh + s)
      (acc + Nat.succ (Nat.shiftRight (Nat.mul a.natAbs pw) sh)) (k + 1) hk1
    simp only [qtailS]
    refine le_trans ?_ ih
    have hsh := shiftRight_ge (Nat.mul a.natAbs pw) sh
    have ha : |δ ^ k * a| ≤ ((Nat.mul a.natAbs pw : ℕ) : ℝ) / 2 ^ sh := by
      rw [abs_mul, abs_pow, cast_mul, Nat.cast_natAbs, Int.cast_abs, mul_div_assoc, mul_comm]
      exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    have e : δ ^ k * qev (a :: p) δ = δ ^ k * a + δ ^ (k + 1) * qev p δ := by
      simp only [qev_cons]; ring
    rw [e]
    push_cast
    calc (acc : ℝ) + |δ ^ k * a + δ ^ (k + 1) * qev p δ|
        ≤ acc + (|δ ^ k * a| + |δ ^ (k + 1) * qev p δ|) := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by push_cast at hsh; linarith

/-- the range of a coefficient polynomial over `|δ| ≤ wm 2^-s` -/
theorem qrng_mem (wm s : ℕ) {δ : ℝ} (hd : |δ| ≤ wm / 2 ^ s) :
    ∀ p : QP, I.mem (qev p δ / S) (qrng wm s p)
  | [] => by simpa [qrng] using I.mem_zero
  | a :: p => by
    have hU := qtailS_ge wm s hd p wm s 0 1 (by simpa using hd)
    simp only [Nat.cast_zero, zero_add, pow_one] at hU
    simp only [qrng]
    have hS := S_pos
    apply ivS_mem
    · rw [div_le_div_iff_of_pos_right hS]
      simp only [qev_cons]
      push_cast
      linarith [neg_abs_le (δ * qev p δ)]
    · rw [div_le_div_iff_of_pos_right hS]
      simp only [qev_cons]
      push_cast
      linarith [le_abs_self (δ * qev p δ)]

theorem imag_ge {x : ℝ} {A : I} (h : I.mem x A) : |x| ≤ (imag A : ℝ) / 2 ^ 96 := by
  obtain ⟨h1, h2⟩ := h
  have hm := sub_le_cast (I.mx A.L A.H) Bb
  rw [cBb] at hm
  have hv : val (I.mx A.L A.H) = max (val A.L) (val A.H) := val_mx A.L A.H
  unfold imag
  have hx : |x| ≤ val (I.mx A.L A.H) := by
    rw [hv]; exact abs_le.mpr ⟨by linarith [le_max_left (val A.L) (val A.H)], le_trans h2 (le_max_right _ _)⟩
  unfold val at hx
  exact le_trans hx (div_le_div_of_nonneg_right hm (by positivity))

theorem mmul_ge (a b : ℕ) : ((a : ℝ) / 2 ^ 96) * ((b : ℝ) / 2 ^ 96) ≤ (mmul a b : ℝ) / 2 ^ 96 := by
  show (a : ℝ) / 2 ^ 96 * ((b : ℝ) / 2 ^ 96) ≤ (I.up (Nat.mul a b) : ℝ) / 2 ^ 96
  have h := up_ge (Nat.mul a b)
  rw [cast_mul] at h
  calc (a : ℝ) / 2 ^ 96 * ((b : ℝ) / 2 ^ 96) = (a * b / 2 ^ 96) / 2 ^ 96 := by field_simp
    _ ≤ _ := by gcongr

theorem mmul_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : mmul a b ≤ mmul a' b' := by
  show (a * b + RND) >>> 96 ≤ (a' * b' + RND) >>> 96
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  apply Nat.div_le_div_right
  show a * b + RND ≤ a' * b' + RND
  have := Nat.mul_le_mul ha hb
  omega

/-! ## the box -/

/-- `ρ = 2^-rb` -/
def Dom.rho (D : Dom) : ℝ := 1 / 2 ^ D.rb
/-- `w = wm 2^-s` -/
def Dom.wd (D : Dom) : ℝ := D.wm / 2 ^ D.s

structure InBox (D : Dom) (b g d : ℝ) : Prop where
  b0 : 0 ≤ b
  b1 : b ≤ D.rho
  g1 : |g| ≤ D.rho
  d1 : |d| ≤ D.wd

theorem Dom.rho_pos (D : Dom) : 0 < D.rho := by unfold Dom.rho; positivity
theorem Dom.rho_le_one (D : Dom) : D.rho ≤ 1 := by
  unfold Dom.rho; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

theorem rpow_ge (D : Dom) (k : ℕ) : D.rho ^ k ≤ (rpow D k : ℝ) / 2 ^ 96 := by
  unfold rpow Dom.rho
  rw [sel_eq]
  split
  · next h =>
    have h' : D.rb * k ≤ 96 := Nat.le_of_ble_eq_true h
    rw [cast_shl, Nat.cast_one, one_mul, div_pow, one_pow, ← pow_mul]
    have e : Nat.sub 96 (Nat.mul D.rb k) + D.rb * k = 96 := by
      show 96 - D.rb * k + D.rb * k = 96; omega
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add, e]
  · next h =>
    have h' : 96 < D.rb * k := by
      have : ¬ (D.rb * k ≤ 96) := fun hh => h (Nat.ble_eq_true_of_le hh)
      omega
    rw [div_pow, one_pow, ← pow_mul, Nat.cast_one]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) h'.le

/-- `m = max b |g|` -/
def mx (b g : ℝ) : ℝ := max b |g|

theorem mx_nonneg {b g : ℝ} (hb : 0 ≤ b) : 0 ≤ mx b g := le_max_of_le_left hb

theorem mx_le {D : Dom} {b g d : ℝ} (hz : InBox D b g d) : mx b g ≤ D.rho :=
  max_le hz.b1 hz.g1

theorem abs_mono_le {b g : ℝ} (hb : 0 ≤ b) (i n : ℕ) : |b ^ i * g ^ n| ≤ mx b g ^ (i + n) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add, abs_of_nonneg hb]
  exact mul_le_mul (pow_le_pow_left₀ hb (le_max_left _ _) _)
    (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _) (by positivity)
    (pow_nonneg (mx_nonneg hb) _)

theorem mono_mem {D : Dom} {b g d : ℝ} (hz : InBox D b g d) (i n : ℕ) :
    I.mem (b ^ i * g ^ n) (mono D i n) := by
  unfold mono
  simp only [sel_eq]
  have hv : D.rho ^ (i + n) ≤ val (Nat.add Bb (rpow D (i + n))) := by
    rw [val_addB']; exact rpow_ge D (i + n)
  have hab : |b ^ i * g ^ n| ≤ D.rho ^ (i + n) :=
    le_trans (abs_mono_le hz.b0 i n) (pow_le_pow_left₀ (mx_nonneg hz.b0) (mx_le hz) _)
  split
  · next h =>
    have : i + n = 0 := Nat.eq_of_beq_eq_true h
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ n = 0 := by omega
    simpa using I.mem_one
  · split
    · exact ⟨by linarith [neg_abs_le (b ^ i * g ^ n)], by linarith [le_abs_self (b ^ i * g ^ n)]⟩
    · next h1 h2 =>
      have hn : n % 2 = 0 := by
        have : ¬ (n % 2 = 1) := fun e => h2 (by simp [e])
        omega
      have hpos : 0 ≤ b ^ i * g ^ n := by
        apply mul_nonneg (pow_nonneg hz.b0 _)
        obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
        rw [hk, pow_mul]; positivity
      refine ⟨?_, by linarith [le_abs_self (b ^ i * g ^ n)]⟩
      show -(b ^ i * g ^ n) ≤ val Bb
      rw [val_Bb]; linarith


/-! ## tops, ranges and magnitudes -/

/-- `Σ_k hs_k b^(p+k) g^(M-p-k)` -/
def tev : List ℝ → ℕ → ℕ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | h :: hs, p, M, b, g => h * (b ^ p * g ^ (M - p)) + tev hs (p + 1) M b g

@[simp] theorem tev_nil (p M : ℕ) (b g : ℝ) : tev [] p M b g = 0 := rfl
theorem tev_cons (h : ℝ) (hs : List ℝ) (p M : ℕ) (b g : ℝ) :
    tev (h :: hs) p M b g = h * (b ^ p * g ^ (M - p)) + tev hs (p + 1) M b g := rfl

/-- pointwise sum (the longer tail is kept) -/
def ladd : List ℝ → List ℝ → List ℝ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, c :: q => (a + c) :: ladd p q

theorem tev_ladd : ∀ (xs ys : List ℝ) (p M : ℕ) (b g : ℝ),
    tev (ladd xs ys) p M b g = tev xs p M b g + tev ys p M b g
  | [], ys, p, M, b, g => by simp [ladd]
  | x :: xs, [], p, M, b, g => by simp [ladd]
  | x :: xs, y :: ys, p, M, b, g => by
    simp only [ladd, tev_cons, tev_ladd xs ys (p + 1) M b g]; ring

theorem mem_ladd : ∀ {xs ys : List ℝ} {X Y : List I}, List.Forall₂ (fun x A => I.mem x A) xs X →
    List.Forall₂ (fun x A => I.mem x A) ys Y → List.Forall₂ (fun x A => I.mem x A) (ladd xs ys) (iadd X Y)
  | [], _, [], _, .nil, hy => by simpa [ladd, iadd] using hy
  | _ :: _, [], _ :: _, [], hx, .nil => by simpa [ladd, iadd] using hx
  | x :: xs, y :: ys, A :: X, B :: Y, .cons h1 h2, .cons h3 h4 =>
    .cons (I.mem_add h1 h3) (mem_ladd h2 h4)

theorem tev_neg : ∀ (xs : List ℝ) (p M : ℕ) (b g : ℝ),
    tev (xs.map (fun x => -x)) p M b g = -tev xs p M b g
  | [], p, M, b, g => by simp
  | x :: xs, p, M, b, g => by simp only [List.map_cons, tev_cons, tev_neg xs (p + 1) M b g]; ring

theorem mem_ineg : ∀ {xs : List ℝ} {X : List I}, List.Forall₂ (fun x A => I.mem x A) xs X →
    List.Forall₂ (fun x A => I.mem x A) (xs.map (fun x => -x)) (ineg X)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (I.mem_neg h1) (mem_ineg h2)

/-- the scaled list `c · xs` -/
theorem tev_scal (c : ℝ) : ∀ (xs : List ℝ) (p M : ℕ) (b g : ℝ),
    tev (xs.map (fun x => c * x)) p M b g = c * tev xs p M b g
  | [], p, M, b, g => by simp
  | x :: xs, p, M, b, g => by simp only [List.map_cons, tev_cons, tev_scal c xs (p + 1) M b g]; ring

theorem mem_iscal {c : ℝ} {C : I} (hc : I.mem c C) : ∀ {xs : List ℝ} {X : List I},
    List.Forall₂ (fun x A => I.mem x A) xs X →
    List.Forall₂ (fun x A => I.mem x A) (xs.map (fun x => c * x)) (iscal C X)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (I.mem_mul hc h1) (mem_iscal hc h2)

/-- the zero tops -/
def zeros : ℕ → List ℝ
  | 0 => [0]
  | n + 1 => 0 :: zeros n

theorem tev_zeros : ∀ (n p M : ℕ) (b g : ℝ), tev (zeros n) p M b g = 0
  | 0, p, M, b, g => by simp [zeros, tev_cons]
  | n + 1, p, M, b, g => by simp only [zeros, tev_cons, tev_zeros n (p + 1) M b g]; ring

theorem mem_zeros : ∀ n, List.Forall₂ (fun x A => I.mem x A) (zeros n) (zeroH n)
  | 0 => .cons I.mem_zero .nil
  | n + 1 => .cons I.mem_zero (mem_zeros n)

theorem zeroH_length : ∀ n, (zeroH n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [zeroH, zeroH_length n]

section box
variable {D : Dom} {b g d : ℝ}

theorem hRange_mem (hz : InBox D b g d) : ∀ (h : Hom) (i n : ℕ),
    I.mem (hev h i n b g d / S) (hRange D n i (hrng D h))
  | [], i, n => by simpa [hrng, hRange] using I.mem_zero
  | c :: h, i, n => by
    simp only [hrng, hRange, hev_cons]
    rw [add_div, mul_div_right_comm]
    exact I.mem_add (I.mem_mul (qrng_mem D.wm D.s hz.d1 c) (mono_mem hz i (n - i)))
      (hRange_mem hz h (i + 1) n)

theorem eRange_mem (hz : InBox D b g d) : ∀ (E : Ex) (k : ℕ),
    I.mem (eev E k b g d / S) (eRange D k (erng D E))
  | [], k => by simpa [erng, eRange] using I.mem_zero
  | a :: E, k => by
    simp only [erng, eRange, eev_cons]
    rw [add_div]
    exact I.mem_add (hRange_mem hz a 0 k) (eRange_mem hz E (k + 1))

theorem topRange_mem (hz : InBox D b g d) : ∀ {hs : List ℝ} {H : List I} (p : ℕ),
    List.Forall₂ (fun x A => I.mem x A) hs H → I.mem (tev hs p D.M b g) (topRange D p H)
  | [], [], p, .nil => by simpa [topRange] using I.mem_zero
  | _ :: _, _ :: _, p, .cons h1 h2 => by
    simp only [topRange, tev_cons]
    exact I.mem_add (I.mem_mul h1 (mono_mem hz p (D.M - p))) (topRange_mem hz (p + 1) h2)

/-- the radial part is bounded by `Hr ρ^(M+1)` -/
theorem radial_le (hz : InBox D b g d) {hr : ℝ} {Hr : ℕ} (hh : |hr| ≤ (Hr : ℝ) / 2 ^ 96) (k : ℕ) :
    |hr * mx b g ^ k| ≤ (mmul Hr (rpow D k) : ℝ) / 2 ^ 96 := by
  rw [abs_mul, abs_pow, abs_of_nonneg (mx_nonneg hz.b0)]
  calc |hr| * mx b g ^ k ≤ ((Hr : ℝ) / 2 ^ 96) * ((rpow D k : ℝ) / 2 ^ 96) :=
        mul_le_mul hh (le_trans (pow_le_pow_left₀ (mx_nonneg hz.b0) (mx_le hz) k) (rpow_ge D k))
          (pow_nonneg (mx_nonneg hz.b0) k) (by positivity)
    _ ≤ _ := mmul_ge _ _

/-- the range of a Taylor form, of `u` and of its exact-plus-tops part -/
theorem range_mem (hz : InBox D b g d) {t : TF} {hs : List ℝ} {hr : ℝ}
    (hH : List.Forall₂ (fun x A => I.mem x A) hs t.H) (hh : |hr| ≤ (t.Hr : ℝ) / 2 ^ 96) :
    I.mem (eev t.E 0 b g d / S + tev hs 0 D.M b g + hr * mx b g ^ (D.M + 1)) (t.range D) ∧
    I.mem (eev t.E 0 b g d / S + tev hs 0 D.M b g) (t.range D) := by
  have he := I.mem_add (eRange_mem hz t.E 0) (topRange_mem hz 0 hH)
  have hrad := radial_le hz hh (D.M + 1)
  refine ⟨I.mem_widen he hrad, ?_⟩
  have h0 : |(0 : ℝ)| ≤ (mmul t.Hr (rpow D (D.M + 1)) : ℝ) / 2 ^ 96 := by
    rw [abs_zero]; positivity
  have h' := I.mem_widen he h0
  rw [add_zero] at h'
  exact h'

end box

/-! ## the semantics -/

/-- `t` encloses the value `u` at the point `(b, g, d)` -/
def TFEncAt (D : Dom) (b g d : ℝ) (u : ℝ) (t : TF) : Prop :=
  t.ok = true → WFo t.E 0 ∧ t.H.length = D.M + 1 ∧
    ∃ hs : List ℝ, ∃ hr : ℝ,
      List.Forall₂ (fun x A => I.mem x A) hs t.H ∧ |hr| ≤ (t.Hr : ℝ) / 2 ^ 96 ∧
      u = eev t.E 0 b g d / S + tev hs 0 D.M b g + hr * mx b g ^ (D.M + 1)

theorem shape_sound {D : Dom} {E : Ex} {H : List I} (h : TF.shape D E H = true) :
    WFo E 0 ∧ H.length = D.M + 1 := by
  unfold TF.shape at h
  rw [sel_eq] at h
  split at h
  · next h1 => exact ⟨wfE_sound E 0 h1, Nat.eq_of_beq_eq_true h⟩
  · exact absurd h Bool.false_ne_true

theorem mk'_ok {D : Dom} {E : Ex} {H : List I} {Hr : ℕ} {ok : Bool}
    (h : (TF.mk' D E H Hr ok).ok = true) : ok = true ∧ WFo E 0 ∧ H.length = D.M + 1 := by
  have h' : (sel ok (TF.shape D E H) false) = true := h
  rw [sel_eq] at h'
  split at h'
  · next h1 => exact ⟨h1, shape_sound h'⟩
  · exact absurd h' Bool.false_ne_true

theorem cst_at (D : Dom) (b g d : ℝ) (q : QP) : TFEncAt D b g d (qev q d / S) (TF.cst D q) := by
  intro _
  refine ⟨⟨by simp, trivial⟩, zeroH_length D.M, ⟨zeros D.M, 0, mem_zeros D.M,
    by rw [abs_zero]; positivity, ?_⟩⟩
  simp [TF.cst, eev_cons, hev_cons, tev_zeros]

theorem varB_at (D : Dom) (b g d : ℝ) : TFEncAt D b g d b (TF.varB D) := by
  intro _
  refine ⟨⟨by simp, by simp, trivial⟩, zeroH_length D.M, ⟨zeros D.M, 0, mem_zeros D.M,
    by rw [abs_zero]; positivity, ?_⟩⟩
  simp only [TF.varB, eev_cons, hev_cons, eev_nil, hev_nil, tev_zeros, qev_cons, qev_nil,
    Int.cast_natCast]
  have hS := S_pos
  field_simp
  ring

theorem varG_at (D : Dom) (b g d : ℝ) : TFEncAt D b g d g (TF.varG D) := by
  intro _
  refine ⟨⟨by simp, by simp, trivial⟩, zeroH_length D.M, ⟨zeros D.M, 0, mem_zeros D.M,
    by rw [abs_zero]; positivity, ?_⟩⟩
  simp only [TF.varG, eev_cons, hev_cons, eev_nil, hev_nil, tev_zeros, qev_cons, qev_nil,
    Int.cast_natCast]
  have hS := S_pos
  field_simp
  ring

theorem hneg_length : ∀ (a : Hom), (hneg a).length = a.length
  | [] => rfl
  | _ :: a => by simp [hneg, hneg_length a]

theorem WFo_eneg : ∀ (E : Ex) (k : ℕ), WFo E k → WFo (eneg E) k
  | [], _, _ => trivial
  | a :: E, k, ⟨h1, h2⟩ => ⟨by rw [hneg_length]; exact h1, WFo_eneg E (k + 1) h2⟩

theorem ineg_length : ∀ (X : List I), (ineg X).length = X.length
  | [] => rfl
  | _ :: X => by simp [ineg, ineg_length X]

section ops
variable {D : Dom} {b g d : ℝ}

theorem neg_at {u : ℝ} {t : TF} (h : TFEncAt D b g d u t) : TFEncAt D b g d (-u) t.neg := by
  intro hok
  obtain ⟨hw, hl, hs, hr, hH, hh, he⟩ := h hok
  refine ⟨WFo_eneg _ 0 hw, by simp [TF.neg, ineg_length, hl], hs.map (fun x => -x), -hr,
    mem_ineg hH, by simpa [TF.neg] using hh, ?_⟩
  simp only [TF.neg, eev_eneg, tev_neg, he]
  ring

theorem add_at {u v : ℝ} {t1 t2 : TF} (h1 : TFEncAt D b g d u t1) (h2 : TFEncAt D b g d v t2) :
    TFEncAt D b g d (u + v) (TF.add D t1 t2) := by
  intro hok
  obtain ⟨hok', hw, hl⟩ := mk'_ok hok
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨-, -, hs1, hr1, hH1, hh1, he1⟩ := h1 hok'.1
  obtain ⟨-, -, hs2, hr2, hH2, hh2, he2⟩ := h2 hok'.2
  refine ⟨hw, hl, ladd hs1 hs2, hr1 + hr2, mem_ladd hH1 hH2, ?_, ?_⟩
  · show |hr1 + hr2| ≤ ((Nat.add t1.Hr t2.Hr : ℕ) : ℝ) / 2 ^ 96
    rw [cast_add, add_div]
    exact le_trans (abs_add_le _ _) (add_le_add hh1 hh2)
  · show u + v = eev (eadd t1.E t2.E) 0 b g d / S + tev (ladd hs1 hs2) 0 D.M b g +
      (hr1 + hr2) * mx b g ^ (D.M + 1)
    rw [eev_eadd, tev_ladd, he1, he2]
    ring

theorem sub_at {u v : ℝ} {t1 t2 : TF} (h1 : TFEncAt D b g d u t1) (h2 : TFEncAt D b g d v t2) :
    TFEncAt D b g d (u - v) (TF.sub D t1 t2) := by
  rw [sub_eq_add_neg]
  exact add_at h1 (neg_at h2)

end ops

/-! ## magnitudes and the overflow of products -/

section mul
variable {D : Dom} {b g d : ℝ}

theorem off_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) / 2 ^ 96 := div_nonneg (Nat.cast_nonneg _) (by norm_num)

theorem mono_le_mx (hz : InBox D b g d) {n : ℕ} (a c : ℕ) (h : n ≤ a + c) :
    |b ^ a * g ^ c| ≤ mx b g ^ n :=
  le_trans (abs_mono_le hz.b0 a c)
    (pow_le_pow_of_le_one (mx_nonneg hz.b0) (le_trans (mx_le hz) D.rho_le_one) h)

/-- `|hev h i n / S| ≤ (Σ |R_k|) m^n` -/
theorem hev_mag (hz : InBox D b g d) : ∀ (h : Hom) (i n : ℕ),
    |hev h i n b g d / S| ≤ (imagSum (hrng D h) : ℝ) / 2 ^ 96 * mx b g ^ n
  | [], i, n => by simp [imagSum, hrng]
  | c :: h, i, n => by
    simp only [hev_cons, hrng, imagSum]
    rw [cast_add]
    have h1 := imag_ge (qrng_mem D.wm D.s hz.d1 c)
    have h2 := mono_le_mx hz (n := n) i (n - i) (by omega)
    have h3 : |qev c d * (b ^ i * g ^ (n - i)) / S| ≤ (imag (qrng D.wm D.s c) : ℝ) / 2 ^ 96 *
        mx b g ^ n := by
      rw [mul_comm, mul_div_assoc, abs_mul, mul_comm]
      exact mul_le_mul h1 h2 (abs_nonneg _) (off_nonneg _)
    have ih := hev_mag hz h (i + 1) n
    calc |(qev c d * (b ^ i * g ^ (n - i)) + hev h (i + 1) n b g d) / S|
        = |qev c d * (b ^ i * g ^ (n - i)) / S + hev h (i + 1) n b g d / S| := by rw [add_div]
      _ ≤ |qev c d * (b ^ i * g ^ (n - i)) / S| + |hev h (i + 1) n b g d / S| := abs_add_le _ _
      _ ≤ (imag (qrng D.wm D.s c) : ℝ) / 2 ^ 96 * mx b g ^ n +
          (imagSum (hrng D h) : ℝ) / 2 ^ 96 * mx b g ^ n := add_le_add h3 ih
      _ = _ := by rw [add_div, add_mul]

/-- the tops are bounded by `(Σ |H_p|) m^M` -/
theorem tev_mag (hz : InBox D b g d) {M : ℕ} : ∀ {hs : List ℝ} {H : List I} (p : ℕ),
    List.Forall₂ (fun x A => I.mem x A) hs H → |tev hs p M b g| ≤ (imagSum H : ℝ) / 2 ^ 96 * mx b g ^ M
  | [], [], p, .nil => by simp [imagSum]
  | x :: xs, A :: H, p, .cons h1 h2 => by
    simp only [tev_cons, imagSum]
    rw [cast_add, add_div, add_mul]
    have hx := imag_ge h1
    have hm := mono_le_mx hz (n := M) p (M - p) (by omega)
    calc |x * (b ^ p * g ^ (M - p)) + tev xs (p + 1) M b g|
        ≤ |x * (b ^ p * g ^ (M - p))| + |tev xs (p + 1) M b g| := abs_add_le _ _
      _ ≤ _ := by
        gcongr
        · rw [abs_mul]; exact mul_le_mul hx hm (abs_nonneg _) (by positivity)
        · exact tev_mag hz (p + 1) h2

/-- the parts of degree `≥ k ≥ 1` are bounded by `m · k1` -/
theorem eev_mag1 (hz : InBox D b g d) : ∀ (E : Ex) (k : ℕ), 1 ≤ k →
    |eev E k b g d / S| ≤ mx b g * ((k1 D k (kcomp (erng D E)) : ℝ) / 2 ^ 96)
  | [], k, _ => by simp [erng, kcomp, k1]
  | a :: E, k, hk => by
    simp only [eev_cons, erng, kcomp, k1, sel_eq]
    rw [if_neg (by simp; omega), cast_add]
    have ha := hev_mag hz a 0 k
    have hm : mx b g ^ k ≤ mx b g * D.rho ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm, Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mx_nonneg hz.b0) (mx_le hz) _)
        (mx_nonneg hz.b0)
    have hr := rpow_ge D (k - 1)
    have hmm := mmul_ge (imagSum (hrng D a)) (rpow D (k - 1))
    have ih := eev_mag1 hz E (k + 1) (by omega)
    have hA : |hev a 0 k b g d / S| ≤
        mx b g * ((mmul (imagSum (hrng D a)) (rpow D (k - 1)) : ℝ) / 2 ^ 96) := by
      calc |hev a 0 k b g d / S| ≤ (imagSum (hrng D a) : ℝ) / 2 ^ 96 * mx b g ^ k := ha
        _ ≤ (imagSum (hrng D a) : ℝ) / 2 ^ 96 * (mx b g * ((rpow D (k - 1) : ℝ) / 2 ^ 96)) := by
          apply mul_le_mul_of_nonneg_left _ (off_nonneg _)
          exact le_trans hm (mul_le_mul_of_nonneg_left hr (mx_nonneg hz.b0))
        _ = mx b g * ((imagSum (hrng D a) : ℝ) / 2 ^ 96 * ((rpow D (k - 1) : ℝ) / 2 ^ 96)) := by
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmm (mx_nonneg hz.b0)
    calc |(hev a 0 k b g d + eev E (k + 1) b g d) / S|
        = |hev a 0 k b g d / S + eev E (k + 1) b g d / S| := by rw [add_div]
      _ ≤ |hev a 0 k b g d / S| + |eev E (k + 1) b g d / S| := abs_add_le _ _
      _ ≤ mx b g * ((mmul (imagSum (hrng D a)) (rpow D (k - 1)) : ℝ) / 2 ^ 96) +
          mx b g * ((k1 D (k + 1) (kcomp (erng D E)) : ℝ) / 2 ^ 96) := add_le_add hA ih
      _ = _ := by rw [add_div, mul_add]

/-- a quantity bounded by `K m^(M+1)` is a radial top of magnitude `K` -/
theorem radial_of {t K : ℝ} {M : ℕ} (hb : 0 ≤ b) (hK : 0 ≤ K) (h : |t| ≤ K * mx b g ^ (M + 1)) :
    ∃ hr, |hr| ≤ K ∧ t = hr * mx b g ^ (M + 1) := by
  by_cases hm : mx b g = 0
  · refine ⟨0, by rw [abs_zero]; exact hK, ?_⟩
    rw [hm, zero_pow (Nat.succ_ne_zero M), mul_zero] at h ⊢
    exact abs_nonpos_iff.mp h
  · have hp : 0 < mx b g ^ (M + 1) := pow_pos (lt_of_le_of_ne (mx_nonneg hb) (Ne.symm hm)) _
    refine ⟨t / mx b g ^ (M + 1), ?_, by rw [div_mul_cancel₀ _ hp.ne']⟩
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact h

theorem addAt_length : ∀ (p : ℕ) (Y : I) (H : List I), (addAt p Y H).length = H.length
  | p, _, [] => by cases p <;> rfl
  | 0, Y, A :: H => by
    show (A.add Y :: H).length = (A :: H).length
    rw [List.length_cons, List.length_cons]
  | p + 1, Y, A :: H => by
    show (A :: addAt p Y H).length = (A :: H).length
    rw [List.length_cons, List.length_cons, addAt_length p Y H]

theorem addAt_sem {M : ℕ} {y : ℝ} {Y : I} (hy : I.mem y Y) : ∀ (p q : ℕ) {hs : List ℝ}
    {H : List I}, List.Forall₂ (fun x A => I.mem x A) hs H → p < H.length →
    ∃ hs', List.Forall₂ (fun x A => I.mem x A) hs' (addAt p Y H) ∧
      tev hs' q M b g = tev hs q M b g + y * (b ^ (q + p) * g ^ (M - (q + p)))
  | _, _, [], [], .nil, hp => absurd hp (by simp)
  | 0, q, x :: xs, A :: H, .cons h1 h2, _ =>
    ⟨(x + y) :: xs, .cons (I.mem_add h1 hy) h2, by simp only [tev_cons, Nat.add_zero]; ring⟩
  | p + 1, q, x :: xs, A :: H, .cons h1 h2, hp => by
    obtain ⟨hs', h3, h4⟩ := addAt_sem (M := M) hy p (q + 1) h2 (by simpa using hp)
    refine ⟨x :: hs', .cons h1 h3, ?_⟩
    rw [tev_cons, tev_cons, h4, show q + 1 + p = q + (p + 1) by omega]
    ring

theorem ovInner_length (A : I) (i1 : ℕ) : ∀ (i2 : ℕ) (rs H : List I),
    (ovInner A i1 i2 rs H).length = H.length
  | _, [], H => rfl
  | i2, r :: rs, H => by simp [ovInner, ovInner_length A i1 (i2 + 1) rs, addAt_length]

theorem ovOuter_length (r2 : List I) : ∀ (i1 : ℕ) (rs H : List I),
    (ovOuter r2 i1 rs H).length = H.length
  | _, [], H => rfl
  | i1, a :: rs, H => by simp [ovOuter, ovOuter_length r2 (i1 + 1) rs, ovInner_length]

/-- one row of the degree-`M` overflow: `x` times the part `c` shifted by `i1` -/
theorem ovInner_sem (hz : InBox D b g d) {x : ℝ} {A : I} (hx : I.mem x A) (i1 : ℕ) :
    ∀ (c : Hom) (i2 : ℕ) {hs : List ℝ} {H : List I}, List.Forall₂ (fun x A => I.mem x A) hs H →
    i1 + i2 + c.length ≤ H.length →
    ∃ hs', List.Forall₂ (fun x A => I.mem x A) hs' (ovInner A i1 i2 (hrng D c) H) ∧
      tev hs' 0 D.M b g = tev hs 0 D.M b g + x * (hev c (i1 + i2) D.M b g d / S)
  | [], i2, hs, H, hH, _ => ⟨hs, by simpa [hrng, ovInner] using hH, by simp⟩
  | c0 :: c, i2, hs, H, hH, hl => by
    simp only [List.length_cons] at hl
    have hy := I.mem_mul hx (qrng_mem D.wm D.s hz.d1 c0)
    obtain ⟨hs1, h1, e1⟩ := addAt_sem (M := D.M) (b := b) (g := g) hy (i1 + i2) 0 hH (by omega)
    obtain ⟨hs2, h2, e2⟩ := ovInner_sem hz hx i1 c (i2 + 1) h1 (by rw [addAt_length]; omega)
    refine ⟨hs2, by simpa [hrng, ovInner] using h2, ?_⟩
    rw [e2, e1, hev_cons, show i1 + (i2 + 1) = i1 + i2 + 1 by omega, Nat.zero_add]
    field_simp
    ring

/-- the semantic counterpart of `ovOuter`: `Σ_j (a_j/S) · hev c (i1 + j) M / S` -/
def ovOS (c : Hom) (M : ℕ) (b g d : ℝ) : Hom → ℕ → ℝ
  | [], _ => 0
  | a0 :: a, i1 => qev a0 d / S * (hev c i1 M b g d / S) + ovOS c M b g d a (i1 + 1)

theorem ovOuter_sem (hz : InBox D b g d) (c : Hom) : ∀ (a : Hom) (i1 : ℕ) {hs : List ℝ}
    {H : List I}, List.Forall₂ (fun x A => I.mem x A) hs H →
    i1 + a.length + c.length ≤ H.length + 1 →
    ∃ hs', List.Forall₂ (fun x A => I.mem x A) hs' (ovOuter (hrng D c) i1 (hrng D a) H) ∧
      tev hs' 0 D.M b g = tev hs 0 D.M b g + ovOS c D.M b g d a i1
  | [], i1, hs, H, hH, _ => ⟨hs, by simpa [hrng, ovOuter] using hH, by simp [ovOS]⟩
  | a0 :: a, i1, hs, H, hH, hl => by
    simp only [List.length_cons] at hl
    by_cases hc : c.length = 0
    · -- `c = []`: nothing is added
      have hc' : c = [] := List.eq_nil_of_length_eq_zero hc
      subst hc'
      obtain ⟨hs2, h2, e2⟩ := ovOuter_sem hz [] a (i1 + 1) (hs := hs)
        (by simpa [hrng, ovInner] using hH) (by simp; omega)
      refine ⟨hs2, by simpa [hrng, ovOuter, ovInner] using h2, ?_⟩
      rw [e2]; simp [ovOS]
    · obtain ⟨hs1, h1, e1⟩ := ovInner_sem hz (qrng_mem D.wm D.s hz.d1 a0) i1 c 0 hH (by omega)
      obtain ⟨hs2, h2, e2⟩ := ovOuter_sem hz c a (i1 + 1) h1
        (by rw [ovInner_length]; omega)
      refine ⟨hs2, by simpa [hrng, ovOuter] using h2, ?_⟩
      rw [e2, e1, Nat.add_zero]
      simp only [ovOS]
      ring

/-- `ovOS` is the product of two parts of total degree `M` -/
theorem ovOS_eq {d1 d2 : ℕ} (c : Hom) (hc : c.length ≤ d2 + 1) : ∀ (a : Hom) (i : ℕ),
    a.length + i ≤ d1 + 1 →
    ovOS c (d1 + d2) b g d a i = hev a i d1 b g d * hev c 0 d2 b g d / (S : ℝ) ^ 2
  | [], i, _ => by simp [ovOS]
  | a0 :: a, i, hl => by
    simp only [List.length_cons] at hl
    simp only [ovOS, hev_cons]
    rw [ovOS_eq c hc a (i + 1) (by omega),
      show hev c i (d1 + d2) b g d = hev c (i + 0) (d1 + d2) b g d from rfl,
      hev_shift (by omega) c 0 d2 (by omega)]
    have hS := S_pos
    field_simp <;> ring

/-- the representation of a partial sum by tops and a radial magnitude -/
def Rep (D : Dom) (b g : ℝ) (acc : List I × ℕ) (X : ℝ) : Prop :=
  ∃ hs : List ℝ, ∃ hr : ℝ, List.Forall₂ (fun x A => I.mem x A) hs acc.1 ∧
    |hr| ≤ (acc.2 : ℝ) / 2 ^ 96 ∧ X = tev hs 0 D.M b g + hr * mx b g ^ (D.M + 1)

theorem ovRow_sem (hz : InBox D b g d) (a : Hom) (d1 : ℕ) (ha : a.length ≤ d1 + 1) :
    ∀ (B : Ex) (d2 : ℕ) (acc : List I × ℕ) (X : ℝ), WFo B d2 → acc.1.length = D.M + 1 →
    Rep D b g acc X →
    (ovRow D d1 (hrng D a) (imagSum (hrng D a)) d2 (erng D B) (kcomp (erng D B)) acc).1.length =
        D.M + 1 ∧
      Rep D b g (ovRow D d1 (hrng D a) (imagSum (hrng D a)) d2 (erng D B) (kcomp (erng D B)) acc)
        (X + ovRowS a d1 B d2 D.M b g d / (S : ℝ) ^ 2)
  | [], d2, acc, X, _, hl, hX => by
    refine ⟨hl, ?_⟩
    simpa [erng, kcomp, ovRow, ovRowS] using hX
  | c :: B, d2, acc, X, ⟨hc, hB⟩, hl, ⟨hs, hr, hH, hh, hXe⟩ => by
    simp only [erng, kcomp, ovRow, ovRowS]
    -- the effect of the pair `(d1, d2)`
    have step : ∃ acc' : List I × ℕ, acc' = (sel (Nat.beq (d1 + d2) D.M)
        (ovOuter (hrng D c) 0 (hrng D a) acc.1, acc.2)
        (sel (Nat.ble (D.M + 1) (d1 + d2))
          (acc.1, Nat.add acc.2 (mmul (mmul (imagSum (hrng D a)) (imagSum (hrng D c)))
            (rpow D (d1 + d2 - (D.M + 1))))) acc)) ∧ acc'.1.length = D.M + 1 ∧
        Rep D b g acc' (X + (if D.M ≤ d1 + d2 then hev a 0 d1 b g d * hev c 0 d2 b g d else 0) /
          (S : ℝ) ^ 2) := by
      refine ⟨_, rfl, ?_⟩
      simp only [sel_eq]
      split
      · next he =>
        have hM : d1 + d2 = D.M := Nat.eq_of_beq_eq_true he
        obtain ⟨hs', h1, e1⟩ := ovOuter_sem hz c a 0 hH (by omega)
        refine ⟨by rw [ovOuter_length]; exact hl, hs', hr, h1, hh, ?_⟩
        rw [if_pos (by omega), hXe, e1, ← hM, ovOS_eq c hc a 0 (by omega)]
        ring
      · next hne =>
        split
        · next hge =>
          have hge' : D.M + 1 ≤ d1 + d2 := Nat.le_of_ble_eq_true hge
          refine ⟨hl, ?_⟩
          have hprod : |hev a 0 d1 b g d * hev c 0 d2 b g d / (S : ℝ) ^ 2| ≤
              (mmul (mmul (imagSum (hrng D a)) (imagSum (hrng D c)))
                (rpow D (d1 + d2 - (D.M + 1))) : ℝ) / 2 ^ 96 * mx b g ^ (D.M + 1) := by
            have h1 := hev_mag hz a 0 d1
            have h2 := hev_mag hz c 0 d2
            have hmx := mx_nonneg hz.b0 (g := g)
            have hpow : mx b g ^ (d1 + d2) ≤ mx b g ^ (D.M + 1) *
                ((rpow D (d1 + d2 - (D.M + 1)) : ℝ) / 2 ^ 96) := by
              rw [show d1 + d2 = (D.M + 1) + (d1 + d2 - (D.M + 1)) by omega, pow_add,
                Nat.add_sub_cancel_left]
              exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hmx (mx_le hz) _)
                (rpow_ge D _)) (pow_nonneg hmx _)
            have hm1 := mmul_ge (imagSum (hrng D a)) (imagSum (hrng D c))
            have hm2 := mmul_ge (mmul (imagSum (hrng D a)) (imagSum (hrng D c)))
              (rpow D (d1 + d2 - (D.M + 1)))
            calc |hev a 0 d1 b g d * hev c 0 d2 b g d / (S : ℝ) ^ 2|
                = |hev a 0 d1 b g d / S| * |hev c 0 d2 b g d / S| := by
                  rw [← abs_mul]; congr 1; ring
              _ ≤ ((imagSum (hrng D a) : ℝ) / 2 ^ 96 * mx b g ^ d1) *
                  ((imagSum (hrng D c) : ℝ) / 2 ^ 96 * mx b g ^ d2) :=
                mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
              _ = ((imagSum (hrng D a) : ℝ) / 2 ^ 96 * ((imagSum (hrng D c) : ℝ) / 2 ^ 96)) *
                  mx b g ^ (d1 + d2) := by
                rw [pow_add]
                generalize ((imagSum (hrng D a) : ℝ) / 2 ^ 96) = X1
                generalize ((imagSum (hrng D c) : ℝ) / 2 ^ 96) = X2
                ring
              _ ≤ (mmul (imagSum (hrng D a)) (imagSum (hrng D c)) : ℝ) / 2 ^ 96 *
                  (mx b g ^ (D.M + 1) * ((rpow D (d1 + d2 - (D.M + 1)) : ℝ) / 2 ^ 96)) :=
                mul_le_mul hm1 hpow (pow_nonneg hmx _) (off_nonneg _)
              _ = ((mmul (imagSum (hrng D a)) (imagSum (hrng D c)) : ℝ) / 2 ^ 96 *
                  ((rpow D (d1 + d2 - (D.M + 1)) : ℝ) / 2 ^ 96)) * mx b g ^ (D.M + 1) := by
                generalize ((mmul (imagSum (hrng D a)) (imagSum (hrng D c)) : ℝ) / 2 ^ 96) = X1
                generalize ((rpow D (d1 + d2 - (D.M + 1)) : ℝ) / 2 ^ 96) = X2
                ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hm2 (pow_nonneg hmx _)
          obtain ⟨hr2, hr2b, hr2e⟩ := radial_of (M := D.M) hz.b0 (by positivity) hprod
          refine ⟨hs, hr + hr2, hH, ?_, ?_⟩
          · show |hr + hr2| ≤ ((Nat.add acc.2 _ : ℕ) : ℝ) / 2 ^ 96
            rw [cast_add, add_div]
            exact le_trans (abs_add_le _ _) (add_le_add hh hr2b)
          · rw [if_pos (by omega), hXe, hr2e]
            ring
        · next hlt =>
          refine ⟨hl, hs, hr, hH, hh, ?_⟩
          have : ¬ D.M ≤ d1 + d2 := by
            have h1 : d1 + d2 ≠ D.M := fun e => hne (by simp [e])
            have h2 : ¬ D.M + 1 ≤ d1 + d2 := fun e => hlt (Nat.ble_eq_true_of_le e)
            omega
          rw [if_neg this, hXe]
          ring
    obtain ⟨acc', hacc, hl', hrep⟩ := step
    subst hacc
    have ih := ovRow_sem hz a d1 ha B (d2 + 1) _
      (X + (if D.M ≤ d1 + d2 then hev a 0 d1 b g d * hev c 0 d2 b g d else 0) / (S : ℝ) ^ 2)
      hB hl' hrep
    refine ⟨ih.1, ?_⟩
    have e : X + ((if D.M ≤ d1 + d2 then hev a 0 d1 b g d * hev c 0 d2 b g d else 0) +
        ovRowS a d1 B (d2 + 1) D.M b g d) / (S : ℝ) ^ 2 =
        X + (if D.M ≤ d1 + d2 then hev a 0 d1 b g d * hev c 0 d2 b g d else 0) / (S : ℝ) ^ 2 +
          ovRowS a d1 B (d2 + 1) D.M b g d / (S : ℝ) ^ 2 := by ring
    rw [e]
    exact ih.2

theorem ovAll_sem (hz : InBox D b g d) (B : Ex) (hB : WFo B 0) :
    ∀ (A : Ex) (d1 : ℕ) (acc : List I × ℕ) (X : ℝ), WFo A d1 → acc.1.length = D.M + 1 →
    Rep D b g acc X →
    Rep D b g (ovAll D (erng D B) (kcomp (erng D B)) d1 (erng D A) (kcomp (erng D A)) acc)
      (X + ovAllS A d1 B D.M b g d / (S : ℝ) ^ 2)
  | [], d1, acc, X, _, _, hX => by simpa [erng, kcomp, ovAll, ovAllS] using hX
  | a :: A, d1, acc, X, ⟨ha, hA⟩, hl, hX => by
    simp only [erng, kcomp, ovAll, ovAllS]
    obtain ⟨hl', hrep⟩ := ovRow_sem hz a d1 ha B 0 acc X hB hl hX
    have ih := ovAll_sem hz B hB A (d1 + 1) _ _ hA hl' hrep
    have e : X + (ovRowS a d1 B 0 D.M b g d + ovAllS A (d1 + 1) B D.M b g d) / (S : ℝ) ^ 2 =
        X + ovRowS a d1 B 0 D.M b g d / (S : ℝ) ^ 2 + ovAllS A (d1 + 1) B D.M b g d / (S : ℝ) ^ 2 := by
      ring
    rw [e]
    exact ih

end mul


section mulmain
variable {D : Dom} {b g d : ℝ}

/-- the constant coefficient of the exact part, and the rest of the exact part -/
theorem const_split (hz : InBox D b g d) {E : Ex} (hw : WFo E 0) :
    ∃ c, I.mem c (rget (rrow (erng D E) 0) 0) ∧
      |eev E 0 b g d / S - c| ≤ mx b g * ((k1 D 0 (kcomp (erng D E)) : ℝ) / 2 ^ 96) := by
  rcases E with _ | ⟨a, E⟩
  · exact ⟨0, by simpa [erng, rrow, rget] using I.mem_zero, by
      simp only [erng, kcomp, k1, eev_nil, zero_div, sub_zero, abs_zero, Nat.cast_zero]
      simp⟩
  · obtain ⟨ha, hE⟩ := hw
    have hk : k1 D 0 (kcomp (erng D (a :: E))) = k1 D 1 (kcomp (erng D E)) := by
      simp only [erng, kcomp, k1, sel_eq]
      simp
    rw [hk]
    have hrest := eev_mag1 hz E 1 le_rfl
    rcases a with _ | ⟨c0, a⟩
    · refine ⟨0, by simpa [erng, rrow, rget, hrng] using I.mem_zero, ?_⟩
      simp only [eev_cons, hev_nil, zero_add, sub_zero]
      exact hrest
    · have ha' : a = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at ha; omega)
      subst ha'
      refine ⟨qev c0 d / S, by simpa [erng, rrow, rget, hrng] using qrng_mem D.wm D.s hz.d1 c0, ?_⟩
      simp only [eev_cons, hev_cons, hev_nil, pow_zero, Nat.zero_sub, mul_one, add_zero]
      rw [add_div, add_sub_cancel_left]
      exact hrest

/-- **Products.** -/
theorem mul_at (hM : 1 ≤ D.M) (hz : InBox D b g d) {u v : ℝ} {t1 t2 : TF}
    (h1 : TFEncAt D b g d u t1) (h2 : TFEncAt D b g d v t2) :
    TFEncAt D b g d (u * v) (TF.mul D t1 t2) := by
  intro hok
  have hok0 := mk'_ok (D := D) (E := (ediv S (emulR D.M t1.E t2.E)).1) hok
  obtain ⟨hok', hw, hl⟩ := hok0
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨hok1, hok2⟩, hex⟩ := hok'
  obtain ⟨hw1, hl1, hs1, hr1, hH1, hh1, he1⟩ := h1 hok1
  obtain ⟨hw2, hl2, hs2, hr2, hH2, hh2, he2⟩ := h2 hok2
  refine ⟨hw, hl, ?_⟩
  dsimp only [TF.mul, TF.mk']
  have hmx : 0 ≤ mx b g := mx_nonneg hz.b0
  -- the exact part and the overflow
  have hE := eev_emulR t1.E t2.E 0 D.M hw1 hw2 (b := b) (g := g) (d := d)
  rw [Nat.zero_add] at hE
  have hdiv := eev_ediv S (emulR D.M t1.E t2.E) 0 hex (b := b) (g := g) (d := d)
  have hov := ovAll_sem hz t2.E hw2 t1.E 0 (zeroH D.M, 0) 0 hw1 (zeroH_length D.M)
    ⟨zeros D.M, 0, mem_zeros D.M, by simp, by simp [tev_zeros]⟩
  obtain ⟨hsov, hrov, hHov, hhov, heov⟩ := hov
  -- the constant terms
  obtain ⟨c1, hc1, hc1b⟩ := const_split hz hw1
  obtain ⟨c2, hc2, hc2b⟩ := const_split hz hw2
  -- magnitudes of the tops and ranges
  have hT1 := tev_mag hz (M := D.M) 0 hH1
  have hT2 := tev_mag hz (M := D.M) 0 hH2
  obtain ⟨-, hrng1'⟩ := range_mem hz hH1 hh1
  obtain ⟨hrng2, -⟩ := range_mem hz hH2 hh2
  have hv_le : |v| ≤ (imag (TF.range D t2) : ℝ) / 2 ^ 96 := by
    rw [he2]; exact imag_ge hrng2
  have hPT1 := imag_ge hrng1'
  -- the radial pieces
  have hmM : mx b g ^ (D.M + 1) = mx b g * mx b g ^ D.M := by rw [pow_succ, mul_comm]
  have rb : |(eev t1.E 0 b g d / S - c1) * tev hs2 0 D.M b g| ≤
      (mmul (k1 D 0 (kcomp (erng D t1.E))) (imagSum t2.H) : ℝ) / 2 ^ 96 * mx b g ^ (D.M + 1) := by
    rw [abs_mul, hmM]
    calc |eev t1.E 0 b g d / S - c1| * |tev hs2 0 D.M b g|
        ≤ (mx b g * ((k1 D 0 (kcomp (erng D t1.E)) : ℝ) / 2 ^ 96)) *
          ((imagSum t2.H : ℝ) / 2 ^ 96 * mx b g ^ D.M) :=
        mul_le_mul hc1b hT2 (abs_nonneg _) (mul_nonneg hmx (off_nonneg _))
      _ = (((k1 D 0 (kcomp (erng D t1.E)) : ℝ) / 2 ^ 96) * ((imagSum t2.H : ℝ) / 2 ^ 96)) *
          (mx b g * mx b g ^ D.M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mmul_ge _ _) (mul_nonneg hmx (pow_nonneg hmx _))
  have rc : |(eev t2.E 0 b g d / S - c2) * tev hs1 0 D.M b g| ≤
      (mmul (k1 D 0 (kcomp (erng D t2.E))) (imagSum t1.H) : ℝ) / 2 ^ 96 * mx b g ^ (D.M + 1) := by
    rw [abs_mul, hmM]
    calc |eev t2.E 0 b g d / S - c2| * |tev hs1 0 D.M b g|
        ≤ (mx b g * ((k1 D 0 (kcomp (erng D t2.E)) : ℝ) / 2 ^ 96)) *
          ((imagSum t1.H : ℝ) / 2 ^ 96 * mx b g ^ D.M) :=
        mul_le_mul hc2b hT1 (abs_nonneg _) (mul_nonneg hmx (off_nonneg _))
      _ = (((k1 D 0 (kcomp (erng D t2.E)) : ℝ) / 2 ^ 96) * ((imagSum t1.H : ℝ) / 2 ^ 96)) *
          (mx b g * mx b g ^ D.M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mmul_ge _ _) (mul_nonneg hmx (pow_nonneg hmx _))
  have rd : |tev hs1 0 D.M b g * tev hs2 0 D.M b g| ≤
      (mmul (mmul (imagSum t1.H) (imagSum t2.H)) (rpow D (D.M - 1)) : ℝ) / 2 ^ 96 *
        mx b g ^ (D.M + 1) := by
    have hpow : mx b g ^ D.M * mx b g ^ D.M ≤
        mx b g ^ (D.M + 1) * ((rpow D (D.M - 1) : ℝ) / 2 ^ 96) := by
      rw [← pow_add, show D.M + D.M = (D.M + 1) + (D.M - 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left (le_trans (pow_le_pow_left₀ hmx (mx_le hz) _)
        (rpow_ge D _)) (pow_nonneg hmx _)
    rw [abs_mul]
    calc |tev hs1 0 D.M b g| * |tev hs2 0 D.M b g|
        ≤ ((imagSum t1.H : ℝ) / 2 ^ 96 * mx b g ^ D.M) *
          ((imagSum t2.H : ℝ) / 2 ^ 96 * mx b g ^ D.M) :=
        mul_le_mul hT1 hT2 (abs_nonneg _) (mul_nonneg (off_nonneg _) (pow_nonneg hmx _))
      _ = ((imagSum t1.H : ℝ) / 2 ^ 96 * ((imagSum t2.H : ℝ) / 2 ^ 96)) *
          (mx b g ^ D.M * mx b g ^ D.M) := by ring
      _ ≤ (mmul (imagSum t1.H) (imagSum t2.H) : ℝ) / 2 ^ 96 *
          (mx b g ^ (D.M + 1) * ((rpow D (D.M - 1) : ℝ) / 2 ^ 96)) :=
        mul_le_mul (mmul_ge _ _) hpow (mul_nonneg (pow_nonneg hmx _) (pow_nonneg hmx _))
          (off_nonneg _)
      _ = ((mmul (imagSum t1.H) (imagSum t2.H) : ℝ) / 2 ^ 96 *
          ((rpow D (D.M - 1) : ℝ) / 2 ^ 96)) * mx b g ^ (D.M + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mmul_ge _ _) (pow_nonneg hmx _)
  have re : |hr1 * mx b g ^ (D.M + 1) * v| ≤
      (mmul t1.Hr (imag (TF.range D t2)) : ℝ) / 2 ^ 96 * mx b g ^ (D.M + 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hmx _)]
    calc |hr1| * mx b g ^ (D.M + 1) * |v| = (|hr1| * |v|) * mx b g ^ (D.M + 1) := by
          ring
      _ ≤ ((t1.Hr : ℝ) / 2 ^ 96 * ((imag (TF.range D t2) : ℝ) / 2 ^ 96)) * mx b g ^ (D.M + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hh1 hv_le (abs_nonneg _) (off_nonneg _))
          (pow_nonneg hmx _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mmul_ge _ _) (pow_nonneg hmx _)
  have rf : |hr2 * mx b g ^ (D.M + 1) * (eev t1.E 0 b g d / S + tev hs1 0 D.M b g)| ≤
      (mmul t2.Hr (imag (TF.range D t1)) : ℝ) / 2 ^ 96 * mx b g ^ (D.M + 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hmx _)]
    calc |hr2| * mx b g ^ (D.M + 1) * |eev t1.E 0 b g d / S + tev hs1 0 D.M b g|
        = (|hr2| * |eev t1.E 0 b g d / S + tev hs1 0 D.M b g|) * mx b g ^ (D.M + 1) := by ring
      _ ≤ ((t2.Hr : ℝ) / 2 ^ 96 * ((imag (TF.range D t1) : ℝ) / 2 ^ 96)) * mx b g ^ (D.M + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hh2 hPT1 (abs_nonneg _) (off_nonneg _))
          (pow_nonneg hmx _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mmul_ge _ _) (pow_nonneg hmx _)
  obtain ⟨xb, xbb, xbe⟩ := radial_of (M := D.M) hz.b0 (off_nonneg _) rb
  obtain ⟨xc, xcb, xce⟩ := radial_of (M := D.M) hz.b0 (off_nonneg _) rc
  obtain ⟨xd, xdb, xde⟩ := radial_of (M := D.M) hz.b0 (off_nonneg _) rd
  obtain ⟨xe, xeb, xee⟩ := radial_of (M := D.M) hz.b0 (off_nonneg _) re
  obtain ⟨xf, xfb, xfe⟩ := radial_of (M := D.M) hz.b0 (off_nonneg _) rf
  refine ⟨ladd hsov (ladd (hs2.map (fun x => c1 * x)) (hs1.map (fun x => c2 * x))),
    hrov + (xb + xc + (xd + (xe + xf))),
    mem_ladd hHov (mem_ladd (mem_iscal hc1 hH2) (mem_iscal hc2 hH1)), ?_, ?_⟩
  · simp only [cast_add, add_div]
    calc |hrov + (xb + xc + (xd + (xe + xf)))|
        ≤ |hrov| + (|xb| + |xc| + (|xd| + (|xe| + |xf|))) := by
          refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
          refine le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) ?_)
          exact le_trans (abs_add_le _ _) (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ _ := by gcongr
  · rw [tev_ladd, tev_ladd, tev_scal, tev_scal]
    have hS := S_pos
    have hPP : eev t1.E 0 b g d / S * (eev t2.E 0 b g d / S) =
        eev (ediv S (emulR D.M t1.E t2.E)).1 0 b g d / S +
          (tev hsov 0 D.M b g + hrov * mx b g ^ (D.M + 1)) := by
      calc eev t1.E 0 b g d / S * (eev t2.E 0 b g d / S)
          = (eev t1.E 0 b g d * eev t2.E 0 b g d) / (S : ℝ) ^ 2 := by ring
        _ = (eev (emulR D.M t1.E t2.E) 0 b g d + ovAllS t1.E 0 t2.E D.M b g d) / (S : ℝ) ^ 2 := by
          rw [hE]
        _ = eev (ediv S (emulR D.M t1.E t2.E)).1 0 b g d * S / (S : ℝ) ^ 2 +
            ovAllS t1.E 0 t2.E D.M b g d / (S : ℝ) ^ 2 := by rw [hdiv, add_div]
        _ = eev (ediv S (emulR D.M t1.E t2.E)).1 0 b g d / S +
            (0 + ovAllS t1.E 0 t2.E D.M b g d / (S : ℝ) ^ 2) := by
          rw [zero_add]; congr 1; field_simp
        _ = _ := by rw [heov]
    rw [he1, he2]
    calc (eev t1.E 0 b g d / S + tev hs1 0 D.M b g + hr1 * mx b g ^ (D.M + 1)) *
          (eev t2.E 0 b g d / S + tev hs2 0 D.M b g + hr2 * mx b g ^ (D.M + 1))
        = eev t1.E 0 b g d / S * (eev t2.E 0 b g d / S) +
          (c1 * tev hs2 0 D.M b g + (eev t1.E 0 b g d / S - c1) * tev hs2 0 D.M b g) +
          (c2 * tev hs1 0 D.M b g + (eev t2.E 0 b g d / S - c2) * tev hs1 0 D.M b g) +
          tev hs1 0 D.M b g * tev hs2 0 D.M b g +
          hr1 * mx b g ^ (D.M + 1) *
            (eev t2.E 0 b g d / S + tev hs2 0 D.M b g + hr2 * mx b g ^ (D.M + 1)) +
          hr2 * mx b g ^ (D.M + 1) * (eev t1.E 0 b g d / S + tev hs1 0 D.M b g) := by ring
      _ = _ := by
        rw [hPP, xbe, xce, xde, ← he2, xee, xfe]
        ring

end mulmain


/-! ## division and square roots -/

section invsqrt
variable {D : Dom} {b g d : ℝ}

/-- an exact Taylor form (no tops) -/
theorem exact_at (Y : Ex) :
    TFEncAt D b g d (eev Y 0 b g d / S) (TF.mk' D Y (zeroH D.M) 0 true) := by
  intro hok
  obtain ⟨-, hw, hl⟩ := mk'_ok hok
  refine ⟨hw, hl, zeros D.M, 0, mem_zeros D.M, by simp [TF.mk'], ?_⟩
  simp [TF.mk', tev_zeros]

theorem finishRes_some {Y : Ex} {res : TF} {X : Option I} {t' : TF}
    (h : finishRes D Y res X = some t') :
    ∃ x, X = some x ∧ ezero res.E = true ∧
      t' = TF.mk' D Y (iscal x res.H) (mmul res.Hr (imag x)) res.ok := by
  unfold finishRes at h
  rcases X with _ | x
  · exact absurd h (by simp)
  · simp only [sel_eq] at h
    split at h
    · next he => exact ⟨x, rfl, he, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-- `Y + res · x` for a residual with vanishing exact part and `w ∈ x` -/
theorem finish_at {Y : Ex} {res : TF} {x : I} {w r : ℝ} (hw : I.mem w x)
    (hres : TFEncAt D b g d r res) (hz0 : ezero res.E = true) (hu : r * w = 0 - 0 + r * w) :
    TFEncAt D b g d (eev Y 0 b g d / S + r * w)
      (TF.mk' D Y (iscal x res.H) (mmul res.Hr (imag x)) res.ok) := by
  intro hok
  obtain ⟨hok', hW, hl⟩ := mk'_ok hok
  obtain ⟨-, -, hs, hr, hH, hh, he⟩ := hres hok'
  rw [ezero_sound res.E hz0 0, zero_div, zero_add] at he
  refine ⟨hW, hl, hs.map (fun h => w * h), hr * w, mem_iscal hw hH, ?_, ?_⟩
  · show |hr * w| ≤ (mmul res.Hr (imag x) : ℝ) / 2 ^ 96
    rw [abs_mul]
    exact le_trans (mul_le_mul hh (imag_ge hw) (abs_nonneg _) (off_nonneg _)) (mmul_ge _ _)
  · show eev Y 0 b g d / S + r * w = eev Y 0 b g d / S + tev (hs.map (fun h => w * h)) 0 D.M b g +
      hr * w * mx b g ^ (D.M + 1)
    rw [tev_scal, he]
    ring

theorem mul_ok {t1 t2 : TF} (h : (TF.mul D t1 t2).ok = true) : t1.ok = true ∧ t2.ok = true := by
  have h0 := mk'_ok (D := D) (E := (ediv S (emulR D.M t1.E t2.E)).1) h
  simp only [Bool.and_eq_true] at h0
  exact h0.1.1

theorem sub_ok {t1 t2 : TF} (h : (TF.sub D t1 t2).ok = true) : t1.ok = true ∧ t2.ok = true := by
  have h0 := mk'_ok (D := D) (E := eadd t1.E t2.neg.E) h
  simp only [Bool.and_eq_true] at h0
  exact h0.1

theorem inv_at (hM : 1 ≤ D.M) (hz : InBox D b g d) {u : ℝ} {t t' : TF}
    (h : TFEncAt D b g d u t) (hi : TF.inv D t = some t') : TFEncAt D b g d u⁻¹ t' := by
  unfold TF.inv at hi
  split at hi
  · next n0 _ =>
    rw [sel_eq] at hi
    split at hi
    · exact absurd hi (by simp)
    · dsimp only at hi
      obtain ⟨x, hx, hz0, rfl⟩ := finishRes_some hi
      intro hok
      obtain ⟨hokres, -, -⟩ := mk'_ok hok
      set Y := TF.invY D t n0
      have hres := sub_at (cst_at D b g d [(S : Int)]) (mul_at hM hz h (exact_at (D := D) (b := b)
        (g := g) (d := d) Y))
      have hokt : t.ok = true := (mul_ok (sub_ok hokres).2).1
      obtain ⟨-, -, hs0, hr0, hH0, hh0, he0⟩ := h hokt
      obtain ⟨hu_rng, -⟩ := range_mem hz hH0 hh0
      rw [← he0] at hu_rng
      obtain ⟨hu0, hw⟩ := I.mem_inv hu_rng hx
      have hS := S_pos
      have hq : qev [(S : Int)] d / S = 1 := by
        simp only [qev_cons, qev_nil, mul_zero, add_zero, Int.cast_natCast]
        exact div_self hS.ne'
      have key : u⁻¹ = eev Y 0 b g d / S +
          (qev [(S : Int)] d / S - u * (eev Y 0 b g d / S)) * u⁻¹ := by
        rw [hq]
        field_simp
        ring
      rw [key]
      exact finish_at hw hres hz0 (by ring) hok
  · exact absurd hi (by simp)

theorem sqrtFin_some {Y : Ex} {u t' : TF} {o : Option I} (h : TF.sqrtFin D Y u o = some t') :
    ∃ su x, o = some su ∧ (su.add ((TF.ex D Y).range D)).inv = some x ∧
      ezero (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y))).E = true ∧
      t' = TF.mk' D Y (iscal x (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y))).H)
        (mmul (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y))).Hr (imag x))
        (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y))).ok := by
  rcases o with _ | su
  · exact absurd h (by simp [TF.sqrtFin])
  · have h' : finishRes D Y (TF.sub D u (TF.mul D (TF.ex D Y) (TF.ex D Y)))
        (su.add ((TF.ex D Y).range D)).inv = some t' := h
    obtain ⟨x, hx, hz0, he⟩ := finishRes_some h'
    exact ⟨su, x, rfl, hx, hz0, he⟩

theorem sqrtCore_at (hM : 1 ≤ D.M) (hz : InBox D b g d) {u : ℝ} {t t' : TF} (y0 : ℕ)
    (h : TFEncAt D b g d u t) (hi : TF.sqrtCore D t y0 = some t') :
    TFEncAt D b g d (Real.sqrt u) t' := by
  unfold TF.sqrtCore at hi
  obtain ⟨su, x, hsu, hx, hz0, rfl⟩ := sqrtFin_some hi
  generalize TF.sqrtY D t y0 = Y at hsu hx hz0 ⊢
  intro hok
  obtain ⟨hokres, -, -⟩ := mk'_ok hok
  have hYt : TFEncAt D b g d (eev Y 0 b g d / S) (TF.ex D Y) := exact_at Y
  have hres := sub_at h (mul_at hM hz hYt hYt)
  have hokt : t.ok = true := (sub_ok hokres).1
  have hYok : (TF.ex D Y).ok = true := (mul_ok (sub_ok hokres).2).1
  obtain ⟨-, -, hs0, hr0, hH0, hh0, he0⟩ := h hokt
  obtain ⟨hu_rng, -⟩ := range_mem hz hH0 hh0
  rw [← he0] at hu_rng
  obtain ⟨hu_nn, hsq⟩ := I.mem_sqrt hu_rng hsu
  obtain ⟨-, -, hsY, hrY, hHY, hhY, heY⟩ := hYt hYok
  obtain ⟨hY_rng, -⟩ := range_mem hz hHY hhY
  rw [← heY] at hY_rng
  obtain ⟨hne, hw⟩ := I.mem_inv (I.mem_add hsq hY_rng) hx
  have key : Real.sqrt u = eev Y 0 b g d / S +
      (u - eev Y 0 b g d / S * (eev Y 0 b g d / S)) * (Real.sqrt u + eev Y 0 b g d / S)⁻¹ := by
    have hsq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu_nn
    have e1 : u - eev Y 0 b g d / S * (eev Y 0 b g d / S) =
        (Real.sqrt u - eev Y 0 b g d / S) * (Real.sqrt u + eev Y 0 b g d / S) := by
      linear_combination (-1 : ℝ) * hsq2
    rw [e1, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    ring
  rw [key]
  exact finish_at hw hres hz0 (by ring) hok

theorem sqrt_at (hM : 1 ≤ D.M) (hz : InBox D b g d) {u : ℝ} {t t' : TF}
    (h : TFEncAt D b g d u t) (hi : TF.sqrt D t = some t') : TFEncAt D b g d (Real.sqrt u) t' := by
  unfold TF.sqrt at hi
  split at hi
  · next n0 _ => exact sqrtCore_at hM hz _ h hi
  · exact absurd hi (by simp)

end invsqrt

end

end CTF
end C4
