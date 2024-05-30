/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Int.Order.Units
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Prime
import FltRegular.FltThree.Primes

theorem Zsqrtd.exists {d : ℤ} (a : ℤ√d) (him : a.im ≠ 0) :
    ∃ c : ℤ√d, a.norm = c.norm ∧ 0 ≤ c.re ∧ c.im ≠ 0 :=
  by
  cases' le_or_lt a.re 0 with hre hre
  · use -a
    simp only [hre, him, Zsqrtd.norm_neg, eq_self_iff_true, Zsqrtd.neg_im, Zsqrtd.neg_re,
      and_self_iff, neg_nonneg, Ne, not_false_iff, neg_eq_zero]
  · use a
    simp only [hre.le, him, eq_self_iff_true, and_self_iff, Ne, not_false_iff]

-- Edwards p49 step (2')
theorem factors2 {a : ℤ√(-3)} (heven : Even a.norm) : ∃ b : ℤ√(-3), a.norm = 4 * b.norm :=
  by
  have hparity : Even a.re ↔ Even a.im := by
    have : ¬ Even (3 : ℤ) := by decide
    simpa [this, two_ne_zero, Zsqrtd.norm_def, parity_simps] using heven
  simp only [iff_iff_and_or_not_and_not, ← Int.odd_iff_not_even] at hparity
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ | ⟨hre, him⟩ := hparity
  · use ⟨c, d⟩
    simp only [Zsqrtd.norm_def, hc, hd]
    ring
  · cases' Int.four_dvd_add_or_sub_of_odd hre him with h4 h4
    · obtain ⟨v, hv⟩ := h4
      use ⟨v - a.im, v⟩
      rw [eq_comm, ← sub_eq_iff_eq_add] at hv
      simp only [Zsqrtd.norm_def, ← hv]
      ring
    · obtain ⟨v, hv⟩ := h4
      use ⟨v + a.im, v⟩
      rw [sub_eq_iff_eq_add] at hv
      simp only [Zsqrtd.norm_def, hv]
      ring

theorem Spts.mul_of_dvd' {a p : ℤ√(-3)} (hdvd : p.norm ∣ a.norm) (hpprime : Prime p.norm) :
    ∃ u : ℤ√(-3), a = p * u ∨ a = star p * u :=
  by
  obtain ⟨f, hf⟩ := hdvd
  have h0 : p.norm ∣ p.re * a.im - a.re * p.im ∨ p.norm ∣ p.re * a.im + a.re * p.im :=
    by
    apply hpprime.dvd_or_dvd
    convert dvd_mul_right p.norm (a.im ^ 2 - p.im ^ 2 * f) using 1
    trans a.im ^ 2 * p.norm - p.im ^ 2 * (p.norm * f)
    · rw [← hf, Zsqrtd.norm_def, Zsqrtd.norm_def]
      ring
    · rw [Zsqrtd.norm_def]
      ring
  obtain ⟨A, HA⟩ : ∃ A : Units ℤ, p.norm ∣ p.re * a.im + A * a.re * p.im :=
    by
    cases' h0 with h0 h0 <;> [(use -1); (use 1)] <;> convert h0 using 1 <;>
      simp only [Units.val_neg, Units.val_one, neg_mul, one_mul]
    ring
  have HAsq : (A : ℤ) ^ 2 = 1 := by
    calc
      (A : ℤ) ^ 2 = ((A ^ 2 : Units ℤ) : ℤ) := (Units.val_pow_eq_pow_val _ _).symm
      _ = ((1 : Units ℤ) : ℤ) := (congr_arg _ (Int.units_sq A))
      _ = 1 := Units.val_one

  · set X : ℤ√(-3) := ⟨p.re * a.re - A * 3 * p.im * a.im, p.re * a.im + A * a.re * p.im⟩ with HX
    obtain ⟨U, HU⟩ : (p.norm : ℤ√(-3)) ∣ X :=
      by
      rw [Zsqrtd.intCast_dvd]
      refine' ⟨_, HA⟩
      apply @Prime.dvd_of_dvd_pow _ _ _ hpprime _ 2
      have : X.re ^ 2 = X.norm - 3 * X.im ^ 2 :=
        by
        rw [Zsqrtd.norm_def]
        ring
      rw [this]
      apply dvd_sub
      · use a.norm
        trans
          (p.re * a.re) ^ 2 + (A : ℤ) ^ 2 * (3 * p.im * a.im) ^ 2 +
            3 * ((p.re * a.im) ^ 2 + (A : ℤ) ^ 2 * (a.re * p.im) ^ 2)
        · simp only [Zsqrtd.norm_def]
          ring
        · simp only [Zsqrtd.norm_def, HAsq]
          ring
      · apply dvd_mul_of_dvd_right
        exact dvd_pow HA two_ne_zero
    use U
    suffices a = ⟨p.re, -A * p.im⟩ * U by
      apply Or.imp _ _ (Int.units_eq_one_or A).symm <;> rintro rfl <;> simpa [Zsqrtd.ext] using this
    apply Zsqrtd.eq_of_smul_eq_smul_left hpprime.ne_zero
    have : p.norm = p.re ^ 2 + 3 * (A : ℤ) ^ 2 * p.im ^ 2 :=
      by
      rw [Zsqrtd.norm_def, HAsq]
      ring
    rw [mul_comm _ U, ← mul_assoc, ← HU, HX]
    simp only [Zsqrtd.ext_iff, neg_mul, add_zero, Zsqrtd.intCast_re, MulZeroClass.zero_mul, mul_neg,
      Zsqrtd.mul_im, Zsqrtd.mul_re, neg_neg, MulZeroClass.mul_zero, neg_zero, Zsqrtd.intCast_im,
      this]
    constructor <;> ring

-- Edwards p49 step (3')
theorem Spts.mul_of_dvd'' {a p : ℤ√(-3)} (hdvd : p.norm ∣ a.norm) (hpprime : Prime p.norm) :
    ∃ u : ℤ√(-3), (a = p * u ∨ a = star p * u) ∧ a.norm = p.norm * u.norm :=
  by
  obtain ⟨u, hu⟩ := Spts.mul_of_dvd' hdvd hpprime
  refine' ⟨u, hu, _⟩
  obtain rfl | rfl := hu
  · rw [Zsqrtd.norm_mul]
  · rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]

-- Edwards p49 step (4'), contraposed
theorem factors' (a : ℤ√(-3)) (f : ℤ) (g : ℤ) (hodd : Odd f) (hgpos : g ≠ 0)
    (hfactor : f * g = a.norm)
    (hnotform : ∀ f' : ℤ, f' ∣ g → Odd f' → ∃ p : ℤ√(-3), abs f' = p.norm) :
    ∃ p : ℤ√(-3), abs f = p.norm :=
  by
  induction' hg : g.natAbs using Nat.strong_induction_on with g'' IH generalizing a g
  subst g''
  dsimp at IH
  by_cases H : Even (Zsqrtd.norm a)
  · obtain ⟨c, hc⟩ := factors2 H
    have : 4 ∣ g := by
      apply IsCoprime.dvd_of_dvd_mul_left
      · show IsCoprime _ f
        rw [Int.odd_iff_not_even, even_iff_two_dvd, ← Int.prime_two.coprime_iff_not_dvd] at hodd
        convert hodd.pow_left
        rw [sq]
        norm_num
      · rw [hfactor, hc]
        exact dvd_mul_right _ _
    obtain ⟨g', rfl⟩ := this
    have hg'pos : g' ≠ 0 := right_ne_zero_of_mul hgpos
    refine' IH g'.natAbs _ c g' hg'pos _ _ rfl
    · rw [Int.natAbs_mul]
      apply lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hg'pos)
      norm_num
    · rw [← mul_right_inj' (four_ne_zero' ℤ), ← hc, ← hfactor, mul_left_comm]
    · intro f' hf'dvd hf'odd
      refine' hnotform f' _ hf'odd
      exact hf'dvd.mul_left _
  · by_cases h : |g| = 1
    · apply_fun abs  at hfactor
      rw [abs_mul, h, mul_one, abs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) a)] at hfactor
      exact ⟨_, hfactor⟩
    · rw [Int.abs_eq_natAbs, ← Int.ofNat_one, Int.natCast_inj] at h
      obtain ⟨p, pprime, pdvd⟩ := Int.exists_prime_and_dvd h
      have : p ∣ a.norm := by
        rw [← hfactor]
        exact pdvd.mul_left _
      have podd : Odd p :=
        Int.odd_iff_not_even.mpr
          (by
            intro X
            apply H
            apply even_iff_two_dvd.mpr
            apply dvd_trans _ this
            apply even_iff_two_dvd.mp X)
      obtain ⟨A, HA⟩ := hnotform p pdvd podd
      have pprime' := pprime.abs
      rw [HA] at pprime'
      have pdvd' : A.norm ∣ a.norm := by
        rw [← hfactor, ← HA, abs_dvd]
        exact dvd_mul_of_dvd_right pdvd _
      obtain ⟨c, -, hcd⟩ := Spts.mul_of_dvd'' pdvd' pprime'
      obtain ⟨q, rfl⟩ := pdvd
      have hqpos : q ≠ 0 := right_ne_zero_of_mul hgpos
      have : (p.sign * q).natAbs = q.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_sign_of_nonzero pprime.ne_zero, one_mul]
      refine' IH q.natAbs _ c (p.sign * q) _ _ _ this
      · rw [Int.natAbs_mul]
        apply lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hqpos)
        rw [Int.prime_iff_natAbs_prime] at pprime
        exact pprime.one_lt
      · rwa [← Int.natAbs_eq_zero, this, Int.natAbs_eq_zero]
      ·
        rw [← mul_right_inj' pprime'.ne_zero, ← hcd, mul_left_comm, ← hfactor, ← HA, ←
          mul_assoc (|p|), mul_comm (|p|), Int.sign_mul_abs]
      · intro f' hf'dvd hf'odd
        refine' hnotform f' _ hf'odd
        rw [← Int.dvd_natAbs, this, Int.dvd_natAbs] at hf'dvd
        exact hf'dvd.mul_left _

theorem Zqrtd.factor_div (a : ℤ√(-3)) {x : ℤ} (hodd : Odd x) :
    ∃ c m : ℤ√(-3), a = c + m * x ∧ c.norm < x ^ 2 :=
  by
  obtain ⟨m, c, ha, hc⟩ := Int.factor_div a.re x hodd
  obtain ⟨n, d, hb, hd⟩ := Int.factor_div a.im x hodd
  set c' : ℤ√(-3) := ⟨c, d⟩
  refine' ⟨c', ⟨m, n⟩, _, _⟩
  ·
    simp only [Zsqrtd.ext_iff, ha, hb, add_zero, Zsqrtd.intCast_re, eq_self_iff_true, Zsqrtd.mul_im,
      zero_add, Zsqrtd.add_im, and_self_iff, Zsqrtd.mul_re, MulZeroClass.mul_zero, Zsqrtd.add_re,
      Zsqrtd.intCast_im]
  · rw [← mul_lt_mul_left (by norm_num : (0 : ℤ) < 4)]
    calc
      4 * c'.norm = (2 * c) ^ 2 + 3 * (2 * d) ^ 2 :=
        by
        rw [Zsqrtd.norm_def]
        ring
      _ < x ^ 2 + 3 * x ^ 2 := (add_lt_add ?_ ?_)
      _ = 4 * x ^ 2 := by ring

    · rw [mul_pow, ← Int.natAbs_pow_two c, ← Int.natAbs_pow_two x, ← mul_pow]
      norm_cast
      exact Nat.pow_lt_pow_left hc two_ne_zero
    · rw [mul_pow, ← Int.natAbs_pow_two d, ← Int.natAbs_pow_two x, ← mul_pow,
        mul_lt_mul_left (by norm_num : (0 : ℤ) < 3)]
      norm_cast
      exact Nat.pow_lt_pow_left hd two_ne_zero

theorem Zqrtd.factor_div' (a : ℤ√(-3)) {x : ℤ} (hodd : Odd x) (h : 1 < |x|)
    (hcoprime : IsCoprime a.re a.im) (hfactor : x ∣ a.norm) :
    ∃ c m : ℤ√(-3),
      a = c + m * x ∧ c.norm < x ^ 2 ∧ c ≠ 0 ∧ ∃ y, c.norm = x * y ∧ y.natAbs < x.natAbs :=
  by
  obtain ⟨c, m, rfl, h2⟩ := Zqrtd.factor_div a hodd
  refine' ⟨c, m, rfl, h2, _, _⟩
  · rintro rfl
    apply h.ne'
    rw [← Int.isUnit_iff_abs_eq]
    apply hcoprime.isUnit_of_dvd' <;>
      simp only [zero_add, mul_comm m, Zsqrtd.smul_re, Zsqrtd.smul_im, dvd_mul_right]
  · obtain ⟨y, hy⟩ : x ∣ c.norm :=
      by
      set e : ℤ := m.re ^ 2 * x + 2 * m.re * c.re + 3 * m.im ^ 2 * x + 6 * m.im * c.im with he
      convert dvd_sub hfactor (dvd_mul_right x e)
      rw [he, Zsqrtd.norm_def, Zsqrtd.norm_def]
      simp only [Zsqrtd.intCast_re, Zsqrtd.mul_im, Zsqrtd.add_im, Zsqrtd.mul_re, Zsqrtd.add_re,
        Zsqrtd.intCast_im]
      ring
    refine' ⟨y, hy, _⟩
    have h0'' : 0 < x.natAbs := by
      zify
      exact zero_lt_one.trans h
    rw [← mul_lt_mul_left h0'', ← pow_two, ← Int.natAbs_mul, ← hy]
    zify
    rwa [← Int.natCast_natAbs x, Int.natAbs_pow_two x, ← Int.natCast_natAbs,
      Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) c)]

-- Edwards p50 step (5')
theorem factors (a : ℤ√(-3)) (x : ℤ) (hcoprime : IsCoprime a.re a.im) (hodd : Odd x)
    (hfactor : x ∣ a.norm) : ∃ c : ℤ√(-3), abs x = c.norm :=
  by
  induction' hx' : x.natAbs using Nat.strong_induction_on with x' IH generalizing a x
  subst hx'
  have hneg1 : 1 ≤ a.norm := by
    rw [← Int.sub_one_lt_iff, sub_self]
    apply lt_of_le_of_ne (Zsqrtd.norm_nonneg (by norm_num) a)
    rw [Ne, eq_comm, Zsqrtd.norm_eq_zero_iff (by norm_num : (-3 : ℤ) < 0)]
    rintro rfl
    rw [Zsqrtd.zero_im, Zsqrtd.zero_re] at hcoprime
    exact not_isCoprime_zero_zero hcoprime
  have h0 : x ≠ 0 := by
    rintro rfl
    simp only [even_zero, not_true, Int.odd_iff_not_even] at hodd
  have h0' : 1 ≤ abs x := by rwa [← Int.sub_one_lt_iff, sub_self, abs_pos]
  cases' h0'.eq_or_lt with h h
  · rw [← h]
    refine' ⟨⟨1, 0⟩, _⟩
    norm_num [Zsqrtd.norm_def]
  obtain ⟨c', m, rfl, -, h1, ⟨y, hy, h3⟩⟩ := Zqrtd.factor_div' a hodd h hcoprime hfactor
  have h4 : c'.norm ≠ 0 := by rwa [Ne, Zsqrtd.norm_eq_zero_iff (by norm_num) c']
  set g := Int.gcd c'.re c'.im with hg
  have hgpos : 0 < g := by rwa [hg, Zsqrtd.gcd_pos_iff]
  obtain ⟨C', HC', HCDcoprime⟩ := Zsqrtd.exists_coprime_of_gcd_pos hgpos
  have h5 : x * y = (g : ℤ) ^ 2 * C'.norm := by
    rw [← hy, HC', Zsqrtd.norm_mul, Zsqrtd.norm_intCast, ← pow_two]
  obtain ⟨z, hz⟩ : (g : ℤ) ^ 2 ∣ y :=
    by
    have : (g : ℤ) ^ 2 ∣ x * y := by
      rw [h5]
      exact dvd_mul_right _ _
    apply IsCoprime.dvd_of_dvd_mul_left _ this
    apply isCoprime_of_prime_dvd
    · contrapose! h0
      exact h0.2
    intro p hpprime hpdvdleft hpdvdright
    have : ↑p ∣ c' + m * x := by
      rw [HC']
      exact
        dvd_add
          (dvd_mul_of_dvd_left
            ((Zsqrtd.intCast_dvd_intCast _ _).mpr (hpprime.dvd_of_dvd_pow hpdvdleft)) _)
          (dvd_mul_of_dvd_right ((Zsqrtd.intCast_dvd_intCast _ _).mpr hpdvdright) _)
    have := Zsqrtd.coprime_of_dvd_coprime hcoprime this
    simp only [Zsqrtd.intCast_re, isCoprime_zero_right, Zsqrtd.intCast_im, hpprime.not_unit] at this
  have h6 : x * z = C'.norm := by
    apply Int.eq_of_mul_eq_mul_left (pow_ne_zero 2 <| Int.natCast_ne_zero_iff_pos.mpr hgpos)
    rw [← h5, hz, mul_left_comm]
  have h8 : z ≠ 0 := by
    apply right_ne_zero_of_mul
    apply right_ne_zero_of_mul
    rwa [h6, ← h5, ← hy]
  refine' factors' _ x z hodd h8 h6 _
  intro w hwdvd hwodd
  refine' IH w.natAbs _ C' w HCDcoprime hwodd _ rfl
  ·
    calc
      w.natAbs ≤ z.natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr h8) (Int.natAbs_dvd_natAbs.mpr hwdvd)
      _ ≤ y.natAbs := by
        rw [hz, Int.natAbs_mul]
        exact Nat.le_mul_of_pos_left _ (pow_pos hgpos 2)
      _ < x.natAbs := h3

  · rw [← h6]
    exact dvd_mul_of_dvd_right hwdvd x

theorem Spts.eq_one {a : ℤ√(-3)} (h : a.norm = 1) : abs a.re = 1 ∧ a.im = 0 := by
  suffices H : abs a.re = 1 by
    refine' ⟨H, _⟩
    rw [Zsqrtd.norm_def, mul_assoc, ← Int.natAbs_mul_self' a.re, ← Int.abs_eq_natAbs, H, one_mul,
      neg_mul, sub_neg_eq_add, add_right_eq_self, mul_eq_zero, mul_self_eq_zero] at h
    exact h.resolve_left three_ne_zero
  contrapose! h
  cases' lt_or_gt_of_ne h with H H
  · have : a.re = 0 := by rwa [← Int.abs_lt_one_iff]
    simp only [Zsqrtd.norm_def, this, MulZeroClass.zero_mul, zero_sub, neg_mul, neg_neg]
    by_cases hb : a.im = 0
    · simp [hb]
    · have : 1 ≤ abs a.im := by rwa [← Int.abs_lt_one_iff, not_lt] at hb
      have : 1 ≤ a.im ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left zero_le_one this 2
      linarith
  · apply ne_of_gt
    rw [Zsqrtd.norm_def, neg_mul, neg_mul, sub_neg_eq_add]
    apply lt_add_of_lt_of_nonneg
    · rw [← sq, ← sq_abs]
      exact pow_lt_pow_left H zero_le_one two_ne_zero
    · rw [mul_assoc]
      exact mul_nonneg zero_lt_three.le (mul_self_nonneg _)

theorem Spts.eq_one' {a : ℤ√(-3)} (h : a.norm = 1) : a = 1 ∨ a = -1 := by
  simp only [Zsqrtd.ext_iff, Zsqrtd.one_re, Zsqrtd.one_im, Zsqrtd.neg_im, Zsqrtd.neg_re, neg_zero,
    ← or_and_right, ← abs_eq (zero_le_one' ℤ), Spts.eq_one h, eq_self_iff_true, and_self_iff]

theorem Spts.ne_zero_of_coprime' (a : ℤ√(-3)) (hcoprime : IsCoprime a.re a.im) : a.norm ≠ 0 :=
  by
  contrapose! hcoprime with H
  obtain ⟨rfl, rfl⟩ := (Zsqrtd.norm_eq_zero_iff (by norm_num) _).mp H
  exact not_isCoprime_zero_zero

theorem Spts.pos_of_coprime' {a : ℤ√(-3)} (hcoprime : IsCoprime a.re a.im) : 0 < a.norm :=
  by
  apply lt_of_le_of_ne
  · apply Zsqrtd.norm_nonneg
    norm_num
  · apply Ne.symm -- Porting note: `symm` fails
    exact Spts.ne_zero_of_coprime' _ hcoprime

theorem Spts.one_lt_of_im_ne_zero (a : ℤ√(-3)) (hb : a.im ≠ 0) : 1 < a.norm :=
  by
  apply lt_of_le_of_ne
  · rw [← Int.sub_one_lt_iff, sub_self]
    apply lt_of_le_of_ne (Zsqrtd.norm_nonneg (by norm_num) a)
    contrapose! hb
    rw [eq_comm, Zsqrtd.norm_eq_zero_iff (by norm_num) a] at hb
    rw [hb, Zsqrtd.zero_im]
  · intro H
    exact hb (Spts.eq_one H.symm).2

theorem Spts.not_two (a : ℤ√(-3)) : a.norm ≠ 2 :=
  by
  rw [Zsqrtd.norm_def]
  obtain him | him := eq_or_ne a.im 0
  · rw [him, MulZeroClass.mul_zero, sub_zero, ← Int.natAbs_mul_self, ← sq]
    norm_cast
    apply (Nat.pow_left_strictMono two_ne_zero).monotone.ne_of_lt_of_lt_nat 1 <;> norm_num
  · apply ne_of_gt
    apply lt_add_of_nonneg_of_lt (mul_self_nonneg a.re)
    rw [← Int.add_one_le_iff]
    rw [mul_assoc, neg_mul_eq_neg_mul, neg_neg]
    refine' le_mul_of_one_le_right zero_lt_three.le _
    rwa [← Int.sub_one_lt_iff, sub_self, mul_self_pos]

theorem Spts.four {p : ℤ√(-3)} (hfour : p.norm = 4) (hq : p.im ≠ 0) : abs p.re = 1 ∧ abs p.im = 1 :=
  by
  suffices p.re ^ 2 = 1 ∧ p.im ^ 2 = 1 by
    apply And.imp _ _ this <;>
      · intro h
        rwa [← sq_eq_sq (abs_nonneg (_ : ℤ)) zero_le_one, one_pow, sq_abs]
  have hq : p.im ^ 2 = 1 := by
    apply le_antisymm
    · contrapose! hfour with hq'
      apply ne_of_gt
      rw [← Int.add_one_le_iff] at hq'
      calc
        4 < 3 * 2 := by norm_num
        _ ≤ 3 * p.im ^ 2 := (Int.mul_le_mul_of_nonneg_left hq' (by norm_num))
        _ ≤ p.re ^ 2 + 3 * p.im ^ 2 := (le_add_of_nonneg_left (pow_two_nonneg p.re))
        _ = p.norm := by
          rw [Zsqrtd.norm_def]
          ring

    · rw [← Int.sub_one_lt_iff, sub_self]
      exact sq_pos_of_ne_zero hq
  refine' ⟨_, hq⟩
  calc
    p.re ^ 2 = p.re ^ 2 + 3 * p.im ^ 2 - 3 := by simp [hq]
    _ = p.norm - 3 := by
      rw [Zsqrtd.norm_def]
      ring
    _ = 1 := by
      rw [hfour]
      norm_num


theorem Spts.four_of_coprime {p : ℤ√(-3)} (hcoprime : IsCoprime p.re p.im) (hfour : p.norm = 4) :
    abs p.re = 1 ∧ abs p.im = 1 := by
  apply Spts.four hfour
  rintro him
  rw [him, isCoprime_zero_right, Int.isUnit_iff_abs_eq] at hcoprime
  rw [Zsqrtd.norm_def, him, MulZeroClass.mul_zero, sub_zero, ← sq, ← sq_abs, hcoprime] at hfour
  norm_num at hfour
