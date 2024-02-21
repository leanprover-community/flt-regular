/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FltRegular.FltThree.Primes
import FltRegular.FltThree.Edwards
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic.IntervalCases

/-- solutions to Fermat's last theorem for the exponent `3`. -/
def FltSolution (n : ℕ) (a b c : ℤ) :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ n + b ^ n = c ^ n

/-- Coprime solutions to Fermat's last theorem for the exponent `3`. -/
def FltCoprime (n : ℕ) (a b c : ℤ) :=
  FltSolution n a b c ∧ IsCoprime a b ∧ IsCoprime a c ∧ IsCoprime b c

theorem exists_coprime {n : ℕ} (hn : 0 < n) {a b c : ℤ} (ha' : a ≠ 0) (hb' : b ≠ 0) (hc' : c ≠ 0)
    (h : a ^ n + b ^ n = c ^ n) :
    ∃ a' b' c' : ℤ,
      a'.natAbs ≤ a.natAbs ∧ b'.natAbs ≤ b.natAbs ∧ c'.natAbs ≤ c.natAbs ∧ FltCoprime n a' b' c' :=
  by
  set d := Int.gcd a b with hd'
  obtain ⟨A, HA⟩ : ↑d ∣ a := @Int.gcd_dvd_left a b
  obtain ⟨B, HB⟩ : ↑d ∣ b := @Int.gcd_dvd_right a b
  obtain ⟨C, HC⟩ : ↑d ∣ c :=
    by
    rw [← Int.pow_dvd_pow_iff hn, ← h, HA, HB, mul_pow, mul_pow, ← mul_add]
    exact dvd_mul_right _ _
  have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_left _ ha'
  have hd := Int.coe_nat_ne_zero_iff_pos.mpr hdpos
  have hsoln : A ^ n + B ^ n = C ^ n :=
    by
    apply Int.eq_of_mul_eq_mul_left (pow_ne_zero n hd)
    simp only [mul_add, ← mul_pow, ← HA, ← HB, ← HC, h]
  have hsoln' : B ^ n + A ^ n = C ^ n := by rwa [add_comm] at hsoln
  have hcoprime : IsCoprime A B :=
    by
    rw [← Int.gcd_eq_one_iff_coprime]
    apply Nat.eq_of_mul_eq_mul_left hdpos
    rw [← Int.natAbs_ofNat d, ← Int.gcd_mul_left, ← HA, ← HB, hd', Int.natAbs_ofNat, mul_one]
  have HA' : A.natAbs ≤ a.natAbs := by
    rw [HA]
    simp only [Int.natAbs_ofNat, Int.natAbs_mul]
    exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
  have HB' : B.natAbs ≤ b.natAbs := by
    rw [HB]
    simp only [Int.natAbs_ofNat, Int.natAbs_mul]
    exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
  have HC' : C.natAbs ≤ c.natAbs := by
    rw [HC]
    simp only [Int.natAbs_ofNat, Int.natAbs_mul]
    exact le_mul_of_one_le_left' (Nat.succ_le_iff.mpr hdpos)
  exact
    ⟨A, B, C, HA', HB', HC',
      ⟨right_ne_zero_of_mul (by rwa [HA] at ha'), right_ne_zero_of_mul (by rwa [HB] at hb'),
        right_ne_zero_of_mul (by rwa [HC] at hc'), hsoln⟩,
      hcoprime, coprime_add_self_pow hn hsoln hcoprime,
      coprime_add_self_pow hn hsoln' hcoprime.symm⟩

theorem descent1a {a b c : ℤ} (h : a ^ 3 + b ^ 3 = c ^ 3) (habcoprime : IsCoprime a b)
    (haccoprime : IsCoprime a c) (hbccoprime : IsCoprime b c) :
    (Even a ∧ ¬Even b ∧ ¬Even c ∨ ¬Even a ∧ Even b ∧ ¬Even c) ∨ ¬Even a ∧ ¬Even b ∧ Even c :=
  by
  have contra : ∀ {x y : ℤ}, IsCoprime x y → Even x → Even y → False :=
    by
    intro x y hcoprime hx hy
    rw [even_iff_two_dvd] at hx hy
    have := Int.isUnit_eq_one_or (hcoprime.isUnit_of_dvd' hx hy)
    norm_num at this
  by_cases haparity : Even a <;> by_cases hbparity : Even b <;> by_cases hcparity : Even c
  · exact False.elim (contra habcoprime ‹_› ‹_›)
  · exact False.elim (contra habcoprime ‹_› ‹_›)
  · exact False.elim (contra haccoprime ‹_› ‹_›)
  · tauto
  · exact False.elim (contra hbccoprime ‹_› ‹_›)
  · tauto
  · tauto
  · exfalso
    apply hcparity
    rw [← Int.even_pow' three_ne_zero, ← h]
    simp [haparity, hbparity, three_ne_zero, parity_simps]

theorem flt_not_add_self {a b c : ℤ} (ha : a ≠ 0) (h : a ^ 3 + b ^ 3 = c ^ 3) : a ≠ b :=
  by
  rintro rfl
  rw [← mul_two] at h
  obtain ⟨d, rfl⟩ : a ∣ c :=
    by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 0 < 3), ← h]
    apply dvd_mul_right
  apply Int.two_not_cube d
  rwa [mul_pow, mul_right_inj' (pow_ne_zero 3 ha), eq_comm] at h

theorem descent1left {a b c : ℤ} (hapos : a ≠ 0) (h : a ^ 3 + b ^ 3 = c ^ 3)
    (hbccoprime : IsCoprime b c) (hb : ¬Even b) (hc : ¬Even c) :
    ∃ p q : ℤ,
      p ≠ 0 ∧ q ≠ 0 ∧ IsCoprime p q ∧ (Even p ↔ ¬Even q) ∧ 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 :=
  by
  obtain ⟨p, hp⟩ : Even (c - b) := by simp [hb, hc, parity_simps]
  obtain ⟨q, hq⟩ : Even (c + b) := by simp [hb, hc, parity_simps]
  rw [← two_mul] at hp hq
  obtain rfl : p + q = c := by
    apply Int.eq_of_mul_eq_mul_left two_ne_zero
    rw [mul_add, ← hp, ← hq]
    ring
  obtain rfl : q - p = b := by
    apply Int.eq_of_mul_eq_mul_left two_ne_zero
    rw [mul_sub, ← hp, ← hq]
    ring
  have hpnezero : p ≠ 0 := by
    rintro rfl
    rw [sub_zero, zero_add, add_left_eq_self] at h
    exact hapos (pow_eq_zero h)
  have hqnezero : q ≠ 0 := by
    rintro rfl
    rw [zero_sub, add_zero, Odd.neg_pow (by norm_num; decide), ← sub_eq_add_neg,
      sub_eq_iff_eq_add] at h
    exact flt_not_add_self hpnezero h.symm rfl
  refine' ⟨p, q, hpnezero, hqnezero, _, _, _⟩
  · apply isCoprime_of_dvd _ _ (not_and_of_not_left _ hpnezero)
    rintro z hznu - hzp hzq
    apply hznu
    exact hbccoprime.isUnit_of_dvd' (dvd_sub hzq hzp) (dvd_add hzp hzq)
  · constructor <;> intro H <;> simpa [H, parity_simps] using hc
  · rw [eq_sub_of_add_eq h]
    ring

theorem descent1 (a b c : ℤ) (h : FltCoprime 3 a b c) :
    ∃ p q : ℤ,
      p ≠ 0 ∧
        q ≠ 0 ∧
          IsCoprime p q ∧
            (Even p ↔ ¬Even q) ∧
              (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
                2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨ 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
  by
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h
  obtain (⟨-, hb, hc⟩ | ⟨ha, hb, hc⟩) | ⟨ha, hb, -⟩ :=
    descent1a h habcoprime haccoprime hbccoprime
  · obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hapos h hbccoprime hb hc
    exact ⟨p, q, hp, hq, hcoprime, hodd, Or.inl hcube⟩
  · rw [add_comm] at h
    obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hbpos h haccoprime ha hc
    refine' ⟨p, q, hp, hq, hcoprime, hodd, Or.inr <| Or.inl hcube⟩
  · have := descent1left hcpos ?_ habcoprime.neg_left ?_ hb
    obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := this
    exact ⟨p, q, hp, hq, hcoprime, hodd, Or.inr <| Or.inr hcube⟩
    · rw [← h]
      ring
    · simp [ha, parity_simps]

theorem descent11 {a b c d : ℤ} (h : d = a ∨ d = b ∨ d = c) : d ∣ a * b * c :=
  by
  rcases h with (rfl | rfl | rfl)
  · exact (dvd_mul_right _ _).mul_right _
  · exact (dvd_mul_left _ _).mul_right _
  · exact dvd_mul_left _ _

theorem descent2 (a b c : ℤ) (h : FltCoprime 3 a b c) :
    ∃ p q : ℤ,
      p ≠ 0 ∧
        q ≠ 0 ∧
          IsCoprime p q ∧
            (Even p ↔ ¬Even q) ∧
              (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
                  2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨ 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
                (2 * p).natAbs < (a ^ 3 * b ^ 3 * c ^ 3).natAbs :=
  by
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1 a b c h
  refine' ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩
  obtain ⟨⟨hapos, hbpos, hcpos, -⟩, -⟩ := h
  set P : ℤ√(-3) := ⟨p, q⟩
  apply lt_of_lt_of_le (b := (2 * p * P.norm).natAbs)
  -- calc
  --   (2 * p).natAbs < (2 * p * P.norm).natAbs := ?_
  --   _ ≤ (a ^ 3 * b ^ 3 * c ^ 3).natAbs := ?_

  · rw [Int.natAbs_mul (2 * p)]
    apply lt_mul_of_one_lt_right (Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero hp))
    rw [← Int.ofNat_lt]
    rw [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) P)]
    exact Spts.one_lt_of_im_ne_zero ⟨p, q⟩ hq
  · apply Nat.le_of_dvd
    · rw [pos_iff_ne_zero, Int.natAbs_ne_zero, ← mul_pow, ← mul_pow]
      exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero hapos hbpos) hcpos)
    · rw [Int.natAbs_dvd_natAbs]
      convert descent11 hcube
      rw [Zsqrtd.norm]
      ring


theorem Nat.cast_three [AddMonoidWithOne R] : ((3 : ℕ) : R) = (3 : R) := rfl


theorem gcd1or3 (p q : ℤ) (hp : p ≠ 0) (hcoprime : IsCoprime p q) (hparity : Even p ↔ ¬Even q) :
    Int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ Int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
  by
  set g := Int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) with hg'
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2 by
    obtain ⟨k, hg, hk⟩ := H
    interval_cases k
    · left
      rw [pow_zero] at hg
      exact hg
    · right
      rw [pow_one] at hg
      exact hg
  have basic : ∀ f, Nat.Prime f → (f : ℤ) ∣ 2 * p → (f : ℤ) ∣ p ^ 2 + 3 * q ^ 2 → f = 3 :=
    by
    intro d hdprime hdleft hdright
    by_contra hne3
    rw [← Ne.def] at hne3
    apply (Nat.prime_iff_prime_int.mp hdprime).not_unit
    have hne2 : d ≠ 2 := by
      rintro rfl
      rw [Nat.cast_two, ← even_iff_two_dvd] at hdright
      have : ¬ Even (3 : ℤ) := by decide
      simp [this, hparity, two_ne_zero, parity_simps] at hdright
    have : 2 < d := lt_of_le_of_ne hdprime.two_le hne2.symm
    have : 3 < d := lt_of_le_of_ne this hne3.symm
    obtain ⟨P, hP⟩ := hdleft
    obtain ⟨Q, hQ⟩ := hdright
    obtain ⟨H, hH⟩ : 2 ∣ P := by
      have H := dvd_mul_right 2 p
      rw [hP] at H
      apply (Prime.dvd_or_dvd Int.prime_two H).resolve_left
      rw [Int.coe_nat_dvd_right]
      change ¬2 ∣ d
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hdprime]
      exact hne2.symm
    have hp : p = d * H := by rw [← mul_right_inj' (two_ne_zero' ℤ), hP, hH, mul_left_comm]
    apply hcoprime.isUnit_of_dvd'
    · rw [hp]
      exact dvd_mul_right _ _
    · have h000 : d ∣ 3 * q.natAbs ^ 2 :=
        by
        rw [← Int.coe_nat_dvd, Int.ofNat_mul, Int.coe_nat_pow, Int.natAbs_sq, Nat.cast_three]
        use Q - d * H ^ 2
        rw [mul_sub, ← hQ, hp]
        ring
      cases' (Nat.Prime.dvd_mul hdprime).mp h000 with h000 h000
      · rw [Nat.prime_dvd_prime_iff_eq hdprime Nat.prime_three] at h000
        exact absurd h000 hne3
      · rw [Int.coe_nat_dvd_left]
        exact Nat.Prime.dvd_of_dvd_pow hdprime h000
  set k := g.factors.length
  have hg : g = 3 ^ k := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd
    · apply ne_of_gt
      apply Nat.gcd_pos_of_pos_left
      rw [Int.natAbs_mul]
      apply mul_pos zero_lt_two
      rwa [pos_iff_ne_zero, Int.natAbs_ne_zero]
    intro d hdprime hddvdg
    rw [← Int.coe_nat_dvd] at hddvdg
    apply basic _ hdprime <;> apply dvd_trans hddvdg <;> rw [hg']
    exacts[Int.gcd_dvd_left, Int.gcd_dvd_right]
  refine' ⟨k, hg, _⟩
  by_contra! H
  rw [← pow_mul_pow_sub _ H] at hg
  have : ¬IsUnit (3 : ℤ) := by
    rw [Int.isUnit_iff_natAbs_eq]
    norm_num
  apply this
  have hdvdp : 3 ∣ p :=
    by
    suffices 3 ∣ 2 * p
      by
      apply Int.dvd_mul_cancel_prime' _ dvd_rfl Int.prime_two this
      norm_num
    have : 3 ∣ (g : ℤ) := by
      rw [hg, pow_two, mul_assoc, Int.ofNat_mul]
      apply dvd_mul_right
    exact dvd_trans this Int.gcd_dvd_left
  apply IsCoprime.isUnit_of_dvd' hcoprime hdvdp
  · rw [← Int.pow_dvd_pow_iff zero_lt_two] at hdvdp
    apply Prime.dvd_of_dvd_pow Int.prime_three
    rw [← mul_dvd_mul_iff_left (three_ne_zero' ℤ), ← pow_two, ← dvd_add_right hdvdp]
    refine' dvd_trans _ Int.gcd_dvd_right
    rw [← hg', hg, Int.ofNat_mul]
    apply dvd_mul_right

theorem obscure' (p q : ℤ) (hp : p ≠ 0) (hcoprime : IsCoprime p q) (hparity : Even p ↔ ¬Even q)
    (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
    ∃ a b,
      p = a * (a - 3 * b) * (a + 3 * b) ∧
        q = 3 * b * (a - b) * (a + b) ∧ IsCoprime a b ∧ (Even a ↔ ¬Even b) :=
  by
  obtain ⟨u, hu⟩ := hcube
  obtain ⟨a, b, hp', hq'⟩ := step6 p q u hcoprime hu.symm
  refine' ⟨a, b, _, _, _, _⟩
  · rw [hp']
    ring
  · rw [hq']
    ring
  · apply isCoprime_of_dvd
    · rintro ⟨rfl, rfl⟩
      norm_num at hp'
      contradiction
    rintro k hknu - hkdvdleft hkdvdright
    apply hknu
    apply hcoprime.isUnit_of_dvd'
    · rw [hp']
      apply dvd_sub
      · exact dvd_pow hkdvdleft (by norm_num)
      · rw [mul_comm (9 : ℤ), mul_assoc]
        exact hkdvdleft.mul_right _
    · rw [hq']
      apply dvd_sub
      · exact hkdvdright.mul_left _
      · exact (hkdvdright.pow (by norm_num)).mul_left _
  ·
    by_cases haparity : Even a <;> by_cases hbparity : Even b <;> [skip; tauto; tauto; skip] <;>
      · exfalso
        have : Even p := by
          rw [hp']
          have : ¬ Even (9 : ℤ) := by decide
          simp [this, haparity, hbparity, three_ne_zero, parity_simps]
        have : Even q := by
          rw [hq']
          simp [haparity, hbparity, three_ne_zero, parity_simps]
        tauto

theorem Int.eq_pow_of_mul_eq_pow_odd {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (hk : Odd k)
    (h : a * b = c ^ k) : (∃ d, a = d ^ k) ∧ ∃ e, b = e ^ k := by
  obtain ⟨k, rfl⟩ := hk.exists_bit1
  exact Int.eq_pow_of_mul_eq_pow_bit1 hab h

theorem Int.cube_of_coprime (a b c s : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcoprimeab : IsCoprime a b) (hcoprimeac : IsCoprime a c) (hcoprimebc : IsCoprime b c)
    (hs : a * b * c = s ^ 3) : ∃ A B C, A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ a = A ^ 3 ∧ b = B ^ 3 ∧ c = C ^ 3 :=
  by
  have : Odd 3 := by decide
  obtain ⟨⟨AB, HAB⟩, ⟨C, HC⟩⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd (IsCoprime.mul_left hcoprimeac hcoprimebc) this hs
  obtain ⟨⟨A, HA⟩, ⟨B, HB⟩⟩ := Int.eq_pow_of_mul_eq_pow_odd hcoprimeab this HAB
  refine' ⟨A, B, C, _, _, _, HA, HB, HC⟩ <;> apply ne_zero_pow three_ne_zero
  · rwa [← HA]
  · rwa [← HB]
  · rwa [← HC]

theorem Int.gcd1_coprime12 (u v : ℤ) (huvcoprime : IsCoprime u v) (notdvd_2_2 : ¬2 ∣ u - 3 * v)
    (not_3_dvd_2 : ¬3 ∣ u - 3 * v) : IsCoprime (2 * u) (u - 3 * v) :=
  by
  apply isCoprime_of_prime_dvd
  · rintro ⟨-, h2⟩
    rw [h2] at notdvd_2_2
    norm_num at notdvd_2_2
  intro k hkprime hkdvdleft hkdvdright
  apply hkprime.not_unit
  apply huvcoprime.isUnit_of_dvd'
  · exact Int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright Int.prime_two hkdvdleft
  · apply Int.dvd_mul_cancel_prime' not_3_dvd_2 hkdvdright Int.prime_three
    apply Int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright Int.prime_two
    convert dvd_sub hkdvdleft (hkdvdright.mul_left 2) using 1
    ring

theorem Int.gcd1_coprime13 (u v : ℤ) (huvcoprime : IsCoprime u v) (this' : ¬Even (u + 3 * v))
    (notdvd_3_3 : ¬3 ∣ u + 3 * v) : IsCoprime (2 * u) (u + 3 * v) :=
  by
  rw [even_iff_two_dvd] at this'
  apply isCoprime_of_prime_dvd
  · rintro ⟨-, h2⟩
    rw [h2] at this'
    norm_num at this'
  intro k hkprime hkdvdleft hkdvdright
  apply hkprime.not_unit
  apply huvcoprime.isUnit_of_dvd'
  · exact Int.dvd_mul_cancel_prime' this' hkdvdright Int.prime_two hkdvdleft
  · apply Int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright Int.prime_three
    apply Int.dvd_mul_cancel_prime' this' hkdvdright Int.prime_two
    convert dvd_sub (hkdvdright.mul_left 2) hkdvdleft using 1
    ring

theorem Int.gcd1_coprime23 (u v : ℤ) (huvcoprime : IsCoprime u v) (notdvd_2_2 : ¬2 ∣ u - 3 * v)
    (notdvd_3_3 : ¬3 ∣ u + 3 * v) : IsCoprime (u - 3 * v) (u + 3 * v) :=
  by
  apply isCoprime_of_prime_dvd
  · rintro ⟨h1, -⟩
    rw [h1] at notdvd_2_2
    norm_num at notdvd_2_2
  intro k hkprime hkdvdleft hkdvdright
  apply hkprime.not_unit
  apply huvcoprime.isUnit_of_dvd'
  · apply Int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft Int.prime_two
    convert dvd_add hkdvdleft hkdvdright using 1
    ring
  · apply Int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright Int.prime_three
    apply Int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft Int.prime_two
    convert dvd_sub hkdvdright hkdvdleft using 1
    ring

theorem descent_gcd1 (a b c p q : ℤ) (hp : p ≠ 0) (hcoprime : IsCoprime p q)
    (hodd : Even p ↔ ¬Even q)
    (hcube :
      2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
        2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨ 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
    (hgcd : IsCoprime (2 * p) (p ^ 2 + 3 * q ^ 2)) :
    ∃ a' b' c' : ℤ,
      a' ≠ 0 ∧
        b' ≠ 0 ∧
          c' ≠ 0 ∧ (a' ^ 3 * b' ^ 3 * c' ^ 3).natAbs ≤ (2 * p).natAbs ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
  by
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3 := by
    rcases hcube with (hcube | hcube | hcube) <;> [(use a); (use b); (use c)]
  have : Odd 3 := by decide
  obtain ⟨hcubeleft, hcuberight⟩ := Int.eq_pow_of_mul_eq_pow_odd hgcd this hr
  -- todo shadowing hq
  obtain ⟨u, v, hpfactor, hq, huvcoprime, huvodd⟩ := obscure' p q hp hcoprime hodd hcuberight
  have u_ne_zero : u ≠ 0 := by
    rintro rfl
    rw [MulZeroClass.zero_mul, MulZeroClass.zero_mul] at hpfactor
    contradiction
  have haaa : 2 * p = 2 * u * (u - 3 * v) * (u + 3 * v) :=
    by
    rw [hpfactor]
    ring
  have : ¬ Even (3 : ℤ) := by decide
  have : ¬Even (u - 3 * v) := by simp [‹¬ Even (3 : ℤ)›, huvodd, parity_simps]
  have : ¬Even (u + 3 * v) := by simp [‹¬ Even (3 : ℤ)›, huvodd, parity_simps]
  have notdvd_2_2 : ¬2 ∣ u - 3 * v := by
    rw [← even_iff_two_dvd]
    exact ‹¬Even (u - 3 * v)›
  have hddd : ¬3 ∣ p := by
    intro H
    have : 3 ∣ p ^ 2 + 3 * q ^ 2 := by
      apply dvd_add
      · rw [pow_two]
        exact H.mul_left _
      · apply dvd_mul_right
    have : 3 ∣ 2 * p := H.mul_left 2
    have := IsCoprime.isUnit_of_dvd' hgcd ‹_› ‹_›
    rw [isUnit_iff_dvd_one] at this
    norm_num at this
  have not_3_dvd_2 : ¬3 ∣ u - 3 * v := by
    intro hd2
    apply hddd
    rw [hpfactor]
    exact (hd2.mul_left _).mul_right _
  have notdvd_3_3 : ¬3 ∣ u + 3 * v := by
    intro hd3
    apply hddd
    rw [hpfactor]
    exact hd3.mul_left _
  obtain ⟨s, hs⟩ := hcubeleft
  obtain ⟨C, A, B, HCpos, HApos, HBpos, HC, HA, HB⟩ :
    ∃ X Y Z : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧ 2 * u = X ^ 3 ∧ u - 3 * v = Y ^ 3 ∧ u + 3 * v = Z ^ 3 :=
    by
    apply Int.cube_of_coprime (2 * u) (u - 3 * v) (u + 3 * v) s
    · apply mul_ne_zero two_ne_zero u_ne_zero
    · rw [sub_ne_zero]
      rintro rfl
      simp only [‹¬ Even (3 : ℤ)›, false_or_iff, iff_not_self, parity_simps] at huvodd
    · intro H
      rw [add_eq_zero_iff_eq_neg] at H
      apply iff_not_self
      simpa [‹¬ Even (3 : ℤ)›, H, parity_simps] using huvodd
    · apply Int.gcd1_coprime12 u v <;> assumption
    · apply Int.gcd1_coprime13 u v <;> assumption
    · apply Int.gcd1_coprime23 u v <;> assumption
    · rw [← haaa]
      exact hs
  refine' ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩
  · rw [mul_comm, ← mul_assoc (C ^ 3), ← HA, ← HB, ← HC, ← haaa]
  · rw [← HA, ← HB, ← HC]
    ring

theorem gcd3_coprime {u v : ℤ} (huvcoprime : IsCoprime u v) (huvodd : Even u ↔ ¬Even v) :
    IsCoprime (2 * v) (u + v) ∧ IsCoprime (2 * v) (u - v) ∧ IsCoprime (u - v) (u + v) :=
  by
  have haddodd : ¬Even (u + v) := by simp [huvodd, parity_simps]
  have hsubodd : ¬Even (u - v) := by simp [huvodd, parity_simps]
  have haddcoprime : IsCoprime (u + v) (2 * v) :=
    by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h1, -⟩
      rw [h1] at haddodd
      norm_num at haddodd
    intro k hkprime hkdvdleft hkdvdright
    apply hkprime.not_unit
    have hkdvdright' : k ∣ v := by
      rw [even_iff_two_dvd] at haddodd
      exact Int.dvd_mul_cancel_prime' haddodd hkdvdleft Int.prime_two hkdvdright
    apply huvcoprime.isUnit_of_dvd' _ hkdvdright'
    rw [← add_sub_cancel u v]
    apply dvd_sub hkdvdleft hkdvdright'
  have hsubcoprime : IsCoprime (u - v) (2 * v) :=
    by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h1, -⟩
      rw [h1] at hsubodd
      norm_num at hsubodd
    intro k hkprime hkdvdleft hkdvdright
    apply hkprime.not_unit
    have hkdvdright' : k ∣ v := by
      rw [even_iff_two_dvd] at hsubodd
      exact Int.dvd_mul_cancel_prime' hsubodd hkdvdleft Int.prime_two hkdvdright
    apply huvcoprime.isUnit_of_dvd' _ hkdvdright'
    rw [← sub_add_cancel u v]
    exact dvd_add hkdvdleft hkdvdright'
  have haddsubcoprime : IsCoprime (u + v) (u - v) :=
    by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h1, -⟩
      rw [h1] at haddodd
      norm_num at haddodd
    intro k hkprime hkdvdleft hkdvdright
    apply hkprime.not_unit
    rw [even_iff_two_dvd] at haddodd
    apply huvcoprime.isUnit_of_dvd' <;>
      apply Int.dvd_mul_cancel_prime' haddodd hkdvdleft Int.prime_two
    · convert dvd_add hkdvdleft hkdvdright using 1
      ring
    · convert dvd_sub hkdvdleft hkdvdright using 1
      ring
  exact ⟨haddcoprime.symm, hsubcoprime.symm, haddsubcoprime.symm⟩

theorem descent_gcd3_coprime {q s : ℤ} (h3_ndvd_q : ¬3 ∣ q) (hspos : s ≠ 0)
    (hcoprime' : IsCoprime s q) (hodd' : Even q ↔ ¬Even s) :
    IsCoprime (3 ^ 2 * 2 * s) (q ^ 2 + 3 * s ^ 2) :=
  by
  have h2ndvd : ¬2 ∣ q ^ 2 + 3 * s ^ 2 :=
    by
    rw [← even_iff_two_dvd]
    have : ¬ Even (3 : ℤ) := by decide
    simp [this, two_ne_zero, hodd', parity_simps]
  have h3ndvd : ¬3 ∣ q ^ 2 + 3 * s ^ 2 := by
    intro H
    apply h3_ndvd_q
    rw [dvd_add_left (dvd_mul_right _ _)] at H
    exact Prime.dvd_of_dvd_pow Int.prime_three H
  apply isCoprime_of_prime_dvd
  · rintro ⟨h1, -⟩
    rw [mul_eq_zero] at h1
    exact hspos (h1.resolve_left (by norm_num))
  intro k hkprime hkdvdleft hkdvdright
  apply hkprime.not_unit
  have : k ∣ s := by
    apply Int.dvd_mul_cancel_prime' h2ndvd hkdvdright Int.prime_two
    apply Int.dvd_mul_cancel_prime' h3ndvd hkdvdright Int.prime_three
    apply Int.dvd_mul_cancel_prime' h3ndvd hkdvdright Int.prime_three
    convert hkdvdleft using 1
    ring
  apply hcoprime'.isUnit_of_dvd' this
  apply hkprime.dvd_of_dvd_pow
  rw [← dvd_add_left ((this.pow two_ne_zero).mul_left _)]
  exact hkdvdright

theorem descent_gcd3 (a b c p q : ℤ) (hp : p ≠ 0) (hq : q ≠ 0) (hcoprime : IsCoprime p q)
    (hodd : Even p ↔ ¬Even q)
    (hcube :
      2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
        2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨ 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
    (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
    ∃ a' b' c' : ℤ,
      a' ≠ 0 ∧
        b' ≠ 0 ∧
          c' ≠ 0 ∧ (a' ^ 3 * b' ^ 3 * c' ^ 3).natAbs ≤ (2 * p).natAbs ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
  by
  -- 1.
  have h3_dvd_p : 3 ∣ p :=
    by
    apply Int.dvd_mul_cancel_prime' _ dvd_rfl Int.prime_two
    · zify  at hgcd
      rw [← hgcd]
      exact Int.gcd_dvd_left
    · norm_num
  have h3_ndvd_q : ¬3 ∣ q := by
    intro H
    have := hcoprime.isUnit_of_dvd' h3_dvd_p H
    rw [Int.isUnit_iff_natAbs_eq] at this
    norm_num at this
  -- 2.
  obtain ⟨s, rfl⟩ := h3_dvd_p
  have hspos : s ≠ 0 := right_ne_zero_of_mul hp
  have hps : 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) = 3 ^ 2 * 2 * s * (q ^ 2 + 3 * s ^ 2) := by
    ring
  -- 3.
  have hcoprime' : IsCoprime s q := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨h1, -⟩
      exact hspos h1
    intro k hkprime hkdvdleft hkdvdright
    apply hkprime.not_unit
    apply hcoprime.isUnit_of_dvd' _ hkdvdright
    exact hkdvdleft.mul_left 3
  have hodd' : Even q ↔ ¬Even s :=
    by
    rw [Iff.comm, not_iff_comm, Iff.comm]
    have : ¬ Even (3 : ℤ) := by decide
    simpa [this, parity_simps] using hodd
  have hcoprime'' : IsCoprime (3 ^ 2 * 2 * s) (q ^ 2 + 3 * s ^ 2) :=
    descent_gcd3_coprime h3_ndvd_q hspos hcoprime' hodd'
  -- 4.
  obtain ⟨r, hr⟩ : ∃ r, 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) = r ^ 3 := by
    rcases hcube with (hcube | hcube | hcube) <;> [(use a); (use b); (use c)]
  rw [hps] at hr
  have : Odd 3 := by norm_num; decide
  obtain ⟨hcubeleft, hcuberight⟩ := Int.eq_pow_of_mul_eq_pow_odd hcoprime'' this hr
  -- 5.
  -- todo shadows hq hq
  obtain ⟨u, v, hq, hs, huvcoprime, huvodd⟩ := obscure' q s hq hcoprime'.symm hodd' hcuberight
  have hv : v ≠ 0 := by
    rintro rfl
    norm_num at hs
    contradiction
  -- 6.
  obtain ⟨haddcoprime, hsubcoprime, haddsubcoprime⟩ := gcd3_coprime huvcoprime huvodd
  -- 7.
  obtain ⟨e, he⟩ := hcubeleft
  have : 3 ∣ e :=
    by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 0 < 3), ← he, hs]
    convert dvd_mul_right _ (2 * v * (u - v) * (u + v)) using 1
    norm_num
    ring
  obtain ⟨t, rfl⟩ := this
  have ht : 2 * v * (u - v) * (u + v) = t ^ 3 :=
    by
    have : (3 ^ 3 : ℤ) ≠ 0 := by norm_num
    rw [← mul_right_inj' this, ← mul_pow, ← he, hs]
    ring
  obtain ⟨A, B, C, HApos, HBpos, HCpos, HA, HB, HC⟩ :
    ∃ X Y Z : ℤ, X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧ 2 * v = X ^ 3 ∧ u - v = Y ^ 3 ∧ u + v = Z ^ 3 :=
    by
    apply Int.cube_of_coprime
    · exact mul_ne_zero two_ne_zero hv
    · intro H
      rw [sub_eq_zero] at H
      apply iff_not_self
      simpa [H, parity_simps] using huvodd
    · intro H
      rw [add_eq_zero_iff_eq_neg] at H
      apply iff_not_self
      simpa [H, parity_simps] using huvodd
    · exact hsubcoprime
    · exact haddcoprime
    · exact haddsubcoprime
    · exact ht
  refine' ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩
  -- 9.
  · rw [← mul_assoc, mul_comm, ← mul_assoc (C ^ 3), ← HA, ← HB, ← HC]
    set x := v * (u - v) * (u + v) with hx
    calc
      ((u + v) * (2 * v) * (u - v)).natAbs = (2 * x).natAbs :=
        by
        rw [hx]
        congr 1
        ring
      _ = 2 * x.natAbs := by
        rw [Int.natAbs_mul 2]
        rfl
      _ ≤ 3 * x.natAbs := (Nat.mul_le_mul_right _ (by norm_num))
      _ = (3 * x).natAbs := by
        rw [Int.natAbs_mul 3]
        rfl
      _ = s.natAbs := by
        rw [hx, hs]
        congr 1
        ring
      _ ≤ 2 * 3 * s.natAbs := (Nat.le_mul_of_pos_left _ (by norm_num))
      _ = (2 * 3 * s).natAbs := by
        rw [Int.natAbs_mul (2 * 3)]
        rfl

  · rw [← HA, ← HB, ← HC]
    ring

theorem descent (a b c : ℤ) (h : FltCoprime 3 a b c) :
    ∃ a' b' c' : ℤ,
      a' ≠ 0 ∧
        b' ≠ 0 ∧ c' ≠ 0 ∧ (a' * b' * c').natAbs < (a * b * c).natAbs ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
  by
  -- 3.
  have := descent2 a b c h
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this
  suffices
    ∃ a' b' c' : ℤ,
      a' ≠ 0 ∧
        b' ≠ 0 ∧
          c' ≠ 0 ∧ (a' ^ 3 * b' ^ 3 * c' ^ 3).natAbs ≤ (2 * p).natAbs ∧ a' ^ 3 + b' ^ 3 = c' ^ 3
    by
    obtain ⟨a', b', c', ha', hb', hc', hsmaller, hsolution⟩ := this
    refine' ⟨a', b', c', ha', hb', hc', _, hsolution⟩
    rw [← Nat.pow_lt_pow_iff_left three_ne_zero]
    convert lt_of_le_of_lt hsmaller haaa <;> simp [mul_pow, Int.natAbs_mul, Int.natAbs_pow]
  -- 4.
  cases' gcd1or3 p q hp hcoprime hodd with hgcd hgcd
  -- 5.
  · rw [Int.gcd_eq_one_iff_coprime] at hgcd
    apply descent_gcd1 a b c p q hp hcoprime hodd hcube hgcd
  · apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube hgcd

theorem flt_three : FermatLastTheoremWith ℤ 3 := by
  intros a b c ha hb hc
  induction' h : (a * b * c).natAbs using Nat.strong_induction_on with k' IH generalizing a b c
  intro H
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ := exists_coprime zero_lt_three ha hb hc H
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime
  refine' IH (x' * y' * z').natAbs _ _ _ _ hx'pos hy'pos hz'pos rfl hsolution
  apply lt_of_lt_of_le hsmaller
  rw [← h]
  simp only [Int.natAbs_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul hxle hyle) hzle
