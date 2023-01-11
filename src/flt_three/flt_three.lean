/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import data.int.basic
import data.int.parity
import data.nat.gcd.big_operators
import data.pnat.basic
import algebra.gcd_monoid.basic
import tactic
import data.nat.modeq
import ring_theory.int.basic
import .primes
import .edwards

/-!
# Fermat's Last Theorem for the case n = 3

There are no non-zero integers `a`, `b` and `c` such that `a ^ 3 + b ^ 3 = c ^ 3`.

This follows the proof by Euler as presented by H. M. Edwards in
*Fermat's Last Theorem: A Genetic Introduction to Algebraic Number Theory*, pp. 39-54.
-/

/-- solutions to Fermat's last theorem for the exponent `3`. -/
def flt_solution
  (n : ℕ)
  (a b c : ℤ) :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
  a ^ n + b ^ n = c ^ n

/-- Coprime solutions to Fermat's last theorem for the exponent `3`. -/
def flt_coprime
  (n : ℕ)
  (a b c : ℤ) :=
  flt_solution n a b c ∧
  is_coprime a b ∧
  is_coprime a c ∧
  is_coprime b c

lemma exists_coprime
  {n : ℕ}
  (hn : 0 < n)
  {a b c : ℤ}
  (ha' : a ≠ 0)
  (hb' : b ≠ 0)
  (hc' : c ≠ 0)
  (h : a ^ n + b ^ n = c ^ n) :
  ∃ a' b' c' : ℤ,
    a'.nat_abs ≤ a.nat_abs ∧ b'.nat_abs ≤ b.nat_abs ∧ c'.nat_abs ≤ c.nat_abs ∧
    flt_coprime n a' b' c' :=
begin
  set d := int.gcd a b with hd',
  obtain ⟨A, HA⟩ : ↑d ∣ a := int.gcd_dvd_left a b,
  obtain ⟨B, HB⟩ : ↑d ∣ b := int.gcd_dvd_right a b,
  obtain ⟨C, HC⟩ : ↑d ∣ c,
  { rw [←int.pow_dvd_pow_iff hn, ←h, HA, HB, mul_pow, mul_pow, ←mul_add],
    exact dvd_mul_right (↑d ^ n) (A ^ n + B ^ n) },
  have hdpos : 0 < d := int.gcd_pos_of_non_zero_left _ ha',
  have hd := int.coe_nat_ne_zero_iff_pos.mpr hdpos,
  have hsoln : A ^ n + B ^ n = C ^ n,
  { apply int.eq_of_mul_eq_mul_left (pow_ne_zero n hd),
    simp only [mul_add, ←mul_pow, ←HA, ←HB, ←HC, h] },
  have hsoln' : B ^ n + A ^ n = C ^ n,
  { rwa add_comm at hsoln },
  have hcoprime : is_coprime A B,
  { rw ←int.gcd_eq_one_iff_coprime,
    apply nat.eq_of_mul_eq_mul_left hdpos,
    rw [←int.nat_abs_of_nat d, ←int.gcd_mul_left, ←HA, ←HB, hd', int.nat_abs_of_nat, mul_one] },
  have HA' : A.nat_abs ≤ a.nat_abs,
  { rw HA,
    simp only [int.nat_abs_of_nat, int.nat_abs_mul],
    exact le_mul_of_one_le_left' (nat.succ_le_iff.mpr hdpos) },
  have HB' : B.nat_abs ≤ b.nat_abs,
  { rw HB,
    simp only [int.nat_abs_of_nat, int.nat_abs_mul],
    exact le_mul_of_one_le_left' (nat.succ_le_iff.mpr hdpos) },
  have HC' : C.nat_abs ≤ c.nat_abs,
  { rw HC,
    simp only [int.nat_abs_of_nat, int.nat_abs_mul],
    exact le_mul_of_one_le_left' (nat.succ_le_iff.mpr hdpos) },
  exact ⟨
    A,
    B,
    C,
    HA',
    HB',
    HC',
    ⟨
      right_ne_zero_of_mul (by rwa HA at ha'),
      right_ne_zero_of_mul (by rwa HB at hb'),
      right_ne_zero_of_mul (by rwa HC at hc'),
      hsoln
    ⟩,
    hcoprime,
    coprime_add_self_pow hn hsoln hcoprime,
    coprime_add_self_pow hn hsoln' hcoprime.symm
  ⟩,
end

lemma descent1a {a b c : ℤ}
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (habcoprime : is_coprime a b)
  (haccoprime : is_coprime a c)
  (hbccoprime : is_coprime b c) :
  (even a ∧ ¬even b ∧ ¬even c ∨
   ¬even a ∧ even b ∧ ¬even c) ∨
  ¬even a ∧ ¬even b ∧ even c :=
begin
  have contra : ∀ {x y : ℤ}, is_coprime x y → even x → even y → false,
  { intros x y hcoprime hx hy,
    rw even_iff_two_dvd at hx hy,
    have := int.is_unit_eq_one_or (hcoprime.is_unit_of_dvd' hx hy),
    norm_num at this },
  by_cases haparity : even a;
  by_cases hbparity : even b;
  by_cases hcparity : even c,
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra haccoprime ‹_› ‹_›) },
  { tauto },
  { exact false.elim (contra hbccoprime ‹_› ‹_›) },
  { tauto },
  { tauto },
  { exfalso,
    apply hcparity,
    rw [←int.even_pow' three_ne_zero, ←h],
    simp [haparity, hbparity, three_ne_zero] with parity_simps },
end

lemma flt_not_add_self {a b c : ℤ} (ha : a ≠ 0) (h : a ^ 3 + b ^ 3 = c ^ 3) : a ≠ b :=
begin
  rintro rfl,
  rw ←mul_two at h,
  obtain ⟨d, rfl⟩ : a ∣ c,
  { rw [←int.pow_dvd_pow_iff (by norm_num : 0 < 3), ←h],
    apply dvd_mul_right },
  apply int.two_not_cube d,
  rwa [mul_pow, mul_right_inj' (pow_ne_zero 3 ha), eq_comm] at h,
end

lemma descent1left {a b c : ℤ}
  (hapos : a ≠ 0)
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (hbccoprime : is_coprime b c)
  (hb : ¬even b)
  (hc : ¬even c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
      q ≠ 0 ∧
        is_coprime p q ∧
          (even p ↔ ¬even q) ∧
            2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 :=
begin
  obtain ⟨p, hp⟩ : even (c - b),
  { simp [hb, hc] with parity_simps},
  obtain ⟨q, hq⟩ : even (c + b),
  { simp [hb, hc] with parity_simps},
  rw ←two_mul at hp hq,
  obtain rfl : p + q = c,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_add, ←hp, ←hq],
    ring },
  obtain rfl : q - p = b,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_sub, ←hp, ←hq],
    ring },
  have hpnezero : p ≠ 0,
  { rintro rfl,
    rw [sub_zero, zero_add, add_left_eq_self] at h,
    exact hapos (pow_eq_zero h) },

  have hqnezero : q ≠ 0,
  { rintro rfl,
    rw [zero_sub, add_zero, neg_pow_bit1, ←sub_eq_add_neg, sub_eq_iff_eq_add] at h,
    exact flt_not_add_self hpnezero h.symm rfl },

  refine ⟨p, q, hpnezero, hqnezero, _, _, _⟩,
  { apply is_coprime_of_dvd _ _ (not_and_of_not_left _ hpnezero),
    intros z hznu hznz hzp hzq,
    apply hznu,
    exact hbccoprime.is_unit_of_dvd' (dvd_sub hzq hzp) (dvd_add hzp hzq) },
  { split; intro H; simpa [H] with parity_simps using hc },
  { rw [eq_sub_of_add_eq h],
    ring },
end

lemma descent1 (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
    q ≠ 0 ∧
    is_coprime p q ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,

  obtain (⟨ha, hb, hc⟩|⟨ha, hb, hc⟩)|⟨ha, hb, hc⟩ := descent1a h habcoprime haccoprime hbccoprime,
  { obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hapos h hbccoprime hb hc,
    exact ⟨p, q, hp, hq, hcoprime, hodd, or.inl hcube⟩ },
  { rw add_comm at h,
    obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hbpos h haccoprime ha hc,
    refine ⟨p, q, hp, hq, hcoprime, hodd, or.inr $ or.inl hcube⟩ },
  { obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hcpos _ habcoprime.neg_left _ hb,
    exact ⟨p, q, hp, hq, hcoprime, hodd, or.inr $ or.inr hcube⟩,
    { rw ←h, ring },
    { simp [ha] with parity_simps } },
end

lemma descent11 {a b c d : ℤ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { exact (dvd_mul_right _ _).mul_right _ },
  { exact (dvd_mul_left _ _).mul_right _ },
  { exact dvd_mul_left _ _ }
end

lemma descent2 (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
    q ≠ 0 ∧
    is_coprime p q ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    ((2 * p).nat_abs < (a ^ 3 * b ^ 3 * c ^ 3).nat_abs) :=
begin
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1 a b c h,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,

  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, -⟩ := h,
  set P : ℤ√-3 := ⟨p, q⟩,
  calc (2 * p).nat_abs < (2 * p * P.norm).nat_abs : _
  ... ≤ (a ^ 3 * b ^ 3 * c ^ 3).nat_abs : _,
  { rw [int.nat_abs_mul (2 * p)],
    apply lt_mul_of_one_lt_right (int.nat_abs_pos_of_ne_zero (mul_ne_zero two_ne_zero hp)),
    rw [← int.coe_nat_lt_coe_nat_iff],
    rw int.nat_abs_of_nonneg (zsqrtd.norm_nonneg (by norm_num) P),
    exact spts.one_lt_of_im_ne_zero ⟨p, q⟩ hq },
  { apply nat.le_of_dvd,
    { rw [pos_iff_ne_zero, int.nat_abs_ne_zero, ←mul_pow, ←mul_pow],
      exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero hapos hbpos) hcpos) },
    { rw int.nat_abs_dvd_iff_dvd,
      convert descent11 hcube,
      rw [zsqrtd.norm],
      ring } }
end

lemma gcd1or3
  (p q : ℤ)
  (hp : p ≠ 0)
  (hcoprime : is_coprime p q)
  (hparity : even p ↔ ¬even q) :
  int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  set g := int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) with hg',
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2,
  { obtain ⟨k, hg, hk⟩ := H,
    interval_cases k,
    { left, rw pow_zero at hg, exact hg },
    { right, rw pow_one at hg, exact hg } },

  have basic : ∀ f, nat.prime f → (f : ℤ) ∣ 2 * p → (f : ℤ) ∣ (p ^ 2 + 3 * q ^ 2) → f = 3,
  { intros d hdprime hdleft hdright,
    by_contra hne3,
    rw ←ne.def at hne3,
    apply (nat.prime_iff_prime_int.mp hdprime).not_unit,

    have hne2 : d ≠ 2,
    { rintro rfl,
      rw [int.coe_nat_bit0, int.coe_nat_one, ←even_iff_two_dvd] at hdright,
      simpa [hparity, two_ne_zero] with parity_simps using hdright },
    have : 2 < d := lt_of_le_of_ne (hdprime.two_le) hne2.symm,
    have : 3 < d := lt_of_le_of_ne (this) hne3.symm,
    obtain ⟨P, hP⟩ := hdleft,
    obtain ⟨Q, hQ⟩ := hdright,
    obtain ⟨H, hH⟩ : 2 ∣ P,
    { have H := dvd_mul_right 2 p,
      rw [hP] at H,
      apply (prime.dvd_or_dvd int.prime_two H).resolve_left,
      rw int.coe_nat_dvd_right,
      change ¬(2 ∣ d),
      rw nat.prime_dvd_prime_iff_eq nat.prime_two hdprime,
      exact hne2.symm },
    have hp : p = d * H,
    { rw [←mul_right_inj' (two_ne_zero' ℤ), hP, hH, mul_left_comm] },

    apply hcoprime.is_unit_of_dvd',
    { rw hp, exact dvd_mul_right d H },
    { have h000 : d ∣ 3 * q.nat_abs ^ 2,
      { rw [←int.coe_nat_dvd, int.coe_nat_mul, int.coe_nat_pow, int.nat_abs_sq, int.coe_nat_bit1,
          int.coe_nat_one],
        use (Q - d * H ^ 2),
        rw [mul_sub, ←hQ, hp],
        ring },
      cases (nat.prime.dvd_mul hdprime).mp h000 with h000 h000,
      { rw nat.prime_dvd_prime_iff_eq hdprime nat.prime_three at h000,
        exact absurd h000 hne3 },
      { rw int.coe_nat_dvd_left,
        exact nat.prime.dvd_of_dvd_pow hdprime h000 } } },

  set k := g.factors.length,
  have hg : g = 3 ^ k,
  { apply nat.eq_prime_pow_of_unique_prime_dvd,
    { apply ne_of_gt,
      apply nat.gcd_pos_of_pos_left,
      rw int.nat_abs_mul,
      apply nat.mul_pos zero_lt_two,
      rwa [pos_iff_ne_zero, int.nat_abs_ne_zero], },
    intros d hdprime hddvdg,
    rw ←int.coe_nat_dvd at hddvdg,
    apply basic _ hdprime; apply dvd_trans hddvdg; rw hg',
    exacts [int.gcd_dvd_left _ _, int.gcd_dvd_right _ _] },
  refine ⟨k, hg, _⟩,
  by_contra' H,
  rw ←pow_mul_pow_sub _ H at hg,
  have : ¬is_unit (3 : ℤ),
  { rw int.is_unit_iff_nat_abs_eq, norm_num },
  apply this,
  have hdvdp : 3 ∣ p,
  { suffices : 3 ∣ 2 * p,
    { apply int.dvd_mul_cancel_prime' _ dvd_rfl int.prime_two this,
      norm_num, },
    have : 3 ∣ (g : ℤ),
    { rw [hg, pow_two, mul_assoc, int.coe_nat_mul],
      apply dvd_mul_right },
    exact dvd_trans this (int.gcd_dvd_left _ _) },
  apply is_coprime.is_unit_of_dvd' hcoprime hdvdp,
  { rw ←int.pow_dvd_pow_iff zero_lt_two at hdvdp,
    apply prime.dvd_of_dvd_pow int.prime_three,
    rw [←mul_dvd_mul_iff_left (three_ne_zero' ℤ), ←pow_two, dvd_add_iff_right hdvdp],
    refine dvd_trans _ (int.gcd_dvd_right (2 * p) (p ^ 2 + 3 * q ^ 2)),
    rw [←hg', hg, int.coe_nat_mul],
    apply dvd_mul_right }
end

lemma obscure'
  (p q : ℤ)
  (hp : p ≠ 0)
  (hcoprime : is_coprime p q)
  (hparity : even p ↔ ¬even q)
  (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
  ∃ a b,
    p = a * (a - 3 * b) * (a + 3 * b) ∧
    q = 3 * b * (a - b) * (a + b) ∧
    is_coprime a b ∧
    (even a ↔ ¬even b) :=
begin
  obtain ⟨u, hu⟩ := hcube,

  obtain ⟨a, b, hp', hq'⟩ := step6 p q u hcoprime hu.symm,
  refine ⟨a, b, _, _, _, _⟩,
  { rw hp', ring },
  { rw hq', ring },
  { apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      norm_num at hp' },

    intros k hknu hknezero hkdvdleft hkdvdright,
    apply hknu,
    apply hcoprime.is_unit_of_dvd',
    { rw hp',
      apply dvd_sub,
      { exact dvd_pow hkdvdleft (by norm_num) },
      { rw [mul_comm (9 : ℤ), mul_assoc],
        exact hkdvdleft.mul_right _ } },
    { rw hq',
      apply dvd_sub,
      { exact hkdvdright.mul_left _ },
      { exact (hkdvdright.pow (by norm_num)).mul_left _ } } },

  { by_cases haparity : even a; by_cases hbparity : even b;
    [skip, tauto, tauto, skip];
    { exfalso,
      have : even p,
      { rw [hp'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      have : even q,
      { rw [hq'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      tauto } }
end

lemma int.cube_of_coprime (a b c s : ℤ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (hcoprimeab : is_coprime a b)
  (hcoprimeac : is_coprime a c)
  (hcoprimebc : is_coprime b c)
  (hs : a * b * c = s ^ 3) :
  ∃ A B C, A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ a = A ^ 3 ∧ b = B ^ 3 ∧ c = C ^ 3 :=
begin
  obtain ⟨⟨AB, HAB⟩, ⟨C, HC⟩⟩ := int.eq_pow_of_mul_eq_pow_bit1
    (is_coprime.mul_left hcoprimeac hcoprimebc) hs,
  obtain ⟨⟨A, HA⟩, ⟨B, HB⟩⟩ := int.eq_pow_of_mul_eq_pow_bit1 hcoprimeab HAB,
  refine ⟨A, B, C, _, _, _, HA, HB, HC⟩; apply ne_zero_pow three_ne_zero,
  { rwa [←HA] },
  { rwa [←HB] },
  { rwa [←HC] },
end

lemma int.gcd1_coprime12 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (not_3_dvd_2 : ¬3 ∣ u - 3 * v) :
  is_coprime (2 * u) (u - 3 * v) :=
begin
  apply is_coprime_of_prime_dvd,
  { rintro ⟨-, h2⟩,
    norm_num [h2] at notdvd_2_2 },
  intros k hkprime hkdvdleft hkdvdright,
  apply hkprime.not_unit,
  apply huvcoprime.is_unit_of_dvd',
  { exact int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright int.prime_two hkdvdleft },
  { apply int.dvd_mul_cancel_prime' not_3_dvd_2 hkdvdright int.prime_three,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright int.prime_two,
    convert dvd_sub hkdvdleft (hkdvdright.mul_left 2),
    ring },
end

lemma int.gcd1_coprime13 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (this : ¬even (u + 3 * v))
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  is_coprime (2 * u) (u + 3 * v) :=
begin
  rw even_iff_two_dvd at this,
  apply is_coprime_of_prime_dvd,
  { rintro ⟨-, h2⟩,
    norm_num [h2] at this },
  intros k hkprime hkdvdleft hkdvdright,
  apply hkprime.not_unit,
  apply huvcoprime.is_unit_of_dvd',
  { exact int.dvd_mul_cancel_prime' this hkdvdright int.prime_two hkdvdleft },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright int.prime_three,
    apply int.dvd_mul_cancel_prime' this hkdvdright int.prime_two,
    convert dvd_sub (hkdvdright.mul_left 2) hkdvdleft,
    ring },
end

lemma int.gcd1_coprime23 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  is_coprime (u - 3 * v) (u + 3 * v) :=
begin
  apply is_coprime_of_prime_dvd,
  { rintro ⟨h1, -⟩,
    norm_num [h1] at notdvd_2_2 },
  intros k hkprime hkdvdleft hkdvdright,
  apply hkprime.not_unit,
  apply huvcoprime.is_unit_of_dvd',
  { apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft int.prime_two,
    convert dvd_add hkdvdleft hkdvdright,
    ring },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright int.prime_three,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft int.prime_two,
    convert dvd_sub hkdvdright hkdvdleft,
    ring },
end

lemma descent_gcd1 (a b c p q : ℤ)
  (hp : p ≠ 0)
  (hcoprime : is_coprime p q)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime 3 a b c)
  (hgcd : is_coprime (2 * p) (p ^ 2 + 3 * q ^ 2)) :
  ∃ (a' b' c' : ℤ),
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 2.
  have h' := h,
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  obtain ⟨hcubeleft, hcuberight⟩ := int.eq_pow_of_mul_eq_pow_bit1 hgcd hr,
  -- todo shadowing hq
  obtain ⟨u, v, hpfactor, hq, huvcoprime, huvodd⟩ := obscure' p q hp hcoprime hodd hcuberight,
  have u_ne_zero : u ≠ 0,
  { rintro rfl,
    rw [zero_mul, zero_mul] at hpfactor,
    contradiction },
  have haaa : 2 * p = (2 * u) * (u - 3 * v) * (u + 3 * v),
  { rw hpfactor, ring },
  have : ¬even (u - 3 * v),
  { simp [huvodd] with parity_simps },
  have : ¬even (u + 3 * v),
  { simp [huvodd] with parity_simps },
  have notdvd_2_2 : ¬(2 ∣ u - 3 * v),
  { rw ←even_iff_two_dvd,
    exact ‹¬even (u - 3 * v)› },
  have hddd : ¬(3 ∣ p),
  { intro H,
    have : 3 ∣ p ^ 2 + 3 * q ^ 2,
    { apply dvd_add,
      { rw pow_two,
        exact H.mul_left _ },
      { apply dvd_mul_right } },
    have : 3 ∣ 2 * p := H.mul_left 2,
    have := is_coprime.is_unit_of_dvd' hgcd ‹_› ‹_›,
    rw is_unit_iff_dvd_one at this,
    norm_num at this },
  have not_3_dvd_2 : ¬(3 ∣ (u - 3 * v)),
  { intro hd2,
    apply hddd,
    rw hpfactor,
    exact (hd2.mul_left _).mul_right _ },
  have notdvd_3_3 : ¬(3 ∣ (u + 3 * v)),
  { intro hd3,
    apply hddd,
    rw hpfactor,
    exact hd3.mul_left _ },

  obtain ⟨s, hs⟩ := hcubeleft,
  obtain ⟨C, A, B, HCpos, HApos, HBpos, HC, HA, HB⟩ : ∃ X Y Z : ℤ,
    X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    2 * u = X ^ 3 ∧ u - 3 * v = Y ^ 3 ∧ u + 3 * v = Z ^ 3,
  { apply int.cube_of_coprime (2 * u) (u - 3 * v) (u + 3 * v) s,
    { apply mul_ne_zero two_ne_zero u_ne_zero },
    { rw sub_ne_zero,
      rintro rfl,
      simpa only [int.not_even_bit1, false_or, iff_not_self] with parity_simps using huvodd },
    { intro H,
      rw add_eq_zero_iff_eq_neg at H,
      simpa [H] with parity_simps using huvodd },
    { apply int.gcd1_coprime12 u v; assumption },
    { apply int.gcd1_coprime13 u v; assumption },
    { apply int.gcd1_coprime23 u v; assumption },
    { rw ←haaa, exact hs } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,
  { rw [mul_comm, ←mul_assoc (C ^ 3), ←HA, ←HB, ←HC, ←haaa] },
  { rw [←HA, ←HB, ←HC], ring },
end

lemma gcd3_coprime
  {u v : ℤ}
  (huvcoprime: is_coprime u v)
  (huvodd : even u ↔ ¬even v) :
  is_coprime (2 * v) (u + v) ∧ is_coprime (2 * v) (u - v) ∧ is_coprime (u - v) (u + v) :=
begin
  have haddodd : ¬even (u + v),
  { simp [huvodd] with parity_simps },
  have hsubodd : ¬even (u - v),
  { simp [huvodd] with parity_simps },

  have haddcoprime : is_coprime (u + v) (2 * v),
  { apply is_coprime_of_prime_dvd,
    { rintro ⟨h1, -⟩,
      norm_num [h1] at haddodd },
    intros k hkprime hkdvdleft hkdvdright,
    apply hkprime.not_unit,
    have hkdvdright' : k ∣ v,
    { rw even_iff_two_dvd at haddodd,
      exact int.dvd_mul_cancel_prime' haddodd hkdvdleft int.prime_two hkdvdright },

    apply huvcoprime.is_unit_of_dvd' _ hkdvdright',
    rw [←add_sub_cancel u v],
    apply dvd_sub hkdvdleft hkdvdright' },
  have hsubcoprime : is_coprime (u - v) (2 * v),
  { apply is_coprime_of_prime_dvd,
    { rintro ⟨h1, -⟩,
      norm_num [h1] at hsubodd },
    intros k hkprime hkdvdleft hkdvdright,
    apply hkprime.not_unit,

    have hkdvdright' : k ∣ v,
    { rw even_iff_two_dvd at hsubodd,
      exact int.dvd_mul_cancel_prime' hsubodd hkdvdleft int.prime_two hkdvdright },

    apply huvcoprime.is_unit_of_dvd' _ hkdvdright',
    rw [←sub_add_cancel u v],
    exact dvd_add hkdvdleft hkdvdright' },
  have haddsubcoprime : is_coprime (u + v) (u - v),
  { apply is_coprime_of_prime_dvd,
    { rintro ⟨h1, -⟩,
      norm_num [h1] at haddodd },
    intros k hkprime hkdvdleft hkdvdright,
    apply hkprime.not_unit,
    rw even_iff_two_dvd at haddodd,
    apply huvcoprime.is_unit_of_dvd';
      apply int.dvd_mul_cancel_prime' haddodd hkdvdleft int.prime_two,

    { convert dvd_add hkdvdleft hkdvdright,
      ring },
    { convert dvd_sub hkdvdleft hkdvdright,
      ring } },
  exact ⟨haddcoprime.symm, hsubcoprime.symm, haddsubcoprime.symm⟩,
end

lemma descent_gcd3_coprime {q s : ℤ}
  (h3_ndvd_q : ¬3 ∣ q)
  (hspos : s ≠ 0)
  (hcoprime' : is_coprime s q)
  (hodd' : even q ↔ ¬even s) :
  is_coprime (3 ^ 2 * 2 * s) (q ^ 2 + 3 * s ^ 2) :=
begin
  have h2ndvd : ¬(2 ∣ (q ^ 2 + 3 * s ^ 2)),
  { rw ←even_iff_two_dvd,
    simp [two_ne_zero, hodd'] with parity_simps },

  have h3ndvd : ¬(3 ∣ (q ^ 2 + 3 * s ^ 2)),
  { intro H,
    apply h3_ndvd_q,
    rw ←dvd_add_iff_left (dvd_mul_right _ _) at H,
    exact prime.dvd_of_dvd_pow int.prime_three H },

  apply is_coprime_of_prime_dvd,
  { rintro ⟨h1, -⟩,
    rw mul_eq_zero at h1,
    exact hspos (h1.resolve_left (by norm_num)) },
  intros k hkprime hkdvdleft hkdvdright,
  apply hkprime.not_unit,
  have : k ∣ s,
  { apply int.dvd_mul_cancel_prime' h2ndvd hkdvdright int.prime_two,
    apply int.dvd_mul_cancel_prime' h3ndvd hkdvdright int.prime_three,
    apply int.dvd_mul_cancel_prime' h3ndvd hkdvdright int.prime_three,
    convert hkdvdleft using 1,
    ring },
  apply hcoprime'.is_unit_of_dvd' this,
  apply hkprime.dvd_of_dvd_pow,
  rw dvd_add_iff_left ((this.pow two_ne_zero).mul_left _),
  exact hkdvdright
end

lemma descent_gcd3 (a b c p q : ℤ)
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hcoprime : is_coprime p q)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime 3 a b c)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
  ∃ (a' b' c' : ℤ),
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 1.
  have h3_dvd_p : 3 ∣ p,
  { apply int.dvd_mul_cancel_prime' _ dvd_rfl int.prime_two,
    { zify at hgcd,
      rw ← hgcd,
      exact int.gcd_dvd_left _ _},
    { norm_num } },
  have h3_ndvd_q : ¬(3 ∣ q),
  { intro H,
    have := hcoprime.is_unit_of_dvd' h3_dvd_p H,
    rw int.is_unit_iff_nat_abs_eq at this,
    norm_num at this },
  -- 2.
  obtain ⟨s, rfl⟩ := h3_dvd_p,
  have hspos : s ≠ 0 := right_ne_zero_of_mul hp,
  have hps : 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) = 3 ^ 2 * 2 * s * (q ^ 2 + 3 * s ^ 2),
  { ring },
  -- 3.
  have hcoprime' : is_coprime s q,
  { apply is_coprime_of_prime_dvd,
    { rintro ⟨h1, -⟩,
      exact hspos h1 },
    intros k hkprime hkdvdleft hkdvdright,
    apply hkprime.not_unit,
    apply hcoprime.is_unit_of_dvd' _ hkdvdright,
    exact hkdvdleft.mul_left 3 },

  have hodd' : even q ↔ ¬even s,
  { rw [iff.comm, not_iff_comm, iff.comm],
  simpa with parity_simps using hodd },
  have hcoprime'' : is_coprime (3^2 * 2 * s) (q ^ 2 + 3 * s ^ 2),
  { exact descent_gcd3_coprime h3_ndvd_q hspos hcoprime' hodd' },
  -- 4.
  obtain ⟨r, hr⟩ : ∃ r, 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  rw hps at hr,
  obtain ⟨hcubeleft, hcuberight⟩ := int.eq_pow_of_mul_eq_pow_bit1 hcoprime'' hr,

  -- 5.
  -- todo shadows hq hq
  obtain ⟨u, v, hq, hs, huvcoprime, huvodd⟩ := obscure' q s hq hcoprime'.symm hodd' hcuberight,
  have hu : u ≠ 0,
  { rintro rfl,
    norm_num at hq },
  have hv : v ≠ 0,
  { rintro rfl,
    norm_num at hs },

  -- 6.
  obtain ⟨haddcoprime, hsubcoprime, haddsubcoprime⟩ := gcd3_coprime huvcoprime huvodd,

  -- 7.
  obtain ⟨e, he⟩ := hcubeleft,
  obtain ⟨t, rfl⟩ : 3 ∣ e,
  { rw [←int.pow_dvd_pow_iff (by norm_num : 0 < 3), ←he, hs],
    convert dvd_mul_right _ (2 * v * (u - v) * (u + v)) using 1,
    norm_num,
    ring },
  have ht : 2 * v * (u - v) * (u + v) = t ^ 3,
  { have : (3 ^ 3 : ℤ) ≠ 0,
    { norm_num },
    rw [←mul_right_inj' this, ←mul_pow, ←he, hs],
    ring },

  obtain ⟨A, B, C, HApos, HBpos, HCpos, HA, HB, HC⟩ : ∃ X Y Z : ℤ,
    X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    2 * v = X ^ 3 ∧ u - v = Y ^ 3 ∧ u + v = Z ^ 3,
  { apply int.cube_of_coprime,
    { exact mul_ne_zero two_ne_zero hv, },
    { intro H, rw sub_eq_zero at H, simpa [H] with parity_simps using huvodd, },
    { intro H, rw add_eq_zero_iff_eq_neg at H, simpa [H] with parity_simps using huvodd },
    { exact hsubcoprime },
    { exact haddcoprime },
    { exact haddsubcoprime },
    { exact ht } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,
  -- 9.
  { rw [←mul_assoc, mul_comm, ←mul_assoc (C ^ 3), ←HA, ←HB, ←HC],
    set x := v * (u - v) * (u + v) with hx,
    calc ((u + v) * (2 * v) * (u - v)).nat_abs
        = (2 * x).nat_abs : by { rw hx, congr' 1, ring }
    ... = 2 * x.nat_abs : by { rw [int.nat_abs_mul 2], refl }
    ... ≤ 3 * x.nat_abs : nat.mul_le_mul_right _ (by norm_num)
    ... = (3 * x).nat_abs : by { rw [int.nat_abs_mul 3], refl }
    ... = s.nat_abs : by { rw [hx, hs], congr' 1, ring }
    ... ≤ (2 * 3) * s.nat_abs : nat.le_mul_of_pos_left (by norm_num)
    ... = (2 * 3 * s).nat_abs : by { rw [int.nat_abs_mul (2 * 3)], refl } },
  { rw [←HA, ←HB, ←HC], ring },
end

lemma descent
  (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ a' b' c' : ℤ,
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' * b' * c').nat_abs < (a * b * c).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,

  suffices : ∃ a' b' c' : ℤ,
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3,
  { obtain ⟨a', b', c', ha', hb', hc', hsmaller, hsolution⟩ := this,
    refine ⟨a', b', c', ha', hb', hc', _, hsolution⟩,
    rw ←nat.pow_lt_iff_lt_left (by norm_num : 1 ≤ 3),
    convert lt_of_le_of_lt hsmaller haaa;
      simp [mul_pow, int.nat_abs_mul, int.nat_abs_pow] },

  -- 4.
  cases gcd1or3 p q hp hcoprime hodd with hgcd hgcd,
  -- 5.
  { rw int.gcd_eq_one_iff_coprime at hgcd,
    apply descent_gcd1 a b c p q hp hcoprime hodd hcube h hgcd },
  { apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube h hgcd },
end

lemma flt_three
  {a b c : ℤ}
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  induction h : (a * b * c).nat_abs using nat.strong_induction_on with k' IH generalizing a b c,
  intro H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ :=
    exists_coprime zero_lt_three ha hb hc H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH (x' * y' * z').nat_abs _ hx'pos hy'pos hz'pos rfl hsolution,
  apply lt_of_lt_of_le hsmaller,
  rw ←h,
  simp only [int.nat_abs_mul],
  exact nat.mul_le_mul (nat.mul_le_mul hxle hyle) hzle,
end
