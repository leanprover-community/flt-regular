/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import ring_theory.coprime.lemmas
import ring_theory.int.basic
import ring_theory.euclidean_domain
import ring_theory.noetherian
import ring_theory.principal_ideal_domain
import ring_theory.prime
import ring_theory.unique_factorization_domain
import tactic

section
variables {R : Type*} [comm_ring R] {x y z : R}
lemma coprime_add_self_pow
  {n : ℕ}
  (hn : 0 < n)
  (hsoln : x ^ n + y ^ n = z ^ n)
  (hxx : is_coprime x y)
   : is_coprime x z :=
begin
  have := is_coprime.mul_add_left_right hxx.pow 1,
  rwa [mul_one, hsoln, is_coprime.pow_iff hn hn] at this,
end
end

-- Edwards p49 introduction
lemma int.factor_div (a x : ℤ) (hodd : odd x) :
  ∃ (m c : ℤ), c + m * x = a ∧ 2 * c.nat_abs < x.nat_abs :=
begin
  have h0' : x ≠ 0,
  { rintro rfl,
    simpa only [even_zero, not_true, int.odd_iff_not_even] using hodd },
  set c := a % x with hc,
  by_cases H : 2 * c.nat_abs < x.nat_abs,
  { exact ⟨a / x, c, int.mod_add_div' a x, H⟩ },
  { push_neg at H,
    refine ⟨(a + abs x) / x, c - abs x, _, _⟩,
    { have := self_dvd_abs x,
      rw [int.add_div_of_dvd_right this, add_mul, int.div_mul_cancel this, sub_add_add_cancel, hc,
        int.mod_add_div'] },
    { zify at ⊢ H,
      have hcnonneg := int.mod_nonneg a h0',
      have := int.mod_lt a h0',
      rw [int.nat_abs_of_nonneg hcnonneg] at H,
      rw [←int.nat_abs_neg, neg_sub, int.nat_abs_of_nonneg (sub_nonneg_of_le this.le),
        mul_sub, sub_lt_iff_lt_add, two_mul, int.abs_eq_nat_abs, add_lt_add_iff_left],
      apply lt_of_le_of_ne H,
      contrapose! hodd with heqtwomul,
      rw [←int.even_iff_not_odd, ←int.nat_abs_even, ←int.even_coe_nat, even_iff_two_dvd],
      exact ⟨_, heqtwomul⟩ } },
end

lemma two_not_cube (r : ℕ) : r ^ 3 ≠ 2 :=
begin
  have : 1 ≤ 3,
  { norm_num },
  apply monotone.ne_of_lt_of_lt_nat (nat.pow_left_strict_mono this).monotone 1; norm_num,
end

lemma int.two_not_cube (r : ℤ) : r ^ 3 ≠ 2 :=
begin
  intro H,
  apply two_not_cube r.nat_abs,
  rw [←int.nat_abs_pow, H],
  norm_num,
end

-- todo square neg_square and neg_pow_bit0

section
variables {R : Type*} [comm_ring R] [is_domain R] [is_principal_ideal_ring R] [gcd_monoid R]

lemma irreducible.coprime_of_not_dvd_of_dvd {p k m : R}
  (hp : irreducible p) (hdvd1 : ¬(p ∣ m)) (hdvd2 : k ∣ m) : is_coprime p k :=
(irreducible.coprime_iff_not_dvd hp).mpr $ λ hdvd1', hdvd1 (hdvd1'.trans hdvd2)

lemma irreducible.dvd_of_dvd_mul_left {p k m n : R}
  (hdvd1 : ¬(p ∣ m))
  (hdvd2 : k ∣ m)
  (hp : irreducible p)
  (h : k ∣ p * n) : k ∣ n :=
(hp.coprime_of_not_dvd_of_dvd hdvd1 hdvd2).symm.dvd_of_dvd_mul_left h

end

lemma int.dvd_mul_cancel_prime' {p k m n : ℤ}
  (hdvd1 : ¬(p ∣ m))
  (hdvd2 : k ∣ m)
  (hp : prime p)
  (h : k ∣ p * n) : k ∣ n :=
irreducible.dvd_of_dvd_mul_left hdvd1 hdvd2 hp.irreducible h
