/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

! This file was ported from Lean 3 source module flt_three.primes
-/
import Mathlib.Data.Int.Parity
import Mathlib.RingTheory.Int.Basic

section

variable {R : Type _} [CommRing R] {x y z : R}

theorem coprime_add_self_pow {n : ℕ} (hn : 0 < n) (hsoln : x ^ n + y ^ n = z ^ n)
    (hxx : IsCoprime x y) : IsCoprime x z := by
  have := IsCoprime.mul_add_left_right (hxx.pow (n := n) (m := n)) 1
  rwa [mul_one, hsoln, IsCoprime.pow_iff hn hn] at this
#align coprime_add_self_pow coprime_add_self_pow

end

-- Edwards p49 introduction
theorem Int.factor_div (a x : ℤ) (hodd : Odd x) :
    ∃ m c : ℤ, c + m * x = a ∧ 2 * c.natAbs < x.natAbs :=
  by
  have h0' : x ≠ 0 := by
    rintro rfl
    simp only at hodd 
  set c := a % x with hc
  by_cases H : 2 * c.natAbs < x.natAbs
  · exact ⟨a / x, c, Int.emod_add_ediv' a x, H⟩
  · push_neg at H 
    refine' ⟨(a + abs x) / x, c - abs x, _, _⟩
    · have := self_dvd_abs x
      rw [Int.add_ediv_of_dvd_right this, add_mul, Int.ediv_mul_cancel this, sub_add_add_cancel, hc,
        Int.emod_add_ediv']
    · rw [← Int.ofNat_lt]
      replace H := Int.ofNat_le_ofNat_of_le H
      have ofNat_two : ((2 : Nat) : Int) = 2 := rfl
      rw [Int.ofNat_mul, ofNat_two] at H ⊢
      have hcnonneg := Int.emod_nonneg a h0'
      have := Int.emod_lt a h0'
      rw [Int.natAbs_of_nonneg hcnonneg] at H 
      rw [← Int.natAbs_neg, neg_sub, Int.natAbs_of_nonneg (sub_nonneg_of_le this.le), mul_sub,
        sub_lt_iff_lt_add, two_mul, Int.abs_eq_natAbs, add_lt_add_iff_left]
      apply lt_of_le_of_ne H
      contrapose! hodd with heqtwomul
      rw [← Int.even_iff_not_odd, ← Int.natAbs_even, ← Int.even_coe_nat, even_iff_two_dvd]
      exact ⟨_, heqtwomul⟩

theorem two_not_cube (r : ℕ) : r ^ 3 ≠ 2 :=by
  have : 1 ≤ 3 := by norm_num
  apply Monotone.ne_of_lt_of_lt_nat (Nat.pow_left_strictMono this).monotone 1 <;> norm_num

nonrec theorem Int.two_not_cube (r : ℤ) : r ^ 3 ≠ 2 :=by
  intro H
  apply two_not_cube r.natAbs
  rw [← Int.natAbs_pow, H]
  norm_num
#align int.two_not_cube Int.two_not_cube  

-- todo square neg_square and neg_pow_bit0
section

variable {R : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [GCDMonoid R]

theorem Irreducible.coprime_of_not_dvd_of_dvd {p k m : R} (hp : Irreducible p) (hdvd1 : ¬p ∣ m)
    (hdvd2 : k ∣ m) : IsCoprime p k :=
  (Irreducible.coprime_iff_not_dvd hp).mpr fun hdvd1' => hdvd1 (hdvd1'.trans hdvd2)

theorem Irreducible.dvd_of_dvd_mul_left {p k m n : R} (hdvd1 : ¬p ∣ m) (hdvd2 : k ∣ m)
    (hp : Irreducible p) (h : k ∣ p * n) : k ∣ n :=
  (hp.coprime_of_not_dvd_of_dvd hdvd1 hdvd2).symm.dvd_of_dvd_mul_left h

end

theorem Int.dvd_mul_cancel_prime' {p k m n : ℤ} (hdvd1 : ¬p ∣ m) (hdvd2 : k ∣ m) (hp : Prime p)
    (h : k ∣ p * n) : k ∣ n :=
  Irreducible.dvd_of_dvd_mul_left hdvd1 hdvd2 hp.irreducible h
#align int.dvd_mul_cancel_prime' Int.dvd_mul_cancel_prime'  

