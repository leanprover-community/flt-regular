import ring_theory.discriminant
import number_theory.cyclotomic.primitive_roots

universes u v
variables {p : ℕ+} (k : ℕ) {K : Type u} {L : Type v} {ζ : L} [field K] [field L]
variables [algebra K L] [ne_zero ((p : ℕ) : K)]

open algebra polynomial nat is_primitive_root

namespace is_cyclotomic_extension

local attribute [instance] is_cyclotomic_extension.finite_dimensional
local attribute [instance] is_cyclotomic_extension.is_galois


lemma discr_odd_prime_pow [is_cyclotomic_extension {p ^ (k + 1)} K L] [hp : fact (p : ℕ).prime]
  (hζ : is_primitive_root ζ ↑(p ^ (k + 1))) (hirr : irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K))
  (hirr₁ : irreducible (cyclotomic (p : ℕ) K))
  (hodd : p ≠ 2) : discr K (hζ.power_basis K).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) ^ k * ((p - 1) * (k + 1) - 1)) :=
begin
  have hodd' : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  haveI : ne_zero ((↑(p ^ (k + 1)) : ℕ) : K),
  { refine ⟨λ hzero, _⟩,
    rw [pnat.pow_coe] at hzero,
    simpa [ne_zero.ne ((p : ℕ) : K)] using hzero },

  rw [discr_power_basis_eq_norm, finrank _ hirr, hζ.power_basis_gen _,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, pnat.pow_coe, totient_prime_pow hp.out
    (succ_pos k)],
  congr' 1,
  { have h := even_sub_one_of_prime_ne_two hp.out hodd',
    rw [← mul_one 2, ← mul_comm ((p : ℕ) - 1), mul_assoc ((p : ℕ) - 1), ← nat.div_mul_div_comm
      (even_iff_two_dvd.1 h) (one_dvd _), nat.div_one, mul_one, pow_mul, nat.sub_one (k + 1),
      nat.pred_succ],
    cases neg_one_pow_eq_or K (((p : ℕ) - 1) / 2) with hpos hneg,
    { rw [hpos, one_pow] },
    { rw [hneg],
      refine (nat.odd_mul.2 ⟨(decidable.or_iff_not_imp_left.1 (hp.out.eq_two_or_odd') hodd').pow,
        nat.even.sub_odd _ (even_mul.2 _) odd_one⟩).neg_one_pow,
      { refine one_le_iff_ne_zero.2 (nat.mul_ne_zero (λ h, _) _),
        { exact (not_lt_of_le (tsub_eq_zero_iff_le.1 h)) (prime.one_lt hp.out) },
        { refine pow_ne_zero _ (hp.out.ne_zero) } },
      { left,
        exact nat.even_sub_one_of_prime_ne_two hp.out hodd' } } },
      { have H := congr_arg derivative (cyclotomic_prime_pow_mul_X_pow_sub_one K p k),
        rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_pow,
          derivative_X, mul_one, derivative_sub, derivative_one, sub_zero, derivative_pow,
          derivative_X, mul_one, ← pnat.pow_coe, hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H,
        replace H := congr_arg (λ P, aeval ζ P) H,
        simp only [aeval_add, aeval_mul, minpoly.aeval, zero_mul, add_zero, aeval_nat_cast,
          _root_.map_sub, aeval_one, aeval_X_pow] at H,
        replace H := congr_arg (algebra.norm K) H,
        rw [monoid_hom.map_mul, hζ.pow_sub_one_norm_prime_ne_two hirr
          (by simpa [tsub_self, pow_one] using hirr₁) rfl.le hodd, monoid_hom.map_mul,
          ← map_nat_cast (algebra_map K L), norm_algebra_map, finrank _ hirr, pnat.pow_coe,
          totient_prime_pow hp.out (succ_pos k), nat.sub_one, nat.pred_succ,
          ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow, hζ.norm_eq_one _ hirr, one_pow,
          mul_one, cast_pow, ← coe_coe, ← pow_mul, ← mul_assoc, mul_comm (k + 1), mul_assoc] at H,
        { have := mul_pos (succ_pos k) (tsub_pos_iff_lt.2 hp.out.one_lt),
          rw [← succ_pred_eq_of_pos this, mul_succ, pow_add _ _ ((p : ℕ) ^ k)] at H,
          replace H := (mul_left_inj' (λ h, _)).1 H,
          { simpa only [← pnat.pow_coe, H, mul_comm _ (k + 1)] },
          { replace h := pow_eq_zero h,
            rw [coe_coe] at h,
            exact ne_zero.ne _ h } },
        { intro h,
          rw [← pnat.coe_inj, pnat.coe_bit0, pnat.one_coe, pnat.pow_coe, ← pow_one 2] at h,
          replace h := eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 nat.prime_two)
            (k.succ_pos) h,
          exact hodd' h },
        apply_instance },
      { apply_instance }
end

end is_cyclotomic_extension
