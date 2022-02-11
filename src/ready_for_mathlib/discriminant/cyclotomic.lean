import ring_theory.adjoin.power_basis
import algebra.char_p.algebra
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.discriminant
import number_theory.cyclotomic.primitive_roots

import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.rat

universes u

open algebra finset nat polynomial cyclotomic_ring is_cyclotomic_extension

open_locale big_operators

namespace is_cyclotomic_extension

local attribute [instance] is_cyclotomic_extension.finite_dimensional

variables (K : Type u) [field K] [char_zero K] {p : ℕ+} [is_cyclotomic_extension {p} ℚ K]

-- this file will be tidied up once #11786 merges

lemma norm_zeta_sub_one [hp : fact (p : ℕ).prime] (h : p ≠ 2) :
  norm ℚ ((zeta p ℚ K) - 1) = p :=
begin
  have := lt_of_le_of_ne hp.1.two_le (by contrapose! h; exact pnat.coe_injective h.symm),
  simp [(zeta_primitive_root p ℚ K).sub_one_norm_eq_eval_cyclotomic this
        (cyclotomic.irreducible_rat hp.out.pos), eval_one_cyclotomic_prime],
end

lemma discriminant_prime [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  discr ℚ (((zeta_primitive_root p ℚ K).power_basis ℚ).basis) =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  have hprim := zeta_primitive_root p ℚ K,
  have hzero : zeta p ℚ K - 1 ≠ 0 := λ h, by simpa [eval_one_cyclotomic_prime, sub_eq_zero.1 h]
    using is_root.def.1 (is_root_cyclotomic p.pos hprim),
  have hodd' : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  have hpos := pos_iff_ne_zero.2 (λ h, (tsub_pos_of_lt (prime.one_lt hp.out)).ne.symm h),
  have heven := even_sub_one_of_prime_ne_two hp.out hodd',

  rw [algebra.of_power_basis_eq_norm, is_primitive_root.power_basis_gen, finrank _
    (cyclotomic.irreducible_rat hp.out.pos), minpoly.gcd_domain_eq_field_fractions ℚ
    (is_primitive_root.is_integral hprim p.pos), ← cyclotomic_eq_minpoly hprim p.pos,
    map_cyclotomic, totient_prime hp.out],
  have H := congr_arg derivative (cyclotomic_prime_mul_X_sub_one ℚ p),
  rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_one,
    derivative_sub, derivative_one, sub_zero, derivative_X_pow] at H,
  replace H := congr_arg (λ P, aeval (zeta p ℚ K) P) H,
  simp only [aeval_X_pow, add_zero, aeval_nat_cast, aeval_X, zeta_spec, aeval_one,
    alg_hom.map_sub, aeval_add, alg_hom.map_mul] at H,
  replace H := congr_arg (algebra.norm ℚ) H,
  rw [monoid_hom.map_mul, norm_zeta_sub_one _ hodd, monoid_hom.map_mul, monoid_hom.map_pow,
    (zeta_primitive_root p ℚ K).norm_eq_one ℚ (odd_iff.2 (or_iff_not_imp_left.1 (nat.prime.eq_two_or_odd hp.out)
    hodd')), one_pow, mul_one, ← map_nat_cast (algebra_map ℚ K), norm_algebra_map,
    finrank _ (cyclotomic.irreducible_rat hp.out.pos), totient_prime hp.out, ← succ_pred_eq_of_pos
    hpos, pow_succ, mul_comm _ (p : ℚ), coe_coe] at H,
  rw [(mul_right_inj' (cast_ne_zero.2 hp.out.ne_zero : (p : ℚ) ≠ 0)).1 H],
  congr' 1,
  rw [← mul_one 2, ← nat.div_mul_div (even_iff_two_dvd.1 heven) (one_dvd _),
    nat.div_one, mul_one, mul_comm, pow_mul],
  congr' 1,
  exact neg_one_pow_of_odd (even.sub_odd (one_le_iff_ne_zero.2 hpos.ne.symm) heven (odd_iff.2 rfl)),
  all_goals { apply_instance },
end


end is_cyclotomic_extension
