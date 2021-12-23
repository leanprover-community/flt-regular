import ready_for_mathlib.multiplicity
import ready_for_mathlib.roots_of_unity
import ready_for_mathlib.totient

import ring_theory.polynomial.cyclotomic.basic

open polynomial

@[simp] lemma cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : nat.prime p) (hdiv : p ∣ n)
  (R : Type*) [comm_ring R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R :=
begin
  by_cases hzero : n = 0,
  { simp [hzero] },
  suffices : expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ,
  { rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int] },
  refine eq_of_monic_of_dvd_of_nat_degree_le (cyclotomic.monic _ _)
    ((cyclotomic.monic n ℤ).expand (zero_lt_iff.2 (nat.prime.ne_zero hp))) _ _,
  { have hpos := nat.mul_pos (zero_lt_iff.mpr hzero) (nat.prime.pos hp),
    have hprim := complex.is_primitive_root_exp _ hpos.ne.symm,
    rw [cyclotomic_eq_minpoly hprim hpos],
    refine @minpoly.gcd_domain_dvd ℤ ℂ ℚ _ _ _ _ _ _ _ _ complex.algebra (algebra_int ℂ) _ _
      (is_primitive_root.is_integral hprim hpos) _ ((cyclotomic.monic n ℤ).expand
      (nat.prime.pos hp)).is_primitive _,
    rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def,
      is_root_cyclotomic_iff],
    { convert is_primitive_root.pow_of_div hprim (nat.prime.ne_zero hp) (dvd_mul_left p n),
      rw [nat.mul_div_cancel _ (nat.prime.pos hp)] },
    { exact_mod_cast hzero } },
  { rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      nat.totient_mul_prime_div hp hdiv, mul_comm] }
end
