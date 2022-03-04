import ring_theory.polynomial.eisenstein
import ring_theory.polynomial.cyclotomic.basic

import ready_for_mathlib.cyclotomic

variables {p : ℕ} [hp : fact p.prime]

open_locale polynomial

open finset

namespace polynomial

local notation `𝓟` := submodule.span ℤ {p}

include hp

lemma cyclotomic_comp_X_add_one_is_eisenstein_at :
  ((cyclotomic p ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
{ leading :=
  begin
    intro h,
    rw [show (X + 1 : ℤ[X]) = X + C 1, by simp] at h,
    suffices : ((cyclotomic p ℤ).comp (X + C 1)).monic,
    { rw [monic.def.1 this, ideal.submodule_span_eq, ideal.mem_span_singleton] at h,
      exact nat.prime.not_dvd_one hp.out (by exact_mod_cast h) },
    refine monic.comp (cyclotomic.monic p ℤ) (monic_X_add_C 1) (λ h₁, _),
    rw [nat_degree_X_add_C] at h₁,
    exact zero_ne_one h₁.symm,
  end,
  mem := λ i hi,
  begin
    rw [cyclotomic_comp_X_add_one p, ← lcoeff_apply, linear_map.map_sum],
    conv { congr, congr, skip, funext,
      rw [lcoeff_apply, mul_comm, ← C_eq_nat_cast, ← monomial_eq_C_mul_X, coeff_monomial] },
    rw [nat_degree_comp, show (X + 1 : ℤ[X]) = X + C 1, by simp, nat_degree_X_add_C, mul_one,
      nat_degree_cyclotomic, nat.totient_prime hp.out] at hi,
    simp only [lt_of_lt_of_le hi (nat.sub_le _ _), int.nat_cast_eq_coe_nat, sum_ite_eq', mem_range,
      if_true, ideal.submodule_span_eq, ideal.mem_span_singleton],
    exact int.coe_nat_dvd.2
      (nat.prime.dvd_choose_self (nat.succ_pos i) (lt_tsub_iff_right.1 hi) hp.out)
  end,
  not_mem :=
  begin
    rw [coeff_zero_eq_eval_zero, eval_comp, cyclotomic_eq_geom_sum hp.out, eval_add, eval_X,
      eval_one, zero_add, eval_geom_sum, one_geom_sum, int.nat_cast_eq_coe_nat,
      ideal.submodule_span_eq, ideal.span_singleton_pow, ideal.mem_span_singleton],
    intro h,
    obtain ⟨k, hk⟩ := int.coe_nat_dvd.1 h,
    rw [← mul_assoc, mul_one, mul_assoc] at hk,
    nth_rewrite 0 [← nat.mul_one p] at hk,
    rw [nat.mul_right_inj hp.out.pos] at hk,
    exact nat.prime.not_dvd_one hp.out (dvd.intro k (hk.symm)),
  end }

end polynomial
