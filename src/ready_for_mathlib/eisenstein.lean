import ring_theory.polynomial.eisenstein

variables (p : ℕ)

local notation `𝓟` := submodule.span ℤ {p}

open_locale big_operators polynomial

open polynomial ideal algebra finset

lemma cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at [hp : fact p.prime] (n : ℕ) :
  ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).is_eisenstein_at 𝓟 :=
{ leading :=
  begin
    intro h,
    rw [show (X + 1 : ℤ[X]) = X + C 1, by simp] at h,
    suffices : ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + C 1)).monic,
    { rw [monic.def.1 this, ideal.submodule_span_eq, ideal.mem_span_singleton] at h,
      exact nat.prime.not_dvd_one hp.out (by exact_mod_cast h) },
    refine monic.comp (cyclotomic.monic _ ℤ) (monic_X_add_C 1) (λ h₁, _),
    rw [nat_degree_X_add_C] at h₁,
    exact zero_ne_one h₁.symm
  end,
  mem :=
  begin
    induction n with n hn,
    { intros i hi,
      rw [zero_add, pow_one] at hi ⊢,
      exact cyclotomic_comp_X_add_one_is_eisenstein_at.mem hi },
    { intros i hi,
      rw [ideal.submodule_span_eq, ideal.mem_span_singleton, ← zmod.int_coe_zmod_eq_zero_iff_dvd,
        ← int.coe_cast_ring_hom, ← coeff_map, map_comp, map_cyclotomic, polynomial.map_add, map_X,
        polynomial.map_one, pow_add, pow_one, cyclotomic_mul_prime_dvd_eq_pow, pow_comp,
        ← zmod.expand_card, coeff_expand hp.out.pos],
      { simp only [ite_eq_right_iff],
        rintro ⟨k, hk⟩,
        rw [nat_degree_comp, show (X + 1 : ℤ[X]) = X + C 1, by simp, nat_degree_X_add_C,
          mul_one, nat_degree_cyclotomic, nat.totient_prime_pow hp.out (nat.succ_pos _),
          nat.succ_sub_one] at hn hi,
        rw [hk, pow_succ, mul_assoc] at hi,
        rw [hk, mul_comm, nat.mul_div_cancel _ hp.out.pos],
        replace hn := hn (lt_of_mul_lt_mul_left' hi),
        rw [ideal.submodule_span_eq, ideal.mem_span_singleton,
          ← zmod.int_coe_zmod_eq_zero_iff_dvd, ← int.coe_cast_ring_hom, ← coeff_map] at hn,
        simpa [map_comp] using hn },
      { exact ⟨p ^ n, by rw [pow_succ]⟩ } },
  end,
  not_mem :=
  begin
    rw [coeff_zero_eq_eval_zero, eval_comp, cyclotomic_prime_pow_eq_geom_sum hp.out, eval_add,
      eval_X, eval_one, zero_add, geom_sum_def, eval_finset_sum],
      simp only [eval_pow, eval_X, one_pow, sum_const, card_range, nat.smul_one_eq_coe,
        int.nat_cast_eq_coe_nat, submodule_span_eq, ideal.submodule_span_eq,
        ideal.span_singleton_pow, ideal.mem_span_singleton],
    intro h,
    obtain ⟨k, hk⟩ := int.coe_nat_dvd.1 h,
    rw [← mul_assoc, mul_one, mul_assoc] at hk,
    nth_rewrite 0 [← nat.mul_one p] at hk,
    rw [nat.mul_right_inj hp.out.pos] at hk,
    exact nat.prime.not_dvd_one hp.out (dvd.intro k (hk.symm))
  end }
