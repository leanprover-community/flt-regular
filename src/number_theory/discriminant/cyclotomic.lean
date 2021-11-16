import ring_theory.adjoin.power_basis
import algebra.char_p.algebra

import number_theory.discriminant.basic
import number_theory.cyclotomic.cyclotomic_units
import ready_for_mathlib.nat
import ready_for_mathlib.cyclotomic

universes u

open algebra finset nat polynomial cyclotomic_ring

open_locale big_operators

namespace is_cyclotomic_extension

variables (K : Type u) [field K] [char_zero K] {p : ℕ+} [is_cyclotomic_extension {p} ℚ K]

lemma norm_zeta' (hodd : odd (p : ℕ)) : norm ℚ (zeta' p ℚ K) = 1 :=
begin
  have hz := congr_arg (norm ℚ) ((is_primitive_root.iff_def _ p).1 (zeta'_primitive_root p ℚ K)).1,
  rw [← ring_hom.map_one (algebra_map ℚ K), norm_algebra_map, one_pow, monoid_hom.map_pow,
    ← one_pow ↑p] at hz,
  exact (strict_mono.injective (odd.strict_mono_pow hodd)) hz,
end

lemma norm_zeta'_sub_one [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  norm ℚ ((zeta' p ℚ K) - 1) = p :=
begin
  let E := algebraic_closure ℚ,
  letI := char_zero_of_injective_algebra_map (algebra_map ℚ E).injective,
  have hpE : ((p : ℕ) : E) ≠ 0 := λ h, p.pos.ne (cast_eq_zero.1 h).symm,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos p E p.pos).ne.symm,

  apply (algebra_map ℚ E).injective,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  replace hodd : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, singleton_finrank p,
    totient_prime hp.out, neg_one_pow_of_even (even_of_prime_neq_two_sub_one hp.out hodd), one_mul],
  have : univ.prod (λ (σ : K →ₐ[ℚ] E), 1 - σ (zeta' p ℚ K)) = eval 1 (cyclotomic' p E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    exact fintype.prod_equiv (zeta'.embeddings_equiv_primitive_roots p ℚ K E) _ _ (λ σ, by simp) },
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots
    ((is_root_cyclotomic_iff hpE).2 hz), eval_one_cyclotomic_prime],
  simp,
end

lemma discriminant_prime [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  discriminant ℚ (zeta'.power_basis p ℚ K).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  letI := char_zero_of_injective_algebra_map (algebra_map ℚ K).injective,
  have hprim := zeta'_primitive_root p ℚ K,
  have hzero : zeta' p ℚ K - 1 ≠ 0 := λ h, by simpa [eval_one_cyclotomic_prime, sub_eq_zero.1 h]
    using is_root.def.1 (is_root_cyclotomic p.pos hprim),
  have hodd' : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  have hpos : 0 < (p : ℕ) - 1 := sorry,
  have hzero : (p : ℚ) ≠ 0 := sorry,

  rw [discriminant.of_power_basis_eq_norm, zeta'.power_basis_gen,
    minpoly.gcd_domain_eq_field_fractions ℚ (is_primitive_root.is_integral hprim p.pos),
    ← cyclotomic_eq_minpoly hprim p.pos, map_cyclotomic],
  have H := congr_arg derivative (cyclotomic_prime_mul_X_sub_one ℚ p),
  rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_one,
    derivative_sub, derivative_one, sub_zero, derivative_X_pow] at H,
  replace H := congr_arg (λ P, aeval (zeta' p ℚ K) P) H,
  simp only [aeval_X_pow, add_zero, aeval_nat_cast, aeval_X, zeta'_spec, aeval_one,
    alg_hom.map_sub, aeval_add, alg_hom.map_mul] at H,
  replace H := congr_arg (algebra.norm ℚ) H,
  rw [monoid_hom.map_mul, norm_zeta'_sub_one _ hodd, monoid_hom.map_mul, monoid_hom.map_pow,
    norm_zeta' K (odd_iff.2 (or_iff_not_imp_left.1 (nat.prime.eq_two_or_odd hp.out) hodd')),
    one_pow, mul_one, ← ring_hom.map_nat_cast (algebra_map ℚ K), norm_algebra_map,
    singleton_finrank p, totient_prime hp.out, ← succ_pred_eq_of_pos hpos, pow_succ,
    mul_comm _ (p : ℚ), ← coe_coe] at H,
  rw [(mul_right_inj' hzero).1 H, singleton_finrank p, totient_prime hp.out],
  sorry
end


end is_cyclotomic_extension
