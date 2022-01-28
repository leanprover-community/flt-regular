import ring_theory.adjoin.power_basis
import algebra.char_p.algebra
import ring_theory.polynomial.cyclotomic.eval
import ring_theory.discriminant

import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.rat

universes u

open algebra finset nat polynomial cyclotomic_ring is_cyclotomic_extension

open_locale big_operators

namespace is_cyclotomic_extension.rat.singleton

local attribute [instance] is_cyclotomic_extension.finite_dimensional

section generalize

variables (K L : Type*) [linear_ordered_field K] [field L] {p : ℕ+} [ne_zero ((p : ℕ) : L)]
          [algebra K L] [is_cyclotomic_extension {p} K L]

lemma norm_zeta (hodd : odd (p : ℕ)) : norm K (zeta p K L) = 1 :=
begin
  have hz := congr_arg (norm K) ((is_primitive_root.iff_def _ p).1 (zeta_primitive_root p K L)).1,
  rw [← ring_hom.map_one (algebra_map K L), norm_algebra_map, one_pow, monoid_hom.map_pow,
    ← one_pow ↑p] at hz,
  exact strict_mono.injective hodd.strict_mono_pow hz
end

end generalize

variables (K : Type u) [field K] [char_zero K] {p : ℕ+} [is_cyclotomic_extension {p} ℚ K]

lemma norm_zeta_sub_one' (h : 2 < (p : ℕ)) :
  norm ℚ ((zeta p ℚ K) - 1) = ↑(eval 1 (cyclotomic p ℤ)) :=
begin
  let E := algebraic_closure K,
  letI := char_zero_of_injective_algebra_map (algebra_map ℚ E).injective,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos p E p.pos).ne.symm,
  letI : fintype (K →ₐ[ℚ] E) := field.alg_hom.fintype _ _,

  apply (algebra_map ℚ E).injective,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, finrank p,
    neg_one_pow_of_even (nat.totient_even h), one_mul],
  have : univ.prod (λ (σ : K →ₐ[ℚ] E), 1 - σ (zeta p ℚ K)) = eval 1 (cyclotomic' p E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    refine fintype.prod_equiv (zeta.embeddings_equiv_primitive_roots p ℚ K E _) _ _ (λ σ, _),
    { rw [← map_cyclotomic_int],
      refine (is_primitive.irreducible_iff_irreducible_map_fraction_map
        (cyclotomic.monic p ℤ).is_primitive).1 (cyclotomic.irreducible p.pos) },
    { simp } },
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots (is_root_cyclotomic_iff.1 hz),
      ← map_cyclotomic_int, (algebra_map ℚ E).map_int_cast, ←int.cast_one, eval_int_cast_map],
  refl
end

lemma norm_zeta_sub_one [hp : fact (p : ℕ).prime] (h : p ≠ 2) :
  norm ℚ ((zeta p ℚ K) - 1) = p :=
have hp : 2 < (p : ℕ) := lt_of_le_of_ne hp.1.two_le $ by contrapose! h; exact pnat.coe_injective h.symm,
(norm_zeta_sub_one' K hp).trans $ by simp [eval_one_cyclotomic_prime]

lemma discriminant_prime [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) :
  discr ℚ (zeta.power_basis p ℚ K).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  have hprim := zeta_primitive_root p ℚ K,
  have hzero : zeta p ℚ K - 1 ≠ 0 := λ h, by simpa [eval_one_cyclotomic_prime, sub_eq_zero.1 h]
    using is_root.def.1 (is_root_cyclotomic p.pos hprim),
  have hodd' : (p : ℕ) ≠ 2 := λ hn, by exact hodd.symm (pnat.coe_inj.1 hn.symm),
  have hpos := pos_iff_ne_zero.2 (λ h, (tsub_pos_of_lt (prime.one_lt hp.out)).ne.symm h),
  have heven := even_sub_one_of_prime_ne_two hp.out hodd',

  rw [algebra.of_power_basis_eq_norm, zeta.power_basis_gen, finrank p,
    minpoly.gcd_domain_eq_field_fractions ℚ (is_primitive_root.is_integral hprim p.pos),
    ← cyclotomic_eq_minpoly hprim p.pos, map_cyclotomic, totient_prime hp.out],
  have H := congr_arg derivative (cyclotomic_prime_mul_X_sub_one ℚ p),
  rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_one,
    derivative_sub, derivative_one, sub_zero, derivative_X_pow] at H,
  replace H := congr_arg (λ P, aeval (zeta p ℚ K) P) H,
  simp only [aeval_X_pow, add_zero, aeval_nat_cast, aeval_X, zeta_spec, aeval_one,
    alg_hom.map_sub, aeval_add, alg_hom.map_mul] at H,
  replace H := congr_arg (algebra.norm ℚ) H,
  rw [monoid_hom.map_mul, norm_zeta_sub_one _ hodd, monoid_hom.map_mul, monoid_hom.map_pow,
    norm_zeta ℚ K (odd_iff.2 (or_iff_not_imp_left.1 (nat.prime.eq_two_or_odd hp.out) hodd')),
    one_pow, mul_one, ← map_nat_cast (algebra_map ℚ K), norm_algebra_map,
    finrank p, totient_prime hp.out, ← succ_pred_eq_of_pos hpos, pow_succ,
    mul_comm _ (p : ℚ), coe_coe] at H,
  rw [(mul_right_inj' (cast_ne_zero.2 hp.out.ne_zero : (p : ℚ) ≠ 0)).1 H],
  congr' 1,
  rw [← mul_one 2, ← nat.div_mul_div (even_iff_two_dvd.1 heven) (one_dvd _),
    nat.div_one, mul_one, mul_comm, pow_mul],
  congr' 1,
  exact neg_one_pow_of_odd (even.sub_odd (one_le_iff_ne_zero.2 hpos.ne.symm) heven (odd_iff.2 rfl)),
end


end is_cyclotomic_extension.rat.singleton
