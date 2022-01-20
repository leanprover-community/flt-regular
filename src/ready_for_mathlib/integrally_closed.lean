import ring_theory.integrally_closed
import ring_theory.power_basis
import ring_theory.norm

import ready_for_mathlib.integral_closure

universes u v z w

open_locale big_operators

open polynomial algebra finset is_integrally_closed

variables {R : Type u} {S : Type w} (K : Type v) (L : Type z)
variables [comm_ring R] [comm_ring S] [algebra R S] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L]

lemma eisenstein {x : S} {P : polynomial S} (hP : eval x P = 0) {p : S}
  (hmo : P.monic) (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n ) :
  ∀ i, P.nat_degree ≤ i → p ∣ x ^ i :=
begin
  intros i hi,
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
  rw [hk, pow_add],
  suffices : p ∣ x ^ P.nat_degree,
  { exact dvd_mul_of_dvd_left this _ },
  rw [eval_eq_finset_sum, range_add_one, sum_insert not_mem_range_self, sum_range,
    hmo.coeff_nat_degree, one_mul] at hP,
  replace hP := eq_neg_of_add_eq_zero hP,
  choose! f hf using hdiv,
  conv_rhs at hP { congr, congr, skip, funext,
    rw [fin.coe_eq_val, hf i.1 i.2, mul_assoc] },
  rw [hP, ← mul_sum, dvd_neg],
  exact dvd_mul_right _ _
end

lemma eisenstein_aeval {x : S} {p : R} {P : polynomial R}
  (hx : aeval x P = 0) (hmo : P.monic) (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n ) :
  ∀ i, P.nat_degree ≤ i → ∃ y, (algebra_map R S) p * y = x ^ i ∧ y ∈ adjoin R ({x} : set S) :=
  begin
  let P₁ := P.map (algebra_map R S),
  intros i hi,
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
  rw [hk, pow_add],
  suffices : ∃ y, (algebra_map R S) p * y = x ^ P₁.nat_degree ∧ y ∈ adjoin R ({x} : set S),
  { obtain ⟨y, hy⟩ := this,
    refine ⟨y * x ^ (k + (P.nat_degree - P₁.nat_degree)), _, _ ⟩,
    { rw [pow_add, mul_comm (x ^ k), ← mul_assoc y, ← mul_assoc _ _ (x ^ k), ← mul_assoc _ y,
        hy.1, ← pow_add, ← nat.add_sub_assoc (nat_degree_map_le _ _), nat.sub_add_comm rfl.le,
        tsub_self, zero_add] },
    { exact subalgebra.mul_mem _ hy.2 (subalgebra.pow_mem _
      (subset_adjoin (set.mem_singleton x)) _) } },
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_finset_sum, range_add_one,
    sum_insert not_mem_range_self, sum_range, (monic_map
    (algebra_map R S) hmo).coeff_nat_degree, one_mul] at hx,
  replace hx := eq_neg_of_add_eq_zero hx,
  choose! f hf using hdiv,
  conv_rhs at hx { congr, congr, skip, funext,
    rw [fin.coe_eq_val, coeff_map, hf i.1 (lt_of_lt_of_le i.2 (nat_degree_map_le _ _)),
      ring_hom.map_mul, mul_assoc] },
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc],
  exact ⟨-1 * ∑ (i : fin (map (algebra_map R S) P).nat_degree), (algebra_map R S)
    (f i.1) * x ^ i.1, rfl, subalgebra.mul_mem _ (subalgebra.neg_mem _ (subalgebra.one_mem _))
    (subalgebra.sum_mem _ (λ i hi, subalgebra.mul_mem _ (subalgebra.algebra_map_mem _ _)
    (subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton x)) _)))⟩,
end

lemma eiseinstein_integral [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K]
  [is_integrally_closed R] [is_separable K L] {B : power_basis K L} {p : R} (hp : prime p)
  (hdiv : ∀ n < (minpoly R B.gen).nat_degree, p ∣ (minpoly R B.gen).coeff n )
  (hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0) (hBint : is_integral R B.gen)
  {z : L} (hzint : is_integral R z) (hz : p • z ∈ adjoin R ({B.gen} : set L)) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  letI := power_basis.finite_dimensional B,
  let P := minpoly R B.gen,
  choose! f hf using eisenstein_aeval (minpoly.aeval R B.gen) (minpoly.monic hBint) hdiv,
  rw [adjoin_singleton_eq_range_aeval] at hz,
  obtain ⟨Q, hQ⟩ := hz,

  have aux : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0, P.nat_degree ≤ i + (P.nat_degree - 1),
  { intros i hi,
    simp only [mem_range, mem_erase] at hi,
    cases P.nat_degree with n,
    { exact zero_le _ },
    { rw [nat.succ_sub_one, nat.succ_eq_add_one, add_comm, add_le_add_iff_right],
        exact nat.one_le_iff_ne_zero.2 hi.1 } },
  have : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0,
    Q.coeff i • B.gen ^ i * B.gen ^ (P.nat_degree - 1) =
    Q.coeff i • (algebra_map R L) p * f (i + (P.nat_degree - 1)),
  { intros i hi,
    rw [smul_mul_assoc, ← pow_add, smul_mul_assoc, (hf _ (aux i hi)).1] },
  have hintsum : is_integral R (z * B.gen ^ (P.nat_degree - 1) -
    ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0, Q.coeff x • f (x + (P.nat_degree - 1))),
  { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
      (is_integral.sum _ (λ i hi, (is_integral_smul _ _))),
    exact adjoin_le_integral_closure hBint (hf _ (aux i hi)).2 },
  obtain ⟨r₁, hr₁⟩ := is_integral_iff.1 (is_integral_norm K hBint),
  obtain ⟨r₂, hr₂⟩ := is_integral_iff.1 (is_integral_norm K hintsum),

  rw [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, aeval_eq_sum_range, ← insert_erase
    (show 0 ∈ range (Q.nat_degree + 1), by simp), sum_insert (not_mem_erase 0 _), pow_zero] at hQ,
  have H := congr_arg (λ x, x * B.gen ^ (P.nat_degree - 1)) hQ,
  simp_rw [smul_mul_assoc, add_mul, smul_mul_assoc, one_mul, sum_mul, sum_congr rfl this,
    smul_mul_assoc, ← smul_def, smul_smul, mul_comm _ p, ← smul_smul] at H,
  replace H := congr_arg (norm K) (eq_sub_of_add_eq H),
  rw [← smul_sum, ← smul_sub, smul_def, is_scalar_tower.algebra_map_apply R K L,
    _root_.map_mul, map_pow, norm_algebra_map, smul_def, _root_.map_mul,
    is_scalar_tower.algebra_map_apply R K L, norm_algebra_map, ← hr₂,
    power_basis.norm_gen_eq_coeff_zero_minpoly, minpoly.gcd_domain_eq_field_fractions K hBint,
    coeff_map, mul_pow, ← map_pow _ _ (P.nat_degree - 1), ← pow_mul,
    show (-1 : K) = algebra_map R K (-1), by simp, ← map_pow _ _ (B.dim * (P.nat_degree - 1)),
    ← _root_.map_mul, ← map_pow, ← _root_.map_mul, ← map_pow, ← _root_.map_mul] at H,
  replace H := is_fraction_ring.injective R K H,

  sorry
end
