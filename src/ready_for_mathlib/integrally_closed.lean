import ring_theory.integrally_closed
import ring_theory.power_basis
import ring_theory.norm

import ready_for_mathlib.integral_closure
import ready_for_mathlib.degree
import ready_for_mathlib.nat
import ready_for_mathlib.prime

universes u v z w

open_locale big_operators

open polynomial algebra finset is_integrally_closed power_basis is_scalar_tower

variables {R : Type u} {S : Type w} (K : Type v) (L : Type z)
variables [comm_ring R] [comm_ring S] [algebra R S] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L]

lemma eisenstein {S : Type*} [comm_ring S] {x : S} {P : polynomial S} (hP : eval x P = 0) {p : S}
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

lemma eisenstein_aeval_coeff_deg {x : S} {p : R} {P : polynomial R}
  (hx : aeval x P = 0) (hmo : P.monic) (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n ) :
  ∃ y, (algebra_map R S) p * y = x ^ (P.map (algebra_map R S)).nat_degree ∧
  y ∈ adjoin R ({x} : set S) :=
begin
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

lemma eisenstein_aeval {x : S} {p : R} {P : polynomial R}
  (hx : aeval x P = 0) (hmo : P.monic) (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n ) :
  ∀ i, (P.map (algebra_map R S)).nat_degree ≤ i → ∃ y, (algebra_map R S) p * y = x ^ i ∧
  y ∈ adjoin R ({x} : set S) :=
begin
  intros i hi,
  obtain ⟨k, hk⟩ := le_iff_exists_add.1 hi,
  rw [hk, pow_add],
  obtain ⟨y, hy⟩ := eisenstein_aeval_coeff_deg hx hmo hdiv,
  exact ⟨y * x ^ k, by rw [← mul_assoc _ y, hy.1], subalgebra.mul_mem _ hy.2 (subalgebra.pow_mem _
    (subset_adjoin (set.mem_singleton x)) _) ⟩
end

lemma eiseinstein_integral_first [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K]
  [is_integrally_closed R] [is_separable K L] {B : power_basis K L} {p : R} (hp : prime p)
  (hdiv : ∀ n < (minpoly R B.gen).nat_degree, p ∣ (minpoly R B.gen).coeff n )
  (hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0) (hBint : is_integral R B.gen)
  {z : L} {Q : polynomial R} (hQ : (aeval B.gen) Q = p • z) (hzint : is_integral R z) :
  p ∣ Q.coeff 0 :=
begin
  letI := finite_dimensional B,
  let P := minpoly R B.gen,
  let P₁ := P.map (algebra_map R L),
  choose! f hf using eisenstein_aeval (minpoly.aeval R B.gen) (minpoly.monic hBint) hdiv,

  have aux : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0, P₁.nat_degree ≤ i + (P₁.nat_degree - 1),
  { intros i hi,
    rw [nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R L)],
    simp only [mem_range, mem_erase] at hi,
    exact nat.le_of_pos_add_prec _ hi.1 },
  have : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0,
    Q.coeff i • B.gen ^ i * B.gen ^ (P.nat_degree - 1) =
    Q.coeff i • (algebra_map R L) p * f (i + (P.nat_degree - 1)),
  { intros i hi,
    rw [← nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R L), smul_mul_assoc,
      ← pow_add, smul_mul_assoc, (hf _ (aux i hi)).1] },
  have hintsum : is_integral R (z * B.gen ^ (P.nat_degree - 1) -
    ∑ (x : ℕ) in (range (Q.nat_degree + 1)).erase 0, Q.coeff x • f (x + (P.nat_degree - 1))),
  { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
      (is_integral.sum _ (λ i hi, (is_integral_smul _ _))),
    rw [← nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R L)],
    exact adjoin_le_integral_closure hBint (hf _ (aux i hi)).2 },
  obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),

  rw [aeval_eq_sum_range, ← insert_erase (show 0 ∈ range (Q.nat_degree + 1), by simp),
    sum_insert (not_mem_erase 0 _), pow_zero] at hQ,
  replace hQ := congr_arg (λ x, x * B.gen ^ (P.nat_degree - 1)) hQ,
  simp_rw [smul_mul_assoc, add_mul, smul_mul_assoc, one_mul, sum_mul, sum_congr rfl this,
    smul_mul_assoc, ← smul_def, smul_smul, mul_comm _ p, ← smul_smul] at hQ,
  replace hQ := congr_arg (norm K) (eq_sub_of_add_eq hQ),
  rw [← smul_sum, ← smul_sub, smul_def, algebra_map_apply R K L, _root_.map_mul, map_pow,
    norm_algebra_map, smul_def, _root_.map_mul, algebra_map_apply R K L, norm_algebra_map,
    ← hr, finrank B, power_basis.norm_gen_eq_coeff_zero_minpoly,
    minpoly.gcd_domain_eq_field_fractions K hBint, coeff_map, mul_pow,
    ← map_pow _ _ (P.nat_degree - 1), ← pow_mul, show (-1 : K) = algebra_map R K (-1), by simp,
    ← map_pow _ _ (B.dim * (P.nat_degree - 1)), ← _root_.map_mul, ← map_pow, ← _root_.map_mul,
    ← map_pow, ← _root_.map_mul] at hQ,
  replace hQ := is_fraction_ring.injective R K hQ,

  refine dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd B.dim_pos hp _ hndiv,
  obtain ⟨x, hx⟩ := hdiv 0 (minpoly.nat_degree_pos hBint),
  have hppdiv : p ^ B.dim ∣ p ^ B.dim * r := dvd_mul_of_dvd_left dvd_rfl _,
  rw [← hQ, mul_comm, mul_assoc, ← units.coe_neg_one, ← units.coe_pow,
    is_unit.dvd_mul_left _ _ _ ⟨_, rfl⟩, mul_comm] at hppdiv,
  convert hppdiv,
  rw [← nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R K),
    ← minpoly.gcd_domain_eq_field_fractions K hBint, nat_degree_minpoly],
end

lemma eiseinstein_integral [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K]
  [is_integrally_closed R] [is_separable K L] {B : power_basis K L} {p : R} (hp : prime p)
  (hdiv : ∀ n < (minpoly R B.gen).nat_degree, p ∣ (minpoly R B.gen).coeff n )
  (hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0) (hBint : is_integral R B.gen)
  {z : L} (hzint : is_integral R z) (hz : p • z ∈ adjoin R ({B.gen} : set L)) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  letI := finite_dimensional B,
  set P := minpoly R B.gen with hP,
  let P₁ := P.map (algebra_map R L),

  choose! f hf using eisenstein_aeval (minpoly.aeval R B.gen) (minpoly.monic hBint) hdiv,
  rw [adjoin_singleton_eq_range_aeval] at hz,
  obtain ⟨Q, hQ⟩ := hz,

  suffices : ∀ i ∈ range (Q.nat_degree + 1), p ∣ Q.coeff i,
  { sorry },

  intro i,
  refine nat.case_strong_induction_on i _ (λ j hind, _),
  { intro H,
    exact eiseinstein_integral_first K L hp hdiv hndiv hBint hQ hzint },
  { intro hj,
    refine dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd B.dim_pos hp _ hndiv,

    choose! g hg using hind,
    replace hg : ∀ k ∈ range (j + 1), Q.coeff k • B.gen ^ k =
      (algebra_map R L p) * (g k • B.gen ^ k),
    { intros k hk,
      rw [hg k (mem_range_succ_iff.1 hk) (mem_range_succ_iff.2 (le_trans (mem_range_succ_iff.1 hk)
        (nat.succ_le_iff.1 (mem_range_succ_iff.1 hj)).le)), smul_def, smul_def,  ring_hom.map_mul,
        mul_assoc] },
    have HjP : j + 1 ≤ P.nat_degree := sorry,
    have Hj : Q.nat_degree + 1 = j + 1 + (Q.nat_degree - j) := sorry,
    have hzeroj : 0 ∈ range (Q.nat_degree - j) := sorry,
    have hdisj : disjoint (range (j + 1))
      (finset.map (add_left_embedding (j + 1)) (range (Q.nat_degree - j))) := sorry,
    have : ∀ k ∈ (range (Q.nat_degree - j)).erase 0,
      Q.coeff (j + 1 + k) • B.gen ^ (j + 1 + k) * B.gen ^ (P.nat_degree - (j + 2)) =
      (algebra_map R L) p * Q.coeff (j + 1 + k) • f (k + P.nat_degree - 1) := sorry,
    have hintsum : is_integral R (z * B.gen ^ (P.nat_degree - (j + 2)) -
      (∑ (x : ℕ) in (range (Q.nat_degree - j)).erase 0, Q.coeff (j + 1 + x) •
        f (x + P.nat_degree - 1) +
      ∑ (x : ℕ) in range (j + 1), g x • B.gen ^ x * B.gen ^ (P.nat_degree - (j + 2)))),
    { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
        (is_integral_add (is_integral.sum _ (λ k hk, is_integral_smul _ _))
        (is_integral.sum _ (λ k hk, is_integral_mul (is_integral_smul _ (is_integral.pow hBint _))
        ((is_integral.pow hBint _))))),
      refine adjoin_le_integral_closure hBint (hf _ _).2,
      rw [nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R L)],
      sorry },
    obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),

    rw [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,aeval_eq_sum_range, Hj,
      range_add, sum_union hdisj, sum_congr rfl hg, add_comm] at hQ,
    replace hQ := congr_arg (λ x, x * B.gen ^ (P.nat_degree - (j + 2))) hQ,
    simp_rw [sum_map, add_left_embedding_apply, add_mul, sum_mul, mul_assoc] at hQ,
    rw [← insert_erase hzeroj, sum_insert (not_mem_erase 0 _), add_zero, sum_congr rfl this,
      ← mul_sum, ← mul_sum, add_assoc, ← mul_add, smul_mul_assoc, ← pow_add, smul_def] at hQ,
    replace hQ := congr_arg (norm K) (eq_sub_of_add_eq hQ),
    rw [smul_def, mul_assoc, ← mul_sub, _root_.map_mul, algebra_map_apply R K L, map_pow,
      norm_algebra_map, _root_.map_mul, algebra_map_apply R K L, norm_algebra_map, finrank B, ← hr,
      power_basis.norm_gen_eq_coeff_zero_minpoly, minpoly.gcd_domain_eq_field_fractions K hBint,
      coeff_map, show (-1 : K) = algebra_map R K (-1), by simp, ← map_pow, ← map_pow,
      ← _root_.map_mul, ← map_pow, ← _root_.map_mul, ← map_pow, ← _root_.map_mul] at hQ,
    replace hQ := is_fraction_ring.injective R K hQ,
    have hppdiv : p ^ B.dim ∣ p ^ B.dim * r := dvd_mul_of_dvd_left dvd_rfl _,
    rw [← hQ, mul_comm, ← units.coe_neg_one, mul_pow, ← units.coe_pow, ← units.coe_pow, mul_assoc,
      is_unit.dvd_mul_left _ _ _ ⟨_, rfl⟩, mul_comm, ← hP, ← nat.succ_eq_add_one] at hppdiv,
    convert hppdiv,
    sorry
  }
end
