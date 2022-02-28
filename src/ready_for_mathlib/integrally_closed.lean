import ring_theory.integrally_closed
import ring_theory.power_basis
import ring_theory.norm
import ring_theory.polynomial.eisenstein

import ready_for_mathlib.integral_closure
import ready_for_mathlib.disjoint
import ready_for_mathlib.no_zero_smul_divisors

universes u v z w

open_locale big_operators

open polynomial algebra finset is_integrally_closed power_basis is_scalar_tower nat ideal

variables {R : Type u} {S : Type w} {K : Type v} {L : Type z} {p : R}
variables [comm_ring R] [comm_ring S] [algebra R S] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L]

local notation `𝓟` := submodule.span R {p}

lemma mem_adjoin_of_dvd_aeval_of_dvd_coeff [no_zero_smul_divisors R L] {Q : polynomial R} {x : L}
  {z : L} (hp : p ≠ 0) (hQ : ∀ i ∈ range (Q.nat_degree + 1), p ∣ Q.coeff i)
  (hz : aeval x Q = p • z) : z ∈ adjoin R ({x} : set L) :=
begin
  choose! f hf using hQ,
  rw [aeval_eq_sum_range, sum_range] at hz,
  conv_lhs at hz { congr, skip, funext,
    rw [hf i (mem_range.2 (fin.is_lt i)), ← smul_smul] },
  rw [← smul_sum] at hz,
  replace hz := smul_right_injective _ hp hz,
  rw [← hz],
  refine subalgebra.sum_mem _ (λ i hi, subalgebra.smul_mem _ (subalgebra.pow_mem _
    (subset_adjoin (set.mem_singleton x)) _) _)
end

lemma eiseinstein_integral [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K]
  [is_integrally_closed R] [is_separable K L] {B : power_basis K L} (hp : prime p)
  (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) (hBint : is_integral R B.gen)
  {z : L} (hzint : is_integral R z) (hz : p • z ∈ adjoin R ({B.gen} : set L)) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  have hndiv : ¬ p ^ 2 ∣ ((minpoly R B.gen)).coeff 0 := λ h,
    hei.not_mem ((span_singleton_pow p 2).symm ▸ (ideal.mem_span_singleton.2 h)),
  letI := finite_dimensional B,
  set P := minpoly R B.gen with hP,
  obtain ⟨n , hn⟩ := nat.exists_eq_succ_of_ne_zero B.dim_pos.ne',
  haveI : no_zero_smul_divisors R L := no_zero_smul_divisors.trans R K L,
  let P₁ := P.map (algebra_map R L),

  choose! f hf using (is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le
    (minpoly.aeval R B.gen) (minpoly.monic hBint) hei.is_weakly_eisenstein_at),
  rw [adjoin_singleton_eq_range_aeval] at hz,
  obtain ⟨Q₁, hQ⟩ := hz,
  set Q := Q₁ %ₘ P with hQ₁,
  replace hQ : aeval B.gen Q = p • z,
  { rw [← mod_by_monic_add_div Q₁ (minpoly.monic hBint)] at hQ,
    simpa using hQ },
  by_cases hQzero : Q = 0,
  { simp only [hQzero, smul_def, zero_eq_mul, aeval_zero] at hQ,
    cases hQ with H H₁,
    { have : function.injective (algebra_map R L),
      { rw [algebra_map_eq R K L],
        exact (algebra_map K L).injective.comp (is_fraction_ring.injective R K) },      exfalso,
      exact hp.ne_zero ((ring_hom.injective_iff _).1 this _ H) },
    { rw [H₁],
      exact subalgebra.zero_mem _ } },

  refine mem_adjoin_of_dvd_aeval_of_dvd_coeff hp.ne_zero (λ i, _) hQ,
  refine nat.case_strong_induction_on i _ (λ j hind, _),
  { intro H,
    exact dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at hp hei hBint hQ hzint },
  { intro hj,
    refine hp.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd _ hndiv,
    exact n,

    choose! g hg using hind,
    replace hg : ∀ k ∈ range (j + 1), Q.coeff k • B.gen ^ k =
      (algebra_map R L p) * (g k • B.gen ^ k),
    { intros k hk,
      rw [hg k (mem_range_succ_iff.1 hk) (mem_range_succ_iff.2 (le_trans (mem_range_succ_iff.1 hk)
        (succ_le_iff.1 (mem_range_succ_iff.1 hj)).le)), smul_def, smul_def,  ring_hom.map_mul,
        mul_assoc] },
    have Hj : Q.nat_degree + 1 = j + 1 + (Q.nat_degree - j),
    { rw [← add_comm 1, ← add_comm 1, add_assoc, add_right_inj, ← nat.add_sub_assoc
        (lt_of_succ_lt_succ (mem_range.1 hj)).le, add_comm, nat.add_sub_cancel] },
    have H := degree_mod_by_monic_lt Q₁ (minpoly.monic hBint),
    rw [← hQ₁, ← hP] at H,
    replace H:= nat.lt_iff_add_one_le.1 (lt_of_lt_of_le (lt_of_le_of_lt
      (nat.lt_iff_add_one_le.1 (lt_of_succ_lt_succ (mem_range.1 hj))) (lt_succ_self _))
      (nat.lt_iff_add_one_le.1 (((nat_degree_lt_nat_degree_iff hQzero).2 H)))),
    rw [add_assoc] at H,
    have : ∀ k ∈ (range (Q.nat_degree - j)).erase 0,
      Q.coeff (j + 1 + k) • B.gen ^ (j + 1 + k) * B.gen ^ (P.nat_degree - (j + 2)) =
      (algebra_map R L) p * Q.coeff (j + 1 + k) • f (k + P.nat_degree - 1),
    { intros k hk,
      rw [smul_mul_assoc, ← pow_add, ← nat.add_sub_assoc H, ← add_assoc j 1 1,
        add_comm (j + 1) 1, add_assoc (j + 1), add_comm _ (k + P.nat_degree),
        nat.add_sub_add_right, ← (hf (k + P.nat_degree - 1) _).2, mul_smul_comm],
      rw [nat_degree_map_of_monic (minpoly.monic hBint), add_comm, nat.add_sub_assoc,
        le_add_iff_nonneg_right],
      { exact nat.zero_le _ },
      { refine one_le_iff_ne_zero.2 (λ h, _),
        rw [h] at hk,
        simpa using hk },
      { apply_instance } },
    have hintsum : is_integral R (z * B.gen ^ (P.nat_degree - (j + 2)) -
      (∑ (x : ℕ) in (range (Q.nat_degree - j)).erase 0, Q.coeff (j + 1 + x) •
        f (x + P.nat_degree - 1) +
      ∑ (x : ℕ) in range (j + 1), g x • B.gen ^ x * B.gen ^ (P.nat_degree - (j + 2)))),
    { refine is_integral_sub (is_integral_mul hzint (is_integral.pow hBint _))
        (is_integral_add (is_integral.sum _ (λ k hk, is_integral_smul _ _))
        (is_integral.sum _ (λ k hk, is_integral_mul (is_integral_smul _ (is_integral.pow hBint _))
        ((is_integral.pow hBint _))))),
      refine adjoin_le_integral_closure hBint (hf _ _).1,
      rw [nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R L)],
      rw [add_comm, nat.add_sub_assoc, le_add_iff_nonneg_right],
      { exact zero_le _ },
      { refine one_le_iff_ne_zero.2 (λ h, _),
        rw [h] at hk,
        simpa using hk } },
    obtain ⟨r, hr⟩ := is_integral_iff.1 (is_integral_norm K hintsum),

    rw [aeval_eq_sum_range, Hj, range_add, sum_union (range_disjoint_add_left_embedding _ _),
      sum_congr rfl hg, add_comm] at hQ,
    replace hQ := congr_arg (λ x, x * B.gen ^ (P.nat_degree - (j + 2))) hQ,
    simp_rw [sum_map, add_left_embedding_apply, add_mul, sum_mul, mul_assoc] at hQ,
    rw [← insert_erase (mem_range.2 (tsub_pos_iff_lt.2 $ lt_of_succ_lt_succ $ mem_range.1 hj)),
      sum_insert (not_mem_erase 0 _), add_zero, sum_congr rfl this, ← mul_sum, ← mul_sum,
      add_assoc, ← mul_add, smul_mul_assoc, ← pow_add, smul_def] at hQ,
    replace hQ := congr_arg (norm K) (eq_sub_of_add_eq hQ),
    rw [smul_def, mul_assoc, ← mul_sub, _root_.map_mul, algebra_map_apply R K L, map_pow,
      norm_algebra_map, _root_.map_mul, algebra_map_apply R K L, norm_algebra_map, finrank B, ← hr,
      power_basis.norm_gen_eq_coeff_zero_minpoly, minpoly.gcd_domain_eq_field_fractions K hBint,
      coeff_map, show (-1 : K) = algebra_map R K (-1), by simp, ← map_pow, ← map_pow,
      ← _root_.map_mul, ← map_pow, ← _root_.map_mul, ← map_pow, ← _root_.map_mul] at hQ,
    replace hQ := is_fraction_ring.injective R K hQ,
    have hppdiv : p ^ B.dim ∣ p ^ B.dim * r := dvd_mul_of_dvd_left dvd_rfl _,
    rw [← hQ, mul_comm, ← units.coe_neg_one, mul_pow, ← units.coe_pow, ← units.coe_pow, mul_assoc,
      is_unit.dvd_mul_left _ _ _ ⟨_, rfl⟩, mul_comm, ← nat.succ_eq_add_one, hn] at hppdiv,
    convert hppdiv,
    rw [nat.succ_eq_add_one, add_assoc, ← nat.add_sub_assoc H, ← add_assoc, add_comm (j + 1),
      nat.add_sub_add_left, ← nat.add_sub_assoc, nat.add_sub_add_left, hP,
      ← nat_degree_map_of_monic (minpoly.monic hBint) (algebra_map R K),
      ← minpoly.gcd_domain_eq_field_fractions K hBint, nat_degree_minpoly, hn, nat.sub_one,
      nat.pred_succ],
    linarith }
end

lemma eiseinstein_integral_gen [is_domain R] [normalized_gcd_monoid R] [is_fraction_ring R K]
  [is_integrally_closed R] [is_separable K L] {B : power_basis K L} (hp : prime p)
  (hei : (minpoly R B.gen).is_eisenstein_at 𝓟) (hBint : is_integral R B.gen) {n : ℕ}
  {z : L} (hzint : is_integral R z) (hz : p ^ n • z ∈ adjoin R ({B.gen} : set L)) :
  z ∈ adjoin R ({B.gen} : set L) :=
begin
  induction n with n hn,
  { simpa using hz },
  { rw [pow_succ, mul_smul] at hz,
    exact hn (eiseinstein_integral hp hei hBint (is_integral_smul _ hzint) hz) }
end
