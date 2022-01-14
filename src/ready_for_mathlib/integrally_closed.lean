import ring_theory.integral_closure
import ring_theory.power_basis
import ring_theory.norm

universes u v z

open_locale big_operators

open polynomial algebra finset

variables {R : Type u} (K : Type v) (L : Type z)
variables [comm_ring R] [field K] [field L]
variables [algebra K L] [algebra R L] [algebra R K] [is_scalar_tower R K L]

lemma eisenstein {x : R} {P : polynomial R} (hP : eval x P = 0) {p : R} (hmo : P.monic)
  (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n ) : ∀ i, P.nat_degree ≤ i → p ∣ x ^ i :=
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

lemma eiseinstein_integral {B : power_basis K L} {P : polynomial R} (hroot : aeval B.gen P = 0)
  {p : R} (hp : prime p) (hmo : P.monic) (hdiv : ∀ n < P.nat_degree, p ∣ P.coeff n )
  (hndiv : ¬ p ^ 2 ∣ P.coeff 0) {z : L} (hzint : is_integral R z)
  (hz : p • z ∈ adjoin R ({B.gen} : set L)) : z ∈ adjoin R ({B.gen} : set L) :=
begin
  --haveI := nontrivial_iff.2 ⟨(0 : R), 1, λ h, by simpa using congr_arg (algebra_map R L) h⟩,
  let P₁ := P.map (algebra_map R L),
  replace hdiv : ∀ n < P₁.nat_degree, algebra_map R L p ∣ P₁.coeff n,
  { intros i hi,
    obtain ⟨r, hr⟩ := hdiv i (lt_of_lt_of_le hi (nat_degree_map_le _ _)),
    rw [coeff_map, hr, ring_hom.map_mul],
    exact dvd_mul_right _ _ },
  replace hroot : eval B.gen P₁ = 0,
  { rwa [aeval_def, eval₂_eq_eval_map] at hroot },
  choose! f hf using (eisenstein hroot (monic_map (algebra_map R L) hmo) hdiv),
  rw [adjoin_singleton_eq_range_aeval] at hz,
  obtain ⟨Q, hQ⟩ := hz,
  have : ∀ i ∈ (range (Q.nat_degree + 1)).erase 0,
    Q.coeff i • B.gen ^ i * B.gen ^ (P₁.nat_degree - 1) =
    Q.coeff i • (algebra_map R L) p * f (i + (P₁.nat_degree - 1)),
  { intros i hi,
    rw [smul_mul_assoc, ← pow_add, smul_mul_assoc],
    congr,
    simp only [mem_range, mem_erase] at hi,
    have : P₁.nat_degree ≤ i + (P₁.nat_degree - 1),
    { cases P₁.nat_degree with n,
      { exact zero_le _ },
      { simp only [tsub_zero, nat.succ_sub_succ_eq_sub],
        rw [nat.succ_eq_add_one, add_comm, add_le_add_iff_right],
        exact nat.one_le_iff_ne_zero.2 hi.1 } },
    rw [hf (i + (P₁.nat_degree - 1)) this] },
  rw [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, aeval_eq_sum_range, ← insert_erase
    (show 0 ∈ range (Q.nat_degree + 1), by simp), sum_insert (not_mem_erase 0 _), pow_zero] at hQ,
  replace hQ := congr_arg (λ x, x * B.gen ^ (P₁.nat_degree - 1)) hQ,
  simp only [smul_mul_assoc] at hQ,
  rw [add_mul, smul_mul_assoc, one_mul, sum_mul, sum_congr rfl this] at hQ,
  conv_lhs at hQ { congr, skip, congr, skip, funext,
    rw [algebra.smul_mul_assoc, ← smul_def, smul_smul, mul_comm _ p, ← smul_smul] },
  replace hQ := congr_arg (norm K) (eq_sub_of_add_eq hQ),
  rw [← smul_sum, ← smul_sub, smul_def, is_scalar_tower.algebra_map_apply R K L,
    _root_.map_mul, map_pow, norm_algebra_map, smul_def, _root_.map_mul,
    is_scalar_tower.algebra_map_apply R K L, norm_algebra_map] at hQ,
  sorry
end
