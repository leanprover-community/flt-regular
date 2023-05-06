import linear_algebra.smodeq
import number_theory.number_field.norm

open_locale number_field

open ring_of_integers ideal finset nat finite_dimensional

variables {K : Type*} [field K] (pb : power_basis ℤ (𝓞 K))

local notation `R` := 𝓞 K

lemma exists_int_smodeq (x : R) : ∃ (n : ℤ), smodeq (span ({pb.gen} : set R)) x n  :=
begin
  refine ⟨((pb.basis.repr) x) ⟨0, pb.dim_pos⟩, _⟩,
  have H := basis.sum_repr pb.basis x,
  rw [power_basis.coe_basis, ← insert_erase
    (mem_univ ⟨0, pb.dim_pos⟩ : (⟨0, pb.dim_pos⟩ : fin pb.dim) ∈ univ), sum_insert] at H,
  { have : ∀ i : (univ : finset (fin pb.dim)).erase ⟨0, pb.dim_pos⟩,
      ↑(((pb.basis.repr) x) i) * pb.gen ^ ((i : fin pb.dim) : ℕ) =
      ↑(((pb.basis.repr) x) i) * pb.gen ^ (i : ℕ).pred.succ,
    { rintro ⟨i, hi⟩,
      congr' 1,
      rw [succ_pred_eq_of_pos],
      rw [coe_coe, subtype.coe_mk],
      refine nat.pos_of_ne_zero (λ h, _),
      cases i with i₁ hi₁,
      simp only [coe_coe, subtype.coe_mk] at h,
      simpa [h] using hi },
    simp only [fin.coe_mk, pow_zero, int.smul_one_eq_coe, zsmul_eq_mul] at H,
    rw [← finset.sum_finset_coe] at H,
    conv_lhs at H { congr, skip, congr, skip, funext,
      rw [this i, pow_succ, ← mul_assoc, mul_comm _ pb.gen, mul_assoc] },
    rw [← mul_sum] at H,
    nth_rewrite 0 [← H],
    rw [mul_one, smodeq.def, quotient.mk_eq_mk, map_add, _root_.map_mul,
      ← submodule_span_eq, quotient.eq_zero_iff_mem.2 (submodule.mem_span_singleton_self pb.gen),
      zero_mul, add_zero, quotient.mk_eq_mk] },
  { exact not_mem_erase ⟨0, pb.dim_pos⟩ univ }
end

variables [number_field K] {pb}
variables (hpr : prime (norm ℚ pb.gen))

include hpr

lemma gen_ne_zero : pb.gen ≠ 0 :=
begin
  intro h,
  simp only [norm, monoid_hom.restrict_apply, monoid_hom.cod_restrict_apply,
    algebra.norm_eq_zero_iff.2 (show (pb.gen : K) = 0, by exact_mod_cast h)] at hpr,
  simpa using prime.ne_zero hpr
end

lemma quotient_not_trivial : nontrivial (R ⧸ (span ({pb.gen} : set R))) :=
quotient.nontrivial (λ h, hpr.not_unit ((is_unit_norm ℚ).2 (span_singleton_eq_top.1 h)))

local attribute [instance] number_field.ring_of_integers_algebra

lemma prime_of_norm_prime : prime pb.gen :=
begin
  rw [← span_singleton_prime (gen_ne_zero hpr), ← quotient.is_domain_iff_prime],
  haveI : nontrivial ((𝓞 K) ⧸ span {pb.gen}) := ⟨(quotient_not_trivial hpr).exists_pair_ne⟩,
  suffices : no_zero_divisors ((𝓞 K) ⧸ span {pb.gen}),
  { exact @no_zero_divisors.to_is_domain _ _ _ this },
  refine ⟨_⟩,
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy,
  by_contra' h,
  have h₁ := h.1, have h₂ := h.2,
  simp only [submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk] at h₁ h₂ hxy,
  obtain ⟨n, hn⟩ := exists_int_smodeq pb ⟨x, hx⟩,
  obtain ⟨m, hm⟩ := exists_int_smodeq pb ⟨y, hy⟩,
  rw [smodeq.def, quotient.mk_eq_mk] at hn hm,
  rw [hn] at h₁ hxy, rw [hm] at h₂ hxy,
  obtain ⟨z, hz⟩ := mem_span_singleton.1 (quotient.eq_zero_iff_mem.1 hxy),
  replace hz := congr_arg (norm ℚ) hz,
  have hnm : (norm ℚ) ((n : R) * (m : R)) = n ^ (finrank ℚ K) * m ^ (finrank ℚ K),
  { refine subtype.ext _,
    simp only [norm, monoid_hom.restrict_apply, mul_mem_class.coe_mul, subring_class.coe_int_cast,
      _root_.map_mul, monoid_hom.cod_restrict_apply, set_like.coe_mk, subsemiring_class.coe_pow],
    rw [show (n : K) = algebra_map ℚ K (n : ℚ), by simp, show (m : K) = algebra_map ℚ K (m : ℚ),
      by simp, algebra.norm_algebra_map, algebra.norm_algebra_map] },
  replace hz : (norm ℚ pb.gen) ∣ n ^ (finrank ℚ K) * m ^ (finrank ℚ K),
  { refine ⟨norm ℚ z, _⟩,
    rwa [← hnm, ← _root_.map_mul] },
  simp only [quotient.mk_eq_mk, map_int_cast] at h₁ h₂,
  cases hpr.dvd_or_dvd hz with Hn Hm,
  { simpa [h₁] using quotient.eq_zero_iff_mem.2 (mem_span_singleton.2 (dvd_trans (dvd_norm ℚ pb.gen)
      (ring_hom.map_dvd (algebra_map (𝓞 ℚ) R) (hpr.dvd_of_dvd_pow Hn)))) },
  { simpa [h₂] using quotient.eq_zero_iff_mem.2 (mem_span_singleton.2 (dvd_trans (dvd_norm ℚ pb.gen)
      (ring_hom.map_dvd (algebra_map (𝓞 ℚ) R) (hpr.dvd_of_dvd_pow Hm)))) },
end
