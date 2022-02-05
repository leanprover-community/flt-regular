import algebra.algebra.basic

lemma no_zero_smul_divisors.trans {R S M : Type*} [comm_ring R] [ring S] [is_domain S] [algebra R S]
  [add_comm_group M] [module R M] [module S M] [is_scalar_tower R S M] [no_zero_smul_divisors R S]
  [no_zero_smul_divisors S M] : no_zero_smul_divisors R M :=
begin
  refine ⟨λ r m h, _⟩,
  rw [algebra_compatible_smul S r m] at h,
  cases smul_eq_zero.1 h with H H,
  { have : function.injective (algebra_map R S) :=
      no_zero_smul_divisors.iff_algebra_map_injective.1 infer_instance,
    left,
    exact (ring_hom.injective_iff _).1 this _ H },
  { right,
    exact H }
end
