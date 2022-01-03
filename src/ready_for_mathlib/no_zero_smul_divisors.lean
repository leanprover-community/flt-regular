import ring_theory.localization

namespace is_fraction_ring

instance {R K} [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K] :
  no_zero_smul_divisors R K :=
no_zero_smul_divisors.of_algebra_map_injective $ is_fraction_ring.injective R K

end is_fraction_ring
