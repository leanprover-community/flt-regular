import ring_theory.norm

import ready_for_mathlib.polynomial

universes u v w

namespace algebra

open polynomial

variables {S : Type u} {K : Type v} {F : Type w} [comm_ring S] [field K] [field F]
variables [algebra K F] [algebra K S]

lemma norm_gen_eq_coeff_zero_minpoly (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  (algebra_map K F) (norm K pb.gen) =
  (-1) ^ (minpoly K pb.gen).nat_degree * coeff ((minpoly K pb.gen).map (algebra_map K F)) 0 :=
begin
  rw [norm_gen_eq_prod_roots pb hf, prod_roots_eq_coeff_zero_of_monic_of_split
    (monic_map _ (minpoly.monic (power_basis.is_integral_gen _))) ((splits_id_iff_splits _).2 hf)],
  simp only [power_basis.nat_degree_minpoly, nat_degree_map],
  rw [← mul_assoc, ← mul_pow],
  simp
end

end algebra
