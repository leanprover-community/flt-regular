import ring_theory.norm

variables {K S : Type*} [field K] [comm_ring S]

namespace algebra

open polynomial matrix

--this is more precise than the umprime version
--do the same for the trace
lemma power_basis.norm_gen_eq_coeff_zero_minpoly' [algebra K S] (pb : power_basis K S) :
  (norm K pb.gen) = (-1) ^ pb.dim * coeff (minpoly K pb.gen) 0 :=
begin
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix,
    fintype.card_fin]
end

end algebra
