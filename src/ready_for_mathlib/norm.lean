import ring_theory.norm
import field_theory.is_alg_closed.algebraic_closure
import field_theory.primitive_element

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L E : Type*} [field K] [field L] [field E] [algebra K L] [algebra K E]
variables {ι : Type w} [fintype ι]

open finite_dimensional intermediate_field matrix polynomial

open_locale big_operators

namespace algebra

namespace intermediate_field.adjoin_simple

variable (K)

lemma norm_eq_norm_adjoin [finite_dimensional K L] [is_separable K L] (x : L) :
  norm K x = (norm K (adjoin_simple.gen K x)) ^ (finrank K⟮x⟯ L) :=
begin
  letI := is_separable_tower_top_of_is_separable K K⟮x⟯ L,
  let pbL := field.power_basis_of_finite_of_separable K⟮x⟯ L,
  let pbx := intermediate_field.adjoin.power_basis (is_separable.is_integral K x),
  rw [← adjoin_simple.algebra_map_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_left_mul_matrix_algebra_map, det_block_diagonal, norm_eq_matrix_det pbx.basis],
  simp only [finset.card_fin, finset.prod_const, adjoin.power_basis_basis],
  congr,
  rw [← power_basis.finrank, adjoin_simple.algebra_map_gen K x],
end

end intermediate_field.adjoin_simple

end algebra
