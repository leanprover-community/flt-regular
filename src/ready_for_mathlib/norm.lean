import ring_theory.norm
import field_theory.is_alg_closed.algebraic_closure
import field_theory.primitive_element

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L E : Type*} [field K] [field L] [field E] [algebra K L] [algebra K E] [algebra L E]
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

section eq_prod_embeddings

open intermediate_field.adjoin_simple

variables (F : Type*) [field F] [algebra L F] [algebra K F] [is_scalar_tower K L E]
variables [is_scalar_tower K L F]

variable (E)

lemma norm_eq_prod_embeddings_gen
  (pb : power_basis K L)
  (hE : (minpoly K pb.gen).splits (algebra_map K E)) (hfx : (minpoly K pb.gen).separable) :
  algebra_map K E (norm K pb.gen) =
    (@@finset.univ (power_basis.alg_hom.fintype pb)).prod (λ σ, σ pb.gen) :=
begin
  letI := classical.dec_eq E,
  rw [norm_gen_eq_prod_roots pb hE, fintype.prod_equiv pb.lift_equiv', finset.prod_mem_multiset,
    finset.prod_eq_multiset_prod, multiset.to_finset_val,
    multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx)), multiset.map_id],
  { intro x, refl },
  { intro σ, rw [power_basis.lift_equiv'_apply_coe, id.def] }
end

lemma prod_embeddings_eq_finrank_pow (E : Type*) [field E] [algebra K E] [is_alg_closed E]
  [is_separable K F] [finite_dimensional K F]
  (pb : power_basis K L) : ∏ σ : F →ₐ[K] E, σ (algebra_map L F pb.gen) =
  ((@@finset.univ (power_basis.alg_hom.fintype pb)).prod
    (λ σ : L →ₐ[K] E, σ pb.gen)) ^ finrank L F :=
begin
  haveI : finite_dimensional L F := finite_dimensional.right K L F,
  haveI : is_separable L F := is_separable_tower_top_of_is_separable K L F,
  letI : fintype (L →ₐ[K] E) := power_basis.alg_hom.fintype pb,
  letI : ∀ (f : L →ₐ[K] E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _,
  rw [fintype.prod_equiv alg_hom_equiv_sigma (λ (σ : F →ₐ[K] E), _) (λ σ, σ.1 pb.gen),
     ← finset.univ_sigma_univ, finset.prod_sigma, ← finset.prod_pow],
  refine finset.prod_congr rfl (λ σ _, _),
  { letI : algebra L E := σ.to_ring_hom.to_algebra,
    simp only [finset.prod_const, finset.card_univ],
    congr,
    rw alg_hom.card L F E },
  { intros σ,
    simp only [alg_hom_equiv_sigma, equiv.coe_fn_mk, alg_hom.restrict_domain, alg_hom.comp_apply,
         is_scalar_tower.coe_to_alg_hom'] }
end

lemma norm_eq_prod_embeddings [finite_dimensional K L] [is_separable K L] [is_alg_closed E]
  {x : L} : algebra_map K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
begin
  have hx := is_separable.is_integral K x,
  rw [norm_eq_norm_adjoin K x, ring_hom.map_pow, ← adjoin.power_basis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _)],
  { exact (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm },
  { haveI := is_separable_tower_bot_of_is_separable K K⟮x⟯ L,
    exact is_separable.separable K _ }
end

end eq_prod_embeddings

end algebra
