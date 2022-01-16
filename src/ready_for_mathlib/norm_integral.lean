import ring_theory.norm
import import field_theory.is_alg_closed.algebraic_closure

universes u v w z

variables {R : Type u} {K : Type v} {L : Type w} {F : Type z}
variables [comm_ring R] [field K] [field L] [field F]

open power_basis polynomial finite_dimensional algebra intermediate_field

namespace intermediate_field.adjoin_simple

lemma norm_gen_eq_one [algebra K L]  {x : L} (hx : ¬is_integral K x) :
  norm K (adjoin_simple.gen K x) = 1 :=
begin
  rw [norm_eq_one_of_not_exists_basis],
  contrapose! hx,
  obtain ⟨s, ⟨b⟩⟩ := hx,
  refine is_integral_of_mem_of_fg (K⟮x⟯).to_subalgebra _ x _,
  { exact (submodule.fg_iff_finite_dimensional _).mpr (of_finset_basis b) },
  { exact subset_adjoin K _ (set.mem_singleton x) }
end

lemma norm_gen_eq_prod_roots [algebra K L] [algebra K F] (x : L)
  (hf : (minpoly K x).splits (algebra_map K F)) :
  (algebra_map K F) (norm K (gen K x)) = ((minpoly K x).map (algebra_map K F)).roots.prod :=
begin
  have injKKx : function.injective (algebra_map K K⟮x⟯) := ring_hom.injective _,
  have injKxL : function.injective (algebra_map K⟮x⟯ L) := ring_hom.injective _,
  by_cases hx : is_integral K x, swap,
  { simp [minpoly.eq_zero hx, norm_gen_eq_one hx] },
  have hx' : is_integral K (adjoin_simple.gen K x),
  { rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen],
    apply_instance },
  rw [← adjoin.power_basis_gen hx],
  rw [power_basis.norm_gen_eq_prod_roots];
  rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'];
  try { simp only [adjoin_simple.algebra_map_gen _ _] },
  exact hf
end

end intermediate_field.adjoin_simple

namespace algebra

lemma norm_eq_prod_roots [algebra K L] [algebra K F] [is_separable K L] [finite_dimensional K L]
  {x : L} (hF : splits (algebra_map K F) (minpoly K x)) :
  (algebra_map K F) (norm K x) =
  ((minpoly K x).map (algebra_map K F)).roots.prod ^ finrank (K⟮x⟯) L :=
by rw [norm_eq_norm_adjoin K x, ring_hom.map_pow,
  intermediate_field.adjoin_simple.norm_gen_eq_prod_roots _ hF]

lemma is_integral_norm [algebra R L] [algebra R K] [algebra K L] [is_scalar_tower R K L]
  [is_separable K L] [finite_dimensional K L] {x : L} (hx : _root_.is_integral R x) :
  _root_.is_integral R (norm K x) :=
begin
  have hx' : _root_.is_integral K x := is_integral_of_is_scalar_tower _ hx,
  rw [← is_integral_algebra_map_iff (algebra_map K (algebraic_closure L)).injective,
      norm_eq_prod_roots],
  { refine (is_integral.multiset_prod (λ y hy, _)).pow _,
    rw mem_roots_map (minpoly.ne_zero hx') at hy,
    use [minpoly R x, minpoly.monic hx],
    rw ← aeval_def at ⊢ hy,
    exact minpoly.aeval_of_is_scalar_tower R x y hy },
  { apply is_alg_closed.splits_codomain },
  { apply_instance }
end

end algebra
