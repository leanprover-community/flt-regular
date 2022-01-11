import field_theory.intermediate_field

namespace intermediate_field

open_locale big_operators

open polynomial

variables {K L ι : Type*} [field K] [field L] [algebra K L] {S : intermediate_field K L}

lemma coe_sum [fintype ι] (f : ι → S) : (↑∑ i, f i : L) = ∑ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.sum_insert hi, coe_add, H, finset.sum_insert hi] }
end

lemma coe_prod [fintype ι] (f : ι → S) : (↑∏ i, f i : L) = ∏ i, (f i : L) :=
begin
  classical,
  induction finset.univ using finset.induction_on with i s hi H,
  { simp },
  { rw [finset.prod_insert hi, coe_mul, H, finset.prod_insert hi] }
end

lemma coe_is_integral {R : Type*} [comm_ring R] [algebra R K] [algebra R L] [is_scalar_tower R K L]
  {x : S} (hx : is_integral R (x : L)) : is_integral R x :=
begin
  obtain ⟨P, hP⟩ := hx,
  refine ⟨P, hP.1, _⟩,
  refine (ring_hom.injective_iff _).1 (algebra_map ↥S L).injective _ _,
  letI : is_scalar_tower R S L := is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
  rw [eval₂_eq_eval_map, ← eval₂_at_apply, eval₂_eq_eval_map, polynomial.map_map,
    ← is_scalar_tower.algebra_map_eq, ← eval₂_eq_eval_map],
  exact hP.2
end

end intermediate_field
