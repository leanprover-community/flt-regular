import field_theory.splitting_field

namespace polynomial

universe u

variables {K : Type u} [field K]

lemma prod_roots_eq_coeff_zero_of_monic_of_split {P : polynomial K} (hmo : P.monic)
  (hP : P.splits (ring_hom.id K)) : coeff P 0 = (-1) ^ P.nat_degree * P.roots.prod :=
begin
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, multiset.map_map],
  simp_rw [function.comp_app, eval_sub, eval_X, zero_sub, eval_C],
  conv_lhs { congr, congr, funext,
    rw [neg_eq_neg_one_mul] },
  rw [multiset.prod_map_mul, multiset.map_const, multiset.prod_repeat, multiset.map_id',
    splits_iff_card_roots.1 hP]
end

end polynomial
