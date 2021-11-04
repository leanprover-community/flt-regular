import data.polynomial.derivative
import field_theory.splitting_field

universes u v

namespace polynomial

open multiset

lemma eval_root_derivative {R : Type u} [decidable_eq R] [comm_ring R] {S : multiset R} {r : R}
  (hr : r ∈ S) : eval r (multiset.map (λ a, X - C a) S).prod.derivative =
  (multiset.map (λ a, r - a) (S.erase r)).prod :=
begin
  nth_rewrite 0 [← cons_erase hr],
  simpa using (eval_ring_hom r).map_multiset_prod (multiset.map (λ a, X - C a) (S.erase r)),
end

lemma eval_root_derivative_of_split {K : Type u} {L : Type v} [decidable_eq L] [field K] [field L]
  [algebra K L] {P : polynomial K} (hmo : P.monic) (hP : P.splits (algebra_map K L)) {r : L}
  (hr : r ∈ (P.map (algebra_map K L)).roots) : aeval r P.derivative =
  (multiset.map (λ a, r - a) ((P.map (algebra_map K L)).roots.erase r)).prod :=
begin
  replace hmo := monic_map (algebra_map K L) hmo,
  replace hP := (splits_id_iff_splits (algebra_map K L)).2 hP,
  rw [aeval_def, ← eval_map, ← derivative_map],
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [eval_root_derivative hr]
end

end polynomial
