import data.polynomial.monic

universes u v

namespace polynomial

variables {R : Type u} {S : Type v} [semiring R] [semiring S]

lemma nat_degree_map_of_monic [nontrivial S] {P : polynomial R} (hmo : P.monic) (f : R →+* S) :
  P.nat_degree = (P.map f).nat_degree :=
begin
  refine le_antisymm (le_nat_degree_of_ne_zero _) (nat_degree_map_le _ _),
  rw [coeff_map, monic.coeff_nat_degree hmo, ring_hom.map_one],
  exact one_ne_zero
end

lemma degree_map_of_monic [nontrivial S] {P : polynomial R} (hmo : P.monic) (f : R →+* S) :
  P.degree = (P.map f).degree :=
begin
  by_cases hP : P = 0,
  { simp [hP] },
  { refine le_antisymm _ (degree_map_le _ _),
    rw [degree_eq_nat_degree hP],
    refine le_degree_of_ne_zero _,
    rw [coeff_map, monic.coeff_nat_degree hmo, ring_hom.map_one],
    exact one_ne_zero }
end

end polynomial
