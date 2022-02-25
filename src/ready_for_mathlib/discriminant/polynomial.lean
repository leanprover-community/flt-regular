import data.polynomial.ring_division

universe u

open_locale polynomial

namespace polynomial

variables {R : Type u} [comm_ring R]

lemma monic_comp [is_domain R] {p q : R[X]} (hp : p.monic) (hq : q.monic) (h : q.nat_degree ≠ 0) :
  (p.comp q).monic :=
begin
  rw [monic.def, leading_coeff_comp h, monic.def.1 hp, monic.def.1 hq, one_pow, one_mul],
end

end polynomial
