import data.polynomial.ring_division

universe u

open_locale polynomial

namespace polynomial

lemma monic_comp {R : Type u} [comm_ring R] [is_domain R] {p q : R[X]} (hp : p.monic)
  (hq : q.monic) (h : q.nat_degree ≠ 0) : (p.comp q).monic :=
begin
  rw [monic.def, leading_coeff_comp h, monic.def.1 hp, monic.def.1 hq, one_pow, one_mul],
end

lemma monic_comp_X_sub_C {R : Type u} [comm_ring R] [is_domain R] {q : R[X]} (hq : q.monic)
  (r : R) : (q.comp (X - C r)).monic :=
begin
  refine monic_comp hq (monic_X_sub_C _) (λ ha, _),
  rw [nat_degree_X_sub_C] at ha,
  exact one_ne_zero ha
end

lemma monic_comp_X_add_C {R : Type u} [comm_ring R] [is_domain R] {q : R[X]} (hq : q.monic)
  (r : R) : (q.comp (X + C r)).monic :=
begin
  refine monic_comp hq (monic_X_add_C _) (λ ha, _),
  rw [nat_degree_X_add_C] at ha,
  exact one_ne_zero ha
end

lemma mul_X_pow_injective {R : Type u} [semiring R] (n : ℕ) :
  function.injective (λ P : R[X], X ^ n * P) :=
begin
  intros P Q hPQ,
  simp only at hPQ,
  ext i,
  rw [← coeff_X_pow_mul P n i, hPQ, coeff_X_pow_mul Q n i]
end

lemma mul_X_injective {R : Type u} [semiring R] : function.injective (λ P : R[X], X * P) :=
begin
  intros P Q hPQ,
  simp only at hPQ,
  rw [← pow_one X] at hPQ,
  exact mul_X_pow_injective 1 hPQ
end

end polynomial
