import ring_theory.integral_closure

universes u v w

variables {R : Type u} {S : Type w} {A : Type v}
variables [comm_ring R] [comm_ring S] [comm_ring A]
variables [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A]

open polynomial

open_locale polynomial

lemma is_integral_of_aeval {a  : A} (P : R[X]) (ha : is_integral S a) :
  is_integral S (aeval a P) :=
begin
  rw [is_scalar_tower.aeval_apply R S A, aeval_eq_sum_range],
  refine is_integral.sum _ (λ i _, _),
  rw [coeff_map],
  exact is_integral_smul _ (is_integral.pow ha _),
end
