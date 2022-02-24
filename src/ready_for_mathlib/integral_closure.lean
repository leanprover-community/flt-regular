import ring_theory.integral_closure

universes u v

variables {R : Type u} {A : Type v} [comm_ring R] [comm_ring A] [algebra R A]

open polynomial

lemma is_integral_smul {x : A} (r : R) (hx : is_integral R x) : is_integral R (r • x) :=
begin
  rw [algebra.smul_def],
  refine is_integral_mul is_integral_algebra_map hx,
end

lemma is_integral_of_aeval {a  : A} {P : polynomial R} (ha : is_integral R a) :
  is_integral R (aeval a P) :=
begin
  rw [aeval_eq_sum_range],
  exact is_integral.sum _ (λ i _, is_integral_smul _ (is_integral.pow ha _)),
end
