import ring_theory.integral_closure

universes u v

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S]

lemma is_integral.smul {x : S} (r : R) (hx : is_integral R x) : is_integral R (r • x) :=
begin
  rw [algebra.smul_def],
  refine is_integral_mul is_integral_algebra_map hx,
end
