import ring_theory.integral_closure

namespace alg_hom

open polynomial

variables {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]
variables [algebra A B] [is_scalar_tower R A B] {x : B} {f : B →ₐ[A] B}

lemma is_integral_of_is_scalar_tower (hx : _root_.is_integral R x) : _root_.is_integral R (f x) :=
begin
  obtain ⟨P, hP⟩ := hx,
  refine ⟨P, hP.1, _⟩,
  rw [← aeval_def, show (aeval (f x)) P = (aeval (f x)) (P.map (algebra_map R A)), by simp,
    aeval_alg_hom_apply, aeval_map, aeval_def, hP.2, map_zero]
end

end alg_hom
