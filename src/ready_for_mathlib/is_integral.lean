import ring_theory.integral_closure
import number_theory.number_field

namespace alg_hom

open polynomial

variables {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]
variables [algebra A B] [is_scalar_tower R A B] {x : B} (f : B →ₐ[A] B)

lemma is_integral_of_is_scalar_tower (hx : is_integral R x) : _root_.is_integral R (f x) :=
begin
  obtain ⟨P, hP⟩ := hx,
  refine ⟨P, hP.1, _⟩,
  rw [← aeval_def, show (aeval (f x)) P = (aeval (f x)) (P.map (algebra_map R A)), by simp,
    aeval_alg_hom_apply, aeval_map, aeval_def, hP.2, map_zero]
end

end alg_hom

namespace number_field

open_locale number_field

variables {K : Type*} [field K] [number_field K] (φ : K ≃ₐ[ℚ] K)

lemma alg_equiv_is_integral {x : K} (hx : is_integral ℤ x) : is_integral ℤ (φ x) :=
alg_hom.is_integral_of_is_scalar_tower φ.to_alg_hom hx

lemma alg_equiv_mem_ring_of_integers {x : 𝓞 K} : φ x ∈ 𝓞 K :=
(mem_ring_of_integers _ _).2 $ alg_equiv_is_integral _ $ ring_of_integers.is_integral_coe x

end number_field
