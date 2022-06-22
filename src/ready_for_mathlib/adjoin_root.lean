import ring_theory.adjoin_root

namespace alg_hom

open subalgebra

variables {R A B : Type*} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

lemma range_top_iff_surjective (f : A →ₐ[R] B) :
f.range = (⊤ : subalgebra R B) ↔ function.surjective f :=
algebra.eq_top_iff --I think this formulation can be useful `eq_top_iff` doesn't work below

end alg_hom

variables (R : Type*) [comm_ring R] {A : Type*} [comm_ring A] [algebra R A] (x : A)

noncomputable theory

open algebra polynomial

namespace adjoin_root

/-- The algebra morphism `adjoin_root (minpoly R x) →ₐ[R] adjoin R x` -/
def minpoly.to_adjoin : adjoin_root (minpoly R x) →ₐ[R] adjoin R ({x} : set A) :=
lift_hom _ ⟨x, self_mem_adjoin_singleton R x⟩
  (by simp [← subalgebra.coe_eq_zero, aeval_subalgebra_coe])

variables {R x}

@[simp] lemma minpoly.to_adjoin_apply (a : adjoin_root (minpoly R x)) : (minpoly.to_adjoin R x) a =
  lift_hom (minpoly R x) (⟨x, self_mem_adjoin_singleton R x⟩ : adjoin R ({x} : set A))
  (by simp [← subalgebra.coe_eq_zero, aeval_subalgebra_coe]) a := rfl

variables (R x)

lemma minpoly.to_adjoin.apply_X : (minpoly.to_adjoin R x) (mk (minpoly R x) X) =
  ⟨x, self_mem_adjoin_singleton R x⟩ :=
by simp

lemma minpoly.to_adjoin.surjective : function.surjective (minpoly.to_adjoin R x) :=
begin
  rw [← alg_hom.range_top_iff_surjective, _root_.eq_top_iff, ← adjoin_adjoin_coe_preimage],
  refine adjoin_le _,
  simp only [alg_hom.coe_range, set.mem_range],
  rintro ⟨y₁, y₂⟩ h,
  refine ⟨mk (minpoly R x) X, by simpa using h.symm⟩
end

variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K] [algebra K A] {R}
variables {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A] [is_scalar_tower R K A]

include K

lemma minpoly.to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  have hinj : function.injective (algebra_map R A) := (is_scalar_tower.algebra_map_eq R K A).symm ▸
    (algebra_map K A).injective.comp (is_fraction_ring.injective R K),
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  have hPcont : P.content ≠ 0 := λ h, hPzero (content_eq_zero_iff.1 h),
  rw [← hP, minpoly.to_adjoin_apply, lift_hom_mk, ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, P.eq_C_content_mul_prim_part, aeval_mul, aeval_C] at hP₁,
  replace hP₁ := eq_zero_of_ne_zero_of_mul_left_eq_zero ((map_ne_zero_iff _ hinj).2 hPcont) hP₁,
  obtain ⟨Q, hQ⟩ := minpoly.gcd_domain_dvd K hx P.is_primitive_prim_part hP₁,
  rw [P.eq_C_content_mul_prim_part, map_mul, hQ, map_mul, mk_self, zero_mul, mul_zero] at hP,
  exact hP.symm
end

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps] def minpoly.to_adjoin_equiv (hx : is_integral R x) :
  adjoin_root (minpoly R x) ≃ₐ[R] adjoin R ({x} : set A) :=
alg_equiv.of_bijective (minpoly.to_adjoin R x)
  ⟨minpoly.to_adjoin.injective K hx, minpoly.to_adjoin.surjective R x⟩

end adjoin_root
