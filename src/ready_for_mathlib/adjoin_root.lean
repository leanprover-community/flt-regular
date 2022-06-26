import ring_theory.adjoin_root
import ready_for_mathlib.minpoly

variables {R A B : Type*}

namespace alg_hom

open subalgebra

variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

lemma range_top_iff_surjective (f : A →ₐ[R] B) :
f.range = (⊤ : subalgebra R B) ↔ function.surjective f :=
algebra.eq_top_iff --I think this formulation can be useful `eq_top_iff` doesn't work below

end alg_hom

variables (R) [comm_ring R] [comm_ring A] [algebra R A] (x : A)
variables (hinj : function.injective (algebra_map R A))

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

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A]

include hinj

lemma minpoly.to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  have hPcont : P.content ≠ 0 := λ h, hPzero (content_eq_zero_iff.1 h),
  rw [← hP, minpoly.to_adjoin_apply, lift_hom_mk, ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, P.eq_C_content_mul_prim_part, aeval_mul, aeval_C] at hP₁,
  replace hP₁ := eq_zero_of_ne_zero_of_mul_left_eq_zero ((map_ne_zero_iff _ hinj).2 hPcont) hP₁,
  obtain ⟨Q, hQ⟩ := minpoly.gcd_domain_dvd' hx hinj P.is_primitive_prim_part.ne_zero hP₁,
  rw [P.eq_C_content_mul_prim_part] at hP,
  simpa [hQ] using hP.symm
end

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps] def minpoly.to_adjoin_equiv (hx : is_integral R x) :
  adjoin_root (minpoly R x) ≃ₐ[R] adjoin R ({x} : set A) :=
alg_equiv.of_bijective (minpoly.to_adjoin R x)
  ⟨minpoly.to_adjoin.injective hinj hx, minpoly.to_adjoin.surjective R x⟩

end adjoin_root

open adjoin_root

namespace algebra

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A]

include hinj

/-- The `power_basis` of `adjoin R {x}` given by `x`. -/
@[simps] def adjoin.power_basis' (hx : _root_.is_integral R x) :
  power_basis R (adjoin R ({x} : set A)) :=
power_basis.map (adjoin_root.power_basis' (minpoly.monic hx)) (minpoly.to_adjoin_equiv hinj hx)

lemma adjoin.power_basis_gen' (hx : _root_.is_integral R x) :
  (adjoin.power_basis' hinj hx).gen = ⟨x, self_mem_adjoin_singleton R x⟩ :=
by simp

end algebra

namespace power_basis

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A]

include hinj

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
@[simps] noncomputable def of_gen_mem_adjoin' (B : power_basis R A) (hint : is_integral R x)
  (hx : B.gen ∈ adjoin R ({x} : set A)) : power_basis R A :=
(algebra.adjoin.power_basis' hinj hint).map $
  (subalgebra.equiv_of_eq _ _ $ power_basis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
  subalgebra.top_equiv

end power_basis
