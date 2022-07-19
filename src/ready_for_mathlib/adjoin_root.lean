import ring_theory.adjoin_root

variables {R A B : Type*}

namespace alg_hom

open subalgebra

variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

lemma range_top_iff_surjective (f : A →ₐ[R] B) :
f.range = (⊤ : subalgebra R B) ↔ function.surjective f :=
algebra.eq_top_iff --I think this formulation can be useful `eq_top_iff` doesn't work below

end alg_hom

variables (R) [comm_ring R] [comm_ring A] [algebra R A] (x : A)

noncomputable theory

open algebra polynomial

namespace adjoin_root

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A] [no_zero_smul_divisors R A]

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps] def minpoly.to_adjoin_equiv (hx : is_integral R x) :
  adjoin_root (minpoly R x) ≃ₐ[R] adjoin R ({x} : set A) :=
alg_equiv.of_bijective (minpoly.to_adjoin R x)
  ⟨minpoly.to_adjoin.injective hx, minpoly.to_adjoin.surjective R x⟩

end adjoin_root

open adjoin_root

namespace algebra

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A] [no_zero_smul_divisors R A]

lemma adjoin.power_basis_gen' (hx : _root_.is_integral R x) :
  (adjoin.power_basis' hx).gen = ⟨x, self_mem_adjoin_singleton R x⟩ :=
by simp

end algebra

namespace power_basis

variables {R} {x} [is_domain R] [normalized_gcd_monoid R] [is_domain A] [no_zero_smul_divisors R A]

end power_basis
