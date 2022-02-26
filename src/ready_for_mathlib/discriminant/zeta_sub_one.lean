import ready_for_mathlib.discriminant.power_basis
import ready_for_mathlib.minpoly

import number_theory.cyclotomic.discriminant

universes u v w

open algebra polynomial nat is_primitive_root power_basis

open_locale polynomial

local attribute [instance] is_cyclotomic_extension.finite_dimensional
local attribute [instance] is_cyclotomic_extension.number_field

namespace is_primitive_root

variables {L : Type v} [field L] {ζ : L} {n : ℕ+} (hζ : is_primitive_root ζ n)
variables (K : Type u) {p : ℕ+} [linear_ordered_field K]
variables [algebra K L] [ne_zero ((p : ℕ) : K)] [is_cyclotomic_extension {n} K L]

include hζ

lemma power_basis_gen_mem_adjoin : (power_basis K hζ).gen ∈ adjoin K ({ζ - 1} : set L) :=
begin
  rw [power_basis_gen, adjoin_singleton_eq_range_aeval, alg_hom.mem_range],
  exact ⟨X + 1, by simp⟩
end

/-- The `power_basis` given by `ζ - 1`. -/
@[simps] noncomputable def sub_one_power_basis : _root_.power_basis K L :=
(hζ.power_basis K).of_mem_adjon (is_integral_sub (is_separable.is_integral K ζ) is_integral_one)
  (hζ.power_basis_gen_mem_adjoin K)

lemma sub_one_minpoly_eq_cyclotomic_comp (h : irreducible (polynomial.cyclotomic n K)) :
  minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1) :=
begin
  rw [show ζ - 1 = ζ + (algebra_map K L (-1)), by simp [sub_eq_add_neg], minpoly_add_algebra_map
    (is_separable.is_integral K ζ), hζ.minpoly_eq_cyclotomic_of_irreducible h],
  simp
end

end is_primitive_root

namespace is_cyclotomic_extension

section power_basis

variables {p : ℕ+} [hp : fact (p : ℕ).prime] {K : Type u} [field K] [char_zero K] {ζ : K}
variables [is_cyclotomic_extension {p} ℚ K]

include hp

lemma discr_eq_discr (hζ : is_primitive_root ζ p)  :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis =
  discr ℚ (hζ.power_basis ℚ).basis :=
begin
  have H₁ : (aeval (hζ.sub_one_power_basis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.power_basis ℚ).gen :=
    by simp,
  have H₂ : (aeval (hζ.power_basis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.sub_one_power_basis ℚ).gen :=
    by simp,
  refine discr_eq_discr_of_to_matrix_coeff_is_integral _
    (λ i j, to_matrix_is_integral_coeff H₁ _  _ _ _)
    (λ i j, to_matrix_is_integral_coeff H₂ _  _ _ _),
  { exact is_integral_sub (hζ.is_integral hp.out.pos) is_integral_one },
  { refine minpoly.gcd_domain_eq_field_fractions _ _,
    exact is_integral_sub (hζ.is_integral hp.out.pos) is_integral_one },
  { exact hζ.is_integral hp.out.pos },
  { refine minpoly.gcd_domain_eq_field_fractions _ (hζ.is_integral hp.out.pos) }
end

lemma discr_odd_prime' (hζ : is_primitive_root ζ p) (hodd : p ≠ 2) :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd],
  exact discr_eq_discr _ _,
end

end power_basis

end is_cyclotomic_extension
