import ready_for_mathlib.power_basis

import number_theory.cyclotomic.discriminant
import field_theory.minpoly

universes u v w

open algebra polynomial nat is_primitive_root power_basis

open_locale polynomial

local attribute [instance] is_cyclotomic_extension.finite_dimensional
local attribute [instance] is_cyclotomic_extension.number_field

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
  exact discr_eq_discr _,
end

end power_basis

end is_cyclotomic_extension
