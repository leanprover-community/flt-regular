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

lemma discr_odd_prime' (hζ : is_primitive_root ζ p) (hodd : p ≠ 2) :
  discr ℚ (hζ.sub_one_power_basis ℚ).basis =
  (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) :=
begin
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd],
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
end

end power_basis

end is_cyclotomic_extension
