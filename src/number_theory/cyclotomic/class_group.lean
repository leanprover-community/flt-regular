import number_theory.class_number.finite
import number_theory.class_number.admissible_abs

import number_theory.cyclotomic.cycl_rat

variable (n : ℕ+)

section finiteness

instance : is_integral_closure (cyclotomic_ring n ℤ ℚ) ℤ (cyclotomic_field n ℚ) := sorry

local attribute [instance] is_cyclotomic_extension.finite_dimensional

-- todo: we should change this definition to not use `cyclotomic_ring`.

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ+) :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n ℚ)
  absolute_value.abs_is_admissible

end finiteness
