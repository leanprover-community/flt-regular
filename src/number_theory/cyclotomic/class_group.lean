import number_theory.class_number.finite
import number_theory.class_number.admissible_abs

import number_theory.cyclotomic.rat

variable (n : ℕ+)

section finiteness

local attribute [instance] is_cyclotomic_extension.finite_dimensional

--this has something to do with `(p : ℕ)`
instance should_be_automatic : is_fraction_ring (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ) :=
sorry

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ+) :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n ℚ)
  absolute_value.abs_is_admissible

end finiteness
