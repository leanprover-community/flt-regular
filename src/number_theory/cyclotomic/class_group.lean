import number_theory.cyclotomic.basic
import number_theory.class_number.finite
import number_theory.class_number.admissible_abs

variable (n : ℕ+)

section finiteness

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ+) :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n ℚ)
  absolute_value.abs_is_admissible

end finiteness
