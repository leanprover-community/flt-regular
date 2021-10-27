import number_theory.cyclotomic.basic
import number_theory.class_number.finite

variable (n : ℕ+)

section finiteness


open new_cyclotomic_field

instance a  : is_domain  (cyclotomic_ring n ℤ ℚ ) := sorry

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ+) :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n ℚ)
  (absolute_value.abs_is_admissible)

end finiteness
