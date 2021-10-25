import number_theory.cyclotomic.ring.basic

variable (n : ℕ)

section finiteness

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ) [fact (0 < n)] :
  fintype (class_group (cyclotomic_ring n) (cyclotomic_field n)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n)
  (absolute_value.abs_is_admissible)

end finiteness
