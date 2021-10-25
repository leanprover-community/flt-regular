import number_theory.cyclotomic.ring.basic

variable (n : ℕ)

section finiteness

instance a (n : ℕ) [fact (0 < n)] : is_fraction_ring (cyclotomic_ring n) (cyclotomic_field n) := sorry

instance b (n : ℕ) [fact (0 < n)] : is_integral_closure (cyclotomic_ring n) ℤ  (cyclotomic_field n) := sorry

noncomputable instance class_group.fintype_of_cyclotomic_ring (n : ℕ) [fact (0 < n)] :
  fintype (class_group (cyclotomic_ring n) (cyclotomic_field n)) :=
class_group.fintype_of_admissible_of_finite ℚ (cyclotomic_field n)
  (absolute_value.abs_is_admissible)

end finiteness
