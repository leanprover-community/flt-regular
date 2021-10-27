import number_theory.cyclotomic.basic
import number_theory.class_number.finite

variable (n : ℕ+)

section finiteness

open new_cyclotomic_field

--set_option pp.all true
noncomputable lemma class_group.fintype_of_cyclotomic_ring (n : ℕ+) :
  fintype (class_group (cyclotomic_ring n ℤ ℚ) (cyclotomic_field n ℚ)) :=
begin
  refine @class_group.fintype_of_admissible_of_finite ℤ _ ℚ (cyclotomic_field n ℚ)
  _ _ _ _ _ _ _ _ _ _ _
  (@add_comm_group.int_is_scalar_tower ℚ (cyclotomic_field n ℚ) _ _ _)
  _ _ _ _ _ _ _ _ _,

end
end finiteness
