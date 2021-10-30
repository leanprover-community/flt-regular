import number_theory.cyclotomic.basic

universes u

open finite_dimensional

variables (L : Type u) [field L] [char_zero L]

namespace rat

section singleton

variables (n : ℕ+) [is_cyclotomic_extension {n} ℚ L]

lemma degree : finrank ℚ L = (n : ℕ).totient := sorry

end singleton

end rat

namespace int

section singleton

variables (n : ℕ+)

instance : is_integral_closure (cyclotomic_ring n ℤ ℚ) ℤ (cyclotomic_field n ℚ) := sorry

end singleton

end int

section int_facts

variables (p : ℕ+) [fact (p : ℕ).prime]

local notation `RR` := number_field.ring_of_integers (cyclotomic_field p ℚ)

--A.K.A theorem:FLT_facts 3
lemma flt_fact_3 (a : RR) : ∃ (n : ℤ), (a^(p : ℕ) -n) ∈ ideal.span ({p} : set RR) := sorry

end int_facts
