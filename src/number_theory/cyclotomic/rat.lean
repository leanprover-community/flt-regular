import number_theory.cyclotomic.basic
import number_theory.cyclotomic.cyclotomic_units

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

noncomputable def flt_ideals (x y : ℤ) (i  : ℕ) : ideal RR :=
  ideal.span ({ x+y*(cyclotomic_ring.zeta p ℚ)^i} : set RR)

lemma flt_fact_2 (x y : ℤ) (i j : ℕ) (h : i ≠ j) (hp: is_coprime x y) :
  (flt_ideals p x y i) + (flt_ideals p x y i) = ⊤ := sorry

end int_facts
