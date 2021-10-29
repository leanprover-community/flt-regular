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
