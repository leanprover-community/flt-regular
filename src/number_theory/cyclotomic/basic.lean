import ring_theory.polynomial.cyclotomic
import number_theory.number_field

open polynomial algebra finite_dimensional

section basic

variables (S : set ℕ+) (K L : Type*) [comm_ring K] [comm_ring L] [algebra K L]

class is_cyclotomic_extension :=
( ex_root (a : ℕ+) (ha : a ∈ S) : ∃ r : L, aeval r (cyclotomic a K) = 0 )
( adjoint_roots : ∀ x, x ∈ adjoin K { b : L | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } )

--TODO: add equivalent definitions

end basic

section field

variables (K L : Type*) [field K] [field L] [algebra K L]

section singleton

variables (n : ℕ+) [is_cyclotomic_extension {n} K L]

namespace is_cyclotomic_extension

instance splitting_field_X_pow_sub_one : is_splitting_field K L (X ^ (n : ℕ) - 1) := sorry

instance splitting_field_cyclotomic : is_splitting_field K L (cyclotomic n K) := sorry

instance finite_dimensional : finite_dimensional K L := sorry

instance number_field [number_field K] : number_field L := sorry

end is_cyclotomic_extension

end singleton

end field

section rational

variables (L : Type*) [field L] [char_zero L]

section singleton

variables (n : ℕ+) [is_cyclotomic_extension {n} ℚ L]

lemma degree : finrank ℚ L = (n : ℕ).totient := sorry

end singleton

end rational
