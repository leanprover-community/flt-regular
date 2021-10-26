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

variables (n : ℕ+) (S : set ℕ+) (K L : Type*) [field K] [field L] [algebra K L]

section fintype

variables [fintype S] [is_cyclotomic_extension S K L]

namespace is_cyclotomic_extension

instance finite_dimensional : finite_dimensional K L := sorry

instance number_field [number_field K] : number_field L := sorry

end is_cyclotomic_extension

end fintype

section singleton

variables [is_cyclotomic_extension {n} K L]

namespace is_cyclotomic_extension

instance splitting_field_X_pow_sub_one : is_splitting_field K L (X ^ (n : ℕ) - 1) := sorry

instance splitting_field_cyclotomic : is_splitting_field K L (cyclotomic n K) := sorry

end is_cyclotomic_extension

end singleton

section rational

variables [char_zero L]

section singleton

variables [is_cyclotomic_extension {n} ℚ L]

lemma degree : finrank ℚ L = (n : ℕ).totient := sorry

end singleton

end rational

section cyclotomic_field

def cyclotomic_field : Type* := (cyclotomic n K).splitting_field

instance : field (cyclotomic_field n K) := sorry

instance : algebra K (cyclotomic_field n K) := sorry

instance : is_cyclotomic_extension {n} K (cyclotomic_field n K) := sorry

end cyclotomic_field

end field
