import ring_theory.polynomial.cyclotomic
import number_theory.number_field

open polynomial algebra finite_dimensional

universes u v w z

variables (n : ℕ+) (S : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

namespace new_cyclotomic_field

section basic

class is_cyclotomic_extension :=
( ex_root (a : ℕ+) (ha : a ∈ S) : ∃ r : B, aeval r (cyclotomic a A) = 0 )
( adjoint_roots : ∀ x, x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } )

--TODO: add equivalent definitions

end basic

section field

section fintype

variables [fintype S] [is_cyclotomic_extension S K L]

namespace is_cyclotomic_extension

instance finite_dimensional : finite_dimensional K L := sorry

lemma number_field [number_field K] : number_field L := sorry

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

@[derive [field, algebra K]]
def cyclotomic_field : Type w := (cyclotomic n K).splitting_field

namespace cyclotomic_field

lemma is_cyclotomic_extension : is_cyclotomic_extension {n} K (cyclotomic_field n K) := sorry

end cyclotomic_field

end cyclotomic_field

end field

section is_domain

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

section cyclotomic_ring

instance cyclotomic_field_algebra : algebra A (cyclotomic_field n K) :=
((algebra_map K (cyclotomic_field n K)).comp (algebra_map A K)).to_algebra

@[derive [comm_ring, algebra A]]
def cyclotomic_ring : Type w := adjoin A { b : (cyclotomic_field n K) | b ^ (n : ℕ) = 1 }

namespace cyclotomic_ring

lemma eq_adjoin_single (μ : (cyclotomic_field n K))
  (h : μ ∈ primitive_roots n ((cyclotomic_field n K))) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) := sorry

instance : is_domain  (cyclotomic_ring n A K) := sorry

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) := sorry

lemma is_cyclotomic_extension : is_cyclotomic_extension {n} A (cyclotomic_ring n A K) := sorry

instance : is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) := sorry

end cyclotomic_ring

end cyclotomic_ring

section integers

instance cyclotomic_ring_int_is_integral_closure :
  is_integral_closure (cyclotomic_ring n ℤ ℚ) ℤ (cyclotomic_field n ℚ) := sorry

end integers

end is_domain

end new_cyclotomic_field
