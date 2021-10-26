import ring_theory.polynomial.cyclotomic

variables (K L : Type*) [comm_ring K] [comm_ring L] [algebra K L]

class is_cyclotomic_extension (S : set ℕ+) :=
( ex_root (a : ℕ+) (ha : a ∈ S) : ∃ r : L, polynomial.aeval r (polynomial.cyclotomic a K) = 0 )
( adjoint_roots : ∀ x, x ∈ algebra.adjoin K { b : L | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } )
