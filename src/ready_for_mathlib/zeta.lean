import number_theory.cyclotomic.zeta
import ring_theory.adjoin.power_basis

noncomputable theory

open polynomial

universes u v w z

variables (n : ℕ+) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

namespace is_cyclotomic_extension

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
is_root_of_unity_of_root_cyclotomic (nat.mem_divisors_self _ n.pos.ne') (zeta_spec' _ _ _)

end is_cyclotomic_extension
