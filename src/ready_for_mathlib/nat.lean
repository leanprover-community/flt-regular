import data.nat.parity

namespace nat

lemma even_mul_self_pred : ∀ (n : ℕ), even (n * (n - 1))
| 0 := even_zero
| (n+1) := by { rw mul_comm, apply even_mul_succ_self }

lemma even_of_prime_neq_two_sub_one {p : ℕ} (hp : prime p) (hodd : p ≠ 2) : even (p - 1) :=
odd.sub_odd (odd_iff.2 (or_iff_not_imp_left.1 (nat.prime.eq_two_or_odd hp) hodd)) $ odd_iff.2 rfl

end nat
