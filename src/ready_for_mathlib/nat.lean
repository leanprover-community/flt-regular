import data.nat.parity

namespace nat

lemma even_mul_self_pred : ∀ (n : ℕ), even (n * (n - 1))
| 0 := even_zero
| (n+1) := by { rw mul_comm, apply even_mul_succ_self }

--I don't find this
lemma even_of_prime_neq_two_sub_one {p : ℕ} (hp : prime p) (hodd : p ≠ 2) : even (p - 1) := sorry

end nat
