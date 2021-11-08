import data.nat.parity

namespace nat

lemma even_mul_self_pred : ∀ (n : ℕ), even (n * (n - 1))
| 0 := even_zero
| (n+1) := by { rw mul_comm, apply even_mul_succ_self }

end nat
