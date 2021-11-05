import data.nat.parity

namespace nat

--I didn't find this
lemma even_mul_self_pred (n : ℕ) : even (n * (n - 1)) :=
begin
  rw [even_mul],
  by_cases h : even n,
  { exact or.inl h},
  { right,
    cases n,
    { simp },
    { simpa with parity_simps using h } }
end

end nat
