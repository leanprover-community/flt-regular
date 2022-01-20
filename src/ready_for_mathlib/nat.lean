import data.nat.basic

namespace nat

lemma le_of_pos_add_prec (n : ℕ) {i : ℕ} (hi : i ≠ 0) : n ≤ i + (n - 1) :=
begin
  cases n,
  { simp },
  { rw [succ_sub_one, succ_eq_add_one, add_comm, add_le_add_iff_right],
    exact nat.one_le_iff_ne_zero.2 hi }
end

end nat
