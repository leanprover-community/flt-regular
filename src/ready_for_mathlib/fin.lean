import data.fin.interval

namespace fin

open finset

lemma Ioi_eq_finset_subtype {n : ℕ} (a : fin (n + 1)) :
  Ioi a = (Ioo (a : ℕ) (n + 1)).subtype (λ x, x < n + 1) :=
by { ext, simp [is_lt] }

lemma card_Ioi (n : ℕ) (a : fin (n + 1)) : (Ioi a).card = n - a :=
begin
  rw [Ioi_eq_finset_subtype],
  simp only [and_imp, imp_self, mem_Ioo, filter_true_of_mem, nat.card_Ioo, card_subtype,
    implies_true_iff],
  have h₁ : 1 ≤ n + 1 - ↑a := by simp [nat.one_le_iff_ne_zero, is_lt],
  rw [nat.sub_eq_iff_eq_add h₁, nat.sub_add_comm (is_le a)],
end

lemma Ioi_eq_filter {n : ℕ} (a : fin (n + 1)) : Ioi a = finset.univ.filter (λ j, a < j) :=
by { ext, simp }

lemma filter_gt_card {n : ℕ} (a : fin n) : (finset.univ.filter (λ j, a < j)).card = n - a - 1 :=
begin
  cases n,
  { simp },
  { rw [← Ioi_eq_filter, card_Ioi, nat.sub.right_comm, nat.succ_sub_succ_eq_sub, nat.sub_zero] }
end

end fin
