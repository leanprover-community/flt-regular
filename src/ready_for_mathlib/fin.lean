import data.fin.interval

namespace fin

open finset

open_locale big_operators

lemma Ioi_eq_filter {n : ℕ} (a : fin (n + 1)) : Ioi a = finset.univ.filter (λ j, a < j) :=
by { ext, simp }

lemma filter_lt_card {n : ℕ} (a : fin n) : (finset.univ.filter (λ j, a < j)).card = n - a - 1 :=
begin
  cases n,
  { simp },
  { rw [← Ioi_eq_filter, card_Ioi, nat.sub.right_comm, nat.succ_sub_succ_eq_sub, nat.sub_zero] }
end

end fin
