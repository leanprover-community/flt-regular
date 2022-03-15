import ring_theory.polynomial.cyclotomic.basic

namespace polynomial

lemma cyclotomic_prime_pow_eq_cyclotomic_pow (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)]
  [ring R] [char_p R p] : cyclotomic (p ^ (n + 1)) R = (cyclotomic p R) ^ (p ^ n) :=
begin
  induction n with n hn,
  { simp },
  { rw [pow_add, pow_one, cyclotomic_mul_prime_dvd_eq_pow, hn, ← pow_mul, pow_succ, mul_comm],
    refine ⟨p ^ n, by rw [pow_succ]⟩ }
end

end polynomial
