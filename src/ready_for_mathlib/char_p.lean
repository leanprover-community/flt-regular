import algebra.char_p.basic
import data.nat.multiplicity

theorem add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute {R : Type*} [semiring R] (p : ℕ)
  [hp : fact p.prime] (x y : R) (h : commute x y) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
begin
  have : p = p - 1 + 1 := (nat.succ_pred_prime (fact.out _)).symm,
  rw [commute.add_pow h, finset.sum_range_succ_comm, tsub_self, pow_zero, nat.choose_self,
    nat.cast_one, mul_one, mul_one, this, finset.sum_range_succ'],
  simp only [this.symm, tsub_zero, mul_one, one_mul, nat.choose_zero_right, nat.cast_one, pow_zero],
  rw add_comm _ (y ^ p),
  simp_rw add_assoc,
  use (finset.range (p - 1)).sum
    (λ (x_1 : ℕ), x ^ (x_1 + 1) * y ^ (p - (x_1 + 1)) * ↑(p.choose (x_1 + 1) / p)),
  rw finset.mul_sum,
  congr' 2,
  apply finset.sum_congr rfl,
  intros i hi,
  rw [finset.mem_range] at hi,
  rw [nat.cast_comm, mul_assoc, mul_assoc, mul_assoc],
  congr,
  norm_cast,
  rw nat.div_mul_cancel,
  exact nat.prime.dvd_choose_self hp.out (nat.succ_ne_zero _) (lt_tsub_iff_right.mp hi),
end

example {R : Type*} [semiring R] (p n : ℕ) [hp : fact p.prime] (x y : R) (h : commute x y) :
  ∃ r : R, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
begin
  have : p ^ n = p ^ n - 1 + 1 := (nat.succ_pred_eq_of_pos (pow_pos hp.out.pos _)).symm,
  rw [commute.add_pow h, finset.sum_range_succ_comm, tsub_self, pow_zero, nat.choose_self,
    nat.cast_one, mul_one, mul_one, this, finset.sum_range_succ'],
  simp only [this.symm, tsub_zero, mul_one, one_mul, nat.choose_zero_right, nat.cast_one, pow_zero],
  rw add_comm _ (y ^ _),
  simp_rw add_assoc,
  use (finset.range (p ^ n - 1)).sum
    (λ (x_1 : ℕ), x ^ (x_1 + 1) * y ^ (p ^ n - (x_1 + 1)) * ↑((p ^ n).choose (x_1 + 1) / p)),
  rw finset.mul_sum,
  congr' 2,
  apply finset.sum_congr rfl,
  intros i hi,
  rw [finset.mem_range] at hi,
  rw [nat.cast_comm, mul_assoc, mul_assoc, mul_assoc],
  congr,
  norm_cast,
  rw nat.div_mul_cancel,
  by_contra habs,
  replace hi : i + 1 < p ^ n,
  { replace hi := nat.add_lt_add_right hi 1,
    rwa [nat.sub_add_cancel (nat.one_le_pow _ _ hp.out.pos)] at hi },
  have H := nat.prime.multiplicity_choose_prime_pow (fact.out _) hi.le (nat.succ_pos _),
  rw [multiplicity.multiplicity_eq_zero.2 habs, zero_add, multiplicity.eq_coe_iff ] at H,
  exact hi.not_le (nat.le_of_dvd (nat.succ_pos i) H.1),
end

theorem add_pow_prime_eq_pow_add_pow_add_prime_mul {R : Type*} [comm_semiring R] (p : ℕ)
  [fact p.prime] (x y : R) : ∃ r : R, (x + y) ^ p = x ^ p + y ^ p + p * r :=
add_pow_prime_eq_pow_add_pow_add_prime_mul_of_commute _ _ _ (commute.all _ _)
