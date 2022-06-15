import data.nat.totient
import number_theory.padics.padic_val

universe u

section totient

open nat

localized "notation `φ` := nat.totient" in nat

lemma gcd_self_pow (p n m : ℕ) : (p ^ n).gcd (p ^ m) = p ^ (min n m) :=
begin
  wlog h : n ≤ m,
  rw [min_eq_left h],
  apply gcd_eq_left,
  exact pow_dvd_pow p h,
end

lemma totient_pow_mul_self {p : ℕ} (n m : ℕ) (h : nat.prime p) :
   φ ((p ^ n).gcd (p ^ m)) * φ (p ^ n * p ^ m) = φ (p ^ n) * φ (p ^ m) * (p ^ n).gcd (p ^ m) :=
begin
  wlog hnm : n ≤ m using [n m],
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [nat.gcd_one_left, mul_one, one_mul, pow_zero] },
  rcases m.eq_zero_or_pos with rfl | hm,
  { simp only [mul_one, one_mul, nat.gcd_one_right, totient_one, pow_zero] },
  have h20 : 0 < n + m, by linarith,
  rw [totient_prime_pow h hn, totient_prime_pow h hm, ←pow_add, totient_prime_pow h h20,
      gcd_self_pow, min_eq_left hnm, totient_prime_pow h hn],
  have : p ^ (n + m - 1) * (p - 1) = (p ^ (m - 1) * (p - 1)) * p^n,
  by { have : p^(n+m-1) = p^n * p^(m-1), by {rw nat.add_sub_assoc, apply pow_add, linarith, },
  rw [this, mul_rotate], },
  rw [this, ←mul_assoc],
end

lemma coprime_of_div_pow_factorization {n p : ℕ} (hp : nat.prime p) (hn : n ≠ 0) :
  coprime p (n / p ^ n.factorization p) :=
(or_iff_left (not_dvd_div_pow_factorization hp hn)).mp $ coprime_or_dvd_of_prime hp _

lemma p_val_nat_div_coprime (a p : ℕ) (ha : a ≠ 0 ) (hp : nat.prime p) :
  coprime p (a/ p^(padic_val_nat p a)) :=
begin
  haveI : fact p.prime, exact {out := hp},
  rw padic_val_nat_eq_factorization p a,
  apply nat.coprime_of_div_pow_factorization hp (ha),
end

/-- An induction principle. -/
def strong_sub_induction {P : ℕ → ℕ → Sort u}
  (H : ∀ n m, ((∀ x y, x < n → y < m → P x y) → P n m)) : Π (n m : ℕ), P n m :=
begin
  intros n m,
  apply H _ _,
  induction n,
  { intros x y hx hy, simp only [not_lt_zero'] at hx, cases hx },
  { intros x y H1 H2,
  apply or.by_cases (decidable.lt_or_eq_of_le (le_of_lt_succ H1)),
  refine λ hn, (n_ih _ _ hn H2),
  intro hn,
  rw hn,
  refine H n_n y (λ a b hab hab2, n_ih a b hab (lt_trans hab2 H2)) },
end

lemma totient_mul_gen : ∀ a b: ℕ, φ (a.gcd b) * φ (a * b) = φ a * φ b * (a.gcd b) :=
begin
  apply strong_sub_induction,
  intros n m hxy,
  by_cases hco : coprime n m,
  rw coprime_iff_gcd_eq_one.1 hco,
  simp only [totient_one, one_mul, mul_one, totient_mul hco],
  by_cases g1 : n ≠ 0,
  by_cases g2 : m ≠ 0,
  obtain ⟨q, hq1, hq2⟩ := prime.not_coprime_iff_dvd.1 hco,
  haveI : fact q.prime, exact { out := hq1 },
  have hn1 := padic_val_int_dvd q n,
  have hm1 := padic_val_int_dvd q m,
  norm_cast at *,
  simp only [padic_val_int.of_nat] at *,
  have hn2 := p_val_nat_div_coprime n q g1 hq1,
  have hm2 := p_val_nat_div_coprime m q g2 hq1,
  have hnm2 := coprime.pow_left (padic_val_nat q n + padic_val_nat q m)
    (p_val_nat_div_coprime (n * m) q (mul_ne_zero g1 g2) hq1),
  rw padic_val_nat.mul q g1 g2 at hnm2,
  rw [ (nat.mul_div_cancel' hn1).symm, (nat.mul_div_cancel' hm1).symm],
  let r := padic_val_nat q n,
  let s := padic_val_nat q m,
  have : q ^ r * (n / q ^ r) * (q ^ s * (m / q ^ s)) = q^(r+s) * (n * m / q^(r+s)),
  by { rw [ (nat.mul_div_cancel' hn1), (nat.mul_div_cancel' hm1)],
    apply symm,
    apply nat.mul_div_cancel',
    convert mul_dvd_mul hn1 hm1,
    apply pow_add, },
  simp_rw [this, totient_mul hnm2, totient_mul (coprime.pow_left r hn2),
   totient_mul (coprime.pow_left s hm2), pow_add, (nat.div_mul_div_comm hn1 hm1).symm,
    coprime.gcd_mul _ (coprime.pow_left s hm2), nat.gcd_comm,
    coprime.gcd_mul _ (coprime.pow_left r hn2)],
  have h33 := (coprime_iff_gcd_eq_one.1 (coprime.pow_left r hm2)),
  rw nat.gcd_comm at h33,
  rw h33,
  rw coprime_iff_gcd_eq_one.1 (coprime.pow_left s hn2),
  simp_rw [mul_one, one_mul, (gcd_self_pow q s r), totient_mul (coprime.gcd_right (m/q^s)
    ((coprime.pow_left (min s r) hn2)))],
  have i1 : n/q^r < n, by { apply (nat.div_lt_self (nat.pos_of_ne_zero g1)),
    rw ←(one_pow (0 : ℕ)),
    have hr : 0 < r, by { have := (one_le_padic_val_nat_of_dvd (nat.pos_of_ne_zero g1) hq2.1),
      linarith},
    apply pow_lt_pow_of_lt_right (prime.one_lt hq1) hr },
  have i2 : m/q^s < m, by { apply (nat.div_lt_self (nat.pos_of_ne_zero g2)),
    rw ←(one_pow (0 : ℕ)),
    have hs : 0 < s, by { have := (one_le_padic_val_nat_of_dvd (nat.pos_of_ne_zero g2) hq2.2),
      linarith},
    apply pow_lt_pow_of_lt_right (prime.one_lt hq1) hs, },
  have V := congr (congr_arg has_mul.mul (hxy (n/q^r) (m/q^s) i1 i2))
    (totient_pow_mul_self r s hq1),
  rw [←(gcd_self_pow q s r), ←mul_assoc],
  have st1 : ∀ (a b c d : ℕ), a * b * c * d = b * d * a * c, by { intros a b c d, ring },
  have st2 : ∀ (a b c d e f : ℕ), a * b * c * d * e * f = b * d * f * a * c * e,
    by { intros a b c d e f, ring },
  simp_rw [← mul_assoc] at *,
  have st3 : (q^r).gcd (q^s) = (q^s).gcd (q^r), by { apply nat.gcd_comm },
  rw [st1, st2, nat.gcd_comm, ←st3],
  exact V,
  { simp only [not_not.1 g2, mul_zero, totient_zero, zero_mul] },
  { simp only [not_not.1 g1, zero_mul, totient_zero, mul_zero] },
end

lemma totient_super_multiplicative (a b : ℕ) : a.totient * b.totient ≤ (a * b).totient :=
begin
  let d := a.gcd b,
  by_cases d ≠ 0,
  { have := totient_mul_gen a b,
  simp only [ne.def, nat.gcd_eq_zero_iff, not_and] at *,
  have hd : 0 < d.totient, by { apply nat.totient_pos,
    simp_rw d,
    by_cases ha : a = 0,
    apply gcd_pos_of_pos_right _ (nat.pos_of_ne_zero (h ha)),
    apply gcd_pos_of_pos_left _(nat.pos_of_ne_zero ha), },
  by_cases HA : a ≠ 0,
  by_cases HB : b ≠ 0,
  have hr : φ (d) * (φ (a) * φ (b)) ≤ φ (d) * φ (a * b) ↔ (φ (a) * φ (b)) ≤ φ (a * b),
  by { apply mul_le_mul_left hd, },
  rw [←hr, this, mul_comm],
  exact mul_le_mul_left' (nat.totient_le d) (φ a * φ b),
  rw (not_not.1 HB),
   simp only [totient_zero, mul_zero],
  rw (not_not.1 HA),
   simp only [totient_zero, zero_mul], },
   simp only [nat.gcd_eq_zero_iff, not_not] at h,
   simp only [h.1, totient_zero, zero_mul],
end

end totient
