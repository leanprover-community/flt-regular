import algebra.associated

universe u

variables {M : Type u} [cancel_comm_monoid_with_zero M]

lemma dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd {p a b : M} {n : ℕ} (hn : 0 < n) (hp : prime p)
  (hpow : p ^ n ∣ a ^ n * b ^ (n - 1)) (hb : ¬ p ^ 2 ∣ b) : p ∣ a :=
begin
  have := dvd_trans ((pow_dvd_pow_iff hp.ne_zero hp.not_unit).2 (nat.succ_le_iff.2 hn)) hpow,
  rw pow_one at this,
  by_contra H,
  have hbdiv := (or_iff_right $ λ h, H $ prime.dvd_of_dvd_pow hp h).1 (hp.dvd_or_dvd this),
  obtain ⟨x, hx⟩ := hp.dvd_of_dvd_pow hbdiv,
  obtain ⟨y, hy⟩ := hpow,
  rw [hx, mul_pow, ← mul_assoc, mul_comm (a ^ n), mul_assoc, ← nat.succ_pred_eq_of_pos hn,
    pow_succ p, mul_comm p, nat.succ_pred_eq_of_pos hn, ← nat.sub_one, mul_assoc,
    mul_eq_mul_left_iff] at hy,
  cases hy with h₁ h₂,
  { apply hb,
    have hdvd := dvd_mul_right p y,
    rw [← h₁] at hdvd,
    obtain ⟨z, hz⟩ := hp.dvd_of_dvd_pow
      ((or_iff_right $ λ h, H $ prime.dvd_of_dvd_pow hp h).1 (hp.dvd_or_dvd hdvd)),
    rw [hz, ← mul_assoc, ← pow_two] at hx,
    rw [hx],
    exact dvd_mul_right _ _ },
  { exfalso,
    exact hp.ne_zero (pow_eq_zero h₂) }
end
