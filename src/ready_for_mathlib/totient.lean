import data.nat.totient
import ready_for_mathlib.multiplicity

namespace nat

lemma totient_mul_prime_div {p n : ℕ} (hp : p.prime) (h : p ∣ n) :
  (p * n).totient = p * n.totient :=
begin
  by_cases hzero : n = 0,
  { simp [hzero] },
  { have hfin := (multiplicity.finite_nat_iff.2 ⟨hp.ne_one, zero_lt_iff.2 hzero⟩),
    have h0 : 0 < (multiplicity p n).get hfin := multiplicity.pos_of_dvd hfin h,
    obtain ⟨m, hm, hndiv⟩ := multiplicity.eq_pow_mul_not_dvd hfin,
    rw [hm, ← mul_assoc, ← pow_succ, nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd
      hndiv)), nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd hndiv)), ← mul_assoc],
    congr,
    rw [ ← succ_pred_eq_of_pos h0, totient_prime_pow_succ hp, totient_prime_pow_succ hp,
      succ_pred_eq_of_pos h0, ← mul_assoc p, ← pow_succ, ← succ_pred_eq_of_pos h0, nat.pred_succ] }
end

end nat
