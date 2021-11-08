import data.nat.prime
import data.nat.parity
import tactic

variables {p : ℕ} (hp : p.prime)
include hp

namespace nat
namespace prime

lemma five_le (h_two : p ≠ 2) (h_three : p ≠ 3) : 5 ≤ p :=
begin
  by_contra h,
  push_neg at h,
  interval_cases p,
  exact not_prime_zero hp,
  exact not_prime_one hp,
  contradiction,
  contradiction,
  revert hp,
  norm_num,
end

lemma odd (h_two : p ≠ 2) : odd p := odd_iff.mpr (or_iff_not_imp_left.mp hp.eq_two_or_odd h_two)

end prime
end nat
