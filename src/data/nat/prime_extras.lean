import data.nat.prime
import data.nat.parity
import tactic
import tactic.by_contra

variables {p : ℕ} (hp : p.prime)
include hp

namespace nat
namespace prime

lemma five_le (h_two : p ≠ 2) (h_three : p ≠ 3) : 5 ≤ p :=
begin
  by_contra' h,
  --I (RB) don't know why this is needed
  --(Eric): `nat.prime` is now defined to be `irreducible`, which is a class
  unfreezingI { revert h_two h_three hp },
  dec_trivial!,
end

lemma odd (h_two : p ≠ 2) : odd p := odd_iff.mpr (or_iff_not_imp_left.mp hp.eq_two_or_odd h_two)

end prime
end nat
