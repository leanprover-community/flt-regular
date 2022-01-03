import algebra.ne_zero

namespace ne_zero

section nat

variables (R : Type*) [semiring R] {n : ℕ}

lemma ne_nat [ne_zero (n : R)] : n ≠ 0 :=
λ h, by { simpa [h] using (ne_zero.ne (n : R)) }

lemma pos_nat [ne_zero (n : R)] : 0 < n :=
pos_iff_ne_zero.2 $ ne_nat R

end nat

end ne_zero
