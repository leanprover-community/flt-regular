import data.polynomial.eval

universe u

open_locale polynomial

namespace polynomial

lemma eval_geom_sum' {R} [comm_semiring R] {n : ℕ} {x : R} {P : R[X]} :
  eval x (geom_sum P n) = geom_sum (eval x P) n :=
by simp [geom_sum_def, eval_finset_sum]

end polynomial
