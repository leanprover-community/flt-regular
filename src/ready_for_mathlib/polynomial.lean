import data.polynomial.ring_division

universe u

open_locale polynomial

namespace polynomial

lemma mul_X_pow_injective {R : Type u} [semiring R] (n : ℕ) :
  function.injective (λ P : R[X], X ^ n * P) :=
begin
  intros P Q hPQ,
  simp only at hPQ,
  ext i,
  rw [← coeff_X_pow_mul P n i, hPQ, coeff_X_pow_mul Q n i]
end

lemma mul_X_injective {R : Type u} [semiring R] : function.injective (λ P : R[X], X * P) :=
begin
  intros P Q hPQ,
  simp only at hPQ,
  rw [← pow_one X] at hPQ,
  exact mul_X_pow_injective 1 hPQ
end

end polynomial
