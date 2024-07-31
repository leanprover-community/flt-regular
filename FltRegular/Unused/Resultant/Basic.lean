import Mathlib.FieldTheory.Galois
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Module.Basic

section resultant

variable {R : Type _}

open Matrix Polynomial

open scoped Polynomial

-- TODO redefine this in terms of a matrix.from_column_blocks, or maybe dont as types of
-- indices will be weird
noncomputable section

/-- The Sylvester matrix of two polynomials -/
def sylvesterMatrix [Semiring R] (p q : Polynomial R) :
    Matrix (Fin <| p.natDegree + q.natDegree) (Fin <| p.natDegree + q.natDegree) R := fun i j =>
  if (i : ℕ) < q.natDegree then (p * X ^ (i : ℕ)).coeff j
  else (q * X ^ (i - q.natDegree : ℕ)).coeff j

-- example : sylvester_matrix (X : polynomial ℕ) X = ![![0, 0], ![1,1]] :=
-- begin
--   norm_num [sylvester_matrix],
--   ext,
--   simp,
--   intros a h hh, fin_cases h,
--   norm_num [hh],
--   rw hh,
--   admit,
--   admit,
-- end
example : (sylvesterMatrix (X : Polynomial ℕ) X) ⟨1, by simp⟩ ⟨1, by simp⟩ = 1 := by
  norm_num [sylvesterMatrix]

example : (sylvesterMatrix (X : Polynomial ℕ) X) ⟨1, by simp⟩ ⟨0, by simp⟩ = 0 := by
  norm_num [sylvesterMatrix]

example : (sylvesterMatrix (X : Polynomial ℕ) X) ⟨0, by simp⟩ ⟨1, by simp⟩ = 1 := by
  norm_num [sylvesterMatrix]

example : (sylvesterMatrix (X : Polynomial ℕ) X) ⟨0, by simp⟩ ⟨0, by simp⟩ = 0 := by
  norm_num [sylvesterMatrix]

/-- The resultant of two polynomials -/
def resultant [CommRing R] (p q : Polynomial R) : R :=
  det (sylvesterMatrix p q)

-- include (-1)^(n(n-1)/2)/a_n part by updating sylvester first col
/-- The discriminant of a polynomial defined as the resultant of p and its derivative -/
def discriminant' [CommRing R] (p : Polynomial R) : R :=
  resultant p p.derivative

-- translation invariance
-- scaling by a^n(n-1)
-- reversal invariance
-- degree preserving ring maps
-- disc prod is prod discs times resultant square
theorem discriminant'_c_mul_x_add_c [CommRing R] {b c : R} (h : b ≠ 0) :
    discriminant' (C b * X + C c) = b :=
  by
  --big note: this used to be `discriminat' = 1`!!
  have : (C b * X + C c).natDegree = 1 :=
    by
    apply nat_degree_eq_of_degree_eq_some
    simp only [degree_add_C, degree_C_mul_X h, ← WithBot.coe_zero, ← WithBot.coe_one,
      WithBot.coe_lt_coe, zero_lt_one]
  -- I'm squeezing the simps to make working on the file faster, if later someone wants to put
  -- back the original one: `simp only [discriminant', resultant, sylvester_matrix]`.
  simp only [discriminant', resultant, sylvesterMatrix, tsub_zero, add_zero, derivative_X, mul_one,
    derivative_add, derivative_mul, coeff_C_mul, MulZeroClass.zero_mul, if_false, nat_degree_C,
    zero_add, derivative_C, not_lt_zero']
  convert_to (det fun i j : Fin 1 => b * (X ^ ↑i).coeff ↑j) = b
  · congr; any_goals rw [this, nat_degree_C, add_zero]
  norm_num

-- does this work without taking n ≥ 2? be careful with signs
-- Eric: doesn't work for n=0 or n=1:
/-
  (with n = 0 substituted)
  simp only [mul_one, nat.cast_zero, add_left_neg, pow_zero],
  rw [add_right_comm, ←C_add, add_comm, discriminant'_C_mul_X_add_C]

  (with n=1 substituted)
  simp only [neg_mul_eq_neg_mul_symm, one_mul, pow_one, nat.cast_one, pow_zero],
  rw [←add_mul, ←C_add, discriminant'_C_mul_X_add_C]
-/
theorem discriminant'_mul_x_pow_add_c_mul_x_add_c [CommRing R] {a b c : R} (ha : a ≠ 0) :
    ∀ {n : ℕ},
      2 ≤ n →
        discriminant' (C a * (X : Polynomial R) ^ n + C b * X + C c) =
          -(n - 1) ^ (n - 1) * b ^ n + n ^ n * a ^ (n - 1) * (-c) ^ (n - 1)
  | 0, hn => (hn.not_lt zero_lt_two).rec _
  | 1, hn => (hn.not_lt one_lt_two).rec _
  | n + 2, _ => by sorry

-- this should give quadratic as b^2 - 4ac and depressed cubic as
-- -4ac^3 - 27 a^2d^2 = -(n-1)^(n-1)a c ^n - n^n a^(n-1) b^(n-1)
-- example of computing this thing
example : discriminant' ((X : ℚ[X]) ^ 5 + -X + -1) = 3381 :=
  by
  have := @discriminant'_mul_x_pow_add_c_mul_x_add_c _ _ (1 : ℚ) (-1) (-1) one_ne_zero 5
  norm_num at this 
  exact this

end resultant

