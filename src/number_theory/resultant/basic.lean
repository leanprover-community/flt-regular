import field_theory.galois
import linear_algebra.determinant
import data.polynomial.derivative
import data.matrix.notation
import data.multiset
import algebra.module.basic
section resultant
variables {R : Type*}
open matrix polynomial
-- TODO redefine this in terms of a matrix.from_column_blocks, or maybe dont as types of
-- indices will be weird
noncomputable theory
/-- The Sylvester matrix of two polynomials -/
def sylvester_matrix [semiring R] (p q : polynomial R) :
  matrix (fin $ p.nat_degree + q.nat_degree) (fin $ p.nat_degree + q.nat_degree) R :=
λ i j, if (i : ℕ) < q.nat_degree
       then (p * X ^ (i : ℕ)).coeff j
       else (q * X ^ (i - q.nat_degree : ℕ)).coeff j
-- example : sylvester_matrix (X : polynomial ℕ) X = ![![0, 0], ![1,1]] :=
-- begin
--   norm_num [sylvester_matrix],
--   ext,
--   simp,
--   intros a h hh, fin_cases h,
--   norm_num [hh],
--   rw hh,
--   sorry,
--   sorry,
-- end

example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1, by simp⟩ ⟨1, by simp⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1, by simp⟩ ⟨0, by simp⟩ = 0:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0, by simp⟩ ⟨1, by simp⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0, by simp⟩ ⟨0, by simp⟩ = 0:=
by norm_num [sylvester_matrix]

/-- The resultant of two polynomials -/
def resultant [comm_ring R] (p q : polynomial R) : R := det (sylvester_matrix p q)
-- include (-1)^(n(n-1)/2)/a_n part by updating sylvester first col
def discriminant [comm_ring R] (p : polynomial R) : R := det (sylvester_matrix p p.derivative)

-- translation invariance
-- scaling by a^n(n-1)
-- reversal invariance
-- degree preserving ring maps
-- disc prod is prod discs times resultant square


lemma degree_C_mul_X [comm_ring R] {a : R} (h : a ≠ 0) : degree (C a * X) = 1 :=
begin
  rw degree_eq_nat_degree,
  rw nat_degree_C_mul_X _ h,
  norm_cast,
  -- simp,
  sorry
end

-- does this work without taking n >= 2? be careful with signs
lemma discriminant_C_mul_X_add_C [comm_ring R] {n : ℕ} {b c : R} (h : b ≠ 0) :
  discriminant (C b * X + C c) = 1 :=
begin
  have : (C b * X + C c).nat_degree = 1,
  { apply nat_degree_eq_of_degree_eq_some,
    have := degree_C_mul_X h,
    rw degree_add_C;
    simp [h, this],
    sorry, },
  norm_num [discriminant, sylvester_matrix, this],
  rw det_apply,
  sorry,
end

lemma discriminant_mul_X_pow_add_C_mul_X_add_C [comm_ring R] {n : ℕ} {a b c : R} (h : a ≠ 0) :
  discriminant (C a * (X : polynomial R)^n + C b * X + C c) =
    -(n - 1)^(n-1) * b^n + n^n * a^(n-1) * (-c)^(n-1) :=
begin
  by_cases hn0 : n = 0,
  norm_num [hn0],
  norm_num [discriminant, sylvester_matrix],
  sorry,
  sorry,
end
-- this should give quadratic as b^2 - 4ac and depressed cubic as
-- -4ac^3 - 27 a^2d^2 = -(n-1)^(n-1)a c ^n - n^n a^(n-1) b^(n-1)

-- example of computing this thing
example : false :=
begin
  have := @discriminant_mul_X_pow_add_C_mul_X_add_C _ _ 5 (1 : ℚ) (-1) (-1),
  norm_num at this,
  sorry,
end
end resultant
