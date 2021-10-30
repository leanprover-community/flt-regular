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
/-- The Sylvester matrix of two polynomials -/
def sylvester_matrix [semiring R] (p q : polynomial R) :
  matrix (fin $ p.nat_degree + q.nat_degree) (fin $ p.nat_degree + q.nat_degree) R :=
λ i j, if (i : ℕ) < q.nat_degree
       then if i ≤ j then p.coeff (j - i) else 0
       else if (i : ℕ) - q.nat_degree ≤ j then q.coeff (j - (i - q.nat_degree)) else 0
example : sylvester_matrix (X : polynomial ℕ) X == ![![0, 0], ![1,1]] :=
begin
  norm_num [sylvester_matrix],
  ext,
  simp,
  intros a h hh, fin_cases h,
  norm_num,
  sorry,
  sorry,
end

example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1,sorry⟩ ⟨1,sorry⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨1,sorry⟩ ⟨0,sorry⟩ = 0:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0,sorry⟩ ⟨1,sorry⟩ = 1:=
by norm_num [sylvester_matrix]
example : (sylvester_matrix (X : polynomial ℕ) X) ⟨0,sorry⟩ ⟨0,sorry⟩ = 0:=
by norm_num [sylvester_matrix]
/-- The resultant of two polynomials -/
noncomputable theory
def resultant [comm_ring R] (p q : polynomial R) : R := det (sylvester_matrix p q)
-- include (-1)^(n(n-1)/2)/a_n part by updating sylvester first col
def discriminant [comm_ring R] (p : polynomial R) : R := det (sylvester_matrix p p.derivative)

-- translation invariance
-- scaling by a^n(n-1)
-- reversal invariance
-- degree preserving ring maps
-- disc prod is prod discs times resultant square

-- does this work without taking n >= 2? be careful with signs
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
