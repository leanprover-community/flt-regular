import linear_algebra.matrix.determinant
import ring_theory.trace

universes u v w

variables (A : Type u) {B : Type v} {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B]

open_locale classical matrix
noncomputable theory

namespace algebra

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`trace_matrix A ι b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
def trace_matrix (b : ι → B) : matrix ι ι A := (λ i j, trace_form A B (b i) (b j))

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discriminant A ι b` as the determinant of `trace_matrix A ι b`. -/
def discriminant [fintype ι] (b : ι → B) := (trace_matrix A b).det

lemma discriminant_def [fintype ι] (b : ι → B) : discriminant A b = (trace_matrix A b).det := rfl

namespace discriminant

variable [fintype ι]

section basic

lemma zero_of_not_linear_independent (b : ι → B) (hli : ¬linear_independent A b) :
  discriminant A b = 0 := sorry

--discriminant of zero family and similar stuff

end basic

section field

variables (K : Type u) (L : Type v) [field K] [field L] [algebra K L] (b : ι → L)
variables (hfin : module.finite K L) (hcard : fintype.card ι = finite_dimensional.finrank K L)

--I don't think we need (and can) prove a more general result
lemma linear_independent_of_not_zero [is_separable K L] (h : discriminant K b ≠ 0) :
  linear_independent K b := sorry

--TODO state this first of all for matrix.trace
--is using matrix.col and unit.star the best way to do this?
lemma of_matrix_mul (P : matrix ι ι K) : discriminant K
  (λ i, (P.map (algebra_map K L) ⬝ (matrix.col b)) i unit.star) = P.det ^ 2 * discriminant K b :=
sorry

end field

end discriminant

end algebra
