import linear_algebra.matrix.determinant
import ring_theory.trace

universes u v w

variables (A : Type u) {B : Type v} {ι : Type w} [fintype ι] (b : ι → B)
variables [comm_ring A] [comm_ring B] [algebra A B]

open_locale classical
noncomputable theory

namespace algebra

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`trace_matrix A ι b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
@[nolint unused_arguments]
def trace_matrix : matrix ι ι A := (λ i j, algebra.trace A B (b i * b j))

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discriminant A ι b` as the determinant of `trace_matrix A ι b`. -/
def discriminant := (trace_matrix A b).det

end algebra
