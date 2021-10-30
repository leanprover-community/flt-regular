import linear_algebra.matrix.determinant
import ring_theory.trace

universes u v w

variables (A : Type u) {B : Type v} {ι : Type w} (b : ι → B)
variables [comm_ring A] [comm_ring B] [algebra A B]

open_locale classical
noncomputable theory

namespace algebra

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`trace_matrix A ι b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
def trace_matrix : matrix ι ι A := (λ i j, algebra.trace A B (b i * b j))

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discriminant A ι b` as the determinant of `trace_matrix A ι b`. -/
def discriminant [fintype ι] := (trace_matrix A b).det

lemma discriminant_def [fintype ι] : discriminant A b = (trace_matrix A b).det := rfl

namespace discriminant

variable [fintype ι]

section basic

--discriminant of zero family and similar stuff

end basic

section

lemma zero_of_not_linear_independent (hli : ¬linear_independent A b) : discriminant A b = 0 :=
sorry

--State the converse with the needed assumptions, fields should be enough for us

end

end discriminant

end algebra
