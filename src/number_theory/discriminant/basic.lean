import linear_algebra.matrix.determinant
import ring_theory.trace

universes u v w

variables (R : Type u) {S : Type v} {ι : Type w} [fintype ι] (b : ι → S)

open_locale classical
noncomputable theory

namespace algebra

variables [comm_ring R] [comm_ring S] [algebra R S]

def trace_matrix : matrix ι ι R := (λ i j, algebra.trace R S (b i * b j))

def discriminant := (trace_matrix R b).det

end algebra
