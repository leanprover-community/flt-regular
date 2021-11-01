import linear_algebra.matrix.determinant
import ring_theory.trace
import ring_theory.norm

universes u v w z

variables (A : Type u) {B : Type v} {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B]

open_locale classical matrix big_operators

noncomputable theory

open matrix finite_dimensional fintype polynomial finset

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

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E] [algebra L E] [is_scalar_tower K L E] (b : ι → L)
variables (hcard : fintype.card ι = finrank K L) (pb : power_basis K L)
variables (hfin : module.finite K L) (hsplits : splits (algebra_map K E) (minpoly K pb.gen))

local notation `n` := finrank K L

--I don't think we need (and can) prove a more general result
lemma linear_independent_of_not_zero [is_separable K L] (h : discriminant K b ≠ 0) :
  linear_independent K b := sorry

variable {K}

--TODO state this first of all for matrix.trace
--is using matrix.col and unit.star the best way to do this?
lemma of_matrix_mul (P : matrix ι ι K) : discriminant K
  (λ i, (P.map (algebra_map K L) ⬝ (matrix.col b)) i unit.star) = P.det ^ 2 * discriminant K b :=
sorry

variables (K L)

--this is probably already in mathlib in some form
instance : fintype (L →ₐ[K] E) := sorry

--this is probably already in mathlib in some form
lemma card_embeddings_eq_finrank : fintype.card (L →ₐ[K] E) = n := sorry

variable {L}

--give a name to the matrix first
lemma eq_det_embeddings : algebra_map K E (discriminant K b) = (reindex (equiv.refl ι)
  (equiv_of_card_eq ((card_embeddings_eq_finrank K L E).trans hcard.symm))
  (λ i (σ : L →ₐ[K] E), σ ( b i))).det := sorry

lemma of_power_basis_eq_prod : algebra_map K E (discriminant K pb.basis) ^ 2 =
  (univ : finset ((L →ₐ[K] E) × (L →ₐ[K] E))).off_diag.prod
  (λ σ, (σ.1.1 pb.gen - σ.1.2 pb.gen) ^ 2) := sorry

lemma of_power_basis_eq_norm : discriminant K pb.basis =
  (-1) ^ (n * (n - 1) / 2) *(norm K (aeval pb.gen (minpoly K pb.gen).derivative)) := sorry

end field

end discriminant

end algebra
