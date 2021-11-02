import linear_algebra.matrix.determinant
import ring_theory.trace
import ring_theory.norm

import ready_for_mathlib.linear_algebra

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

lemma trace_matrix_apply (b : ι → B) (i j : ι) :
  trace_matrix A b i j = trace_form A B (b i) (b j) := rfl

lemma trace_matrix_of_matrix_mul_vec [fintype ι] (b : ι → B) (P : matrix ι ι A) :
 trace_matrix A ((P.map (algebra_map A B)).vec_mul b) = Pᵀ ⬝ (trace_matrix A b) ⬝ P :=
begin
  ext α β,
  rw [trace_matrix_apply, vec_mul, dot_product, vec_mul, dot_product, trace_matrix, mul_apply,
    bilin_form.sum_left, fintype.sum_congr _ _ (λ (i : ι), @bilin_form.sum_right _ _ _ _ _ _ _ _
    (b i * P.map (algebra_map A B) i α) (λ (y : ι), b y * P.map (algebra_map A B) y β)), sum_comm],
  refine sum_congr _ _ (λ x, _),
  rw [mul_apply, sum_mul],
  refine sum_congr _ _ (λ y, _),
  rw [map_apply, trace_form_apply, mul_comm (b y), ← smul_def],
  simp only [id.smul_eq_mul, ring_hom.id_apply, map_apply, transpose_apply, linear_map.map_smulₛₗ,
    trace_form_apply, algebra.smul_mul_assoc],
  rw [mul_comm (b x), ← smul_def],
  ring_nf,
  simp,
end

variable {A}

lemma trace_matrix_of_basis [fintype ι] (b : basis ι A B) :
  trace_matrix A b = bilin_form.to_matrix b (trace_form A B) :=
begin
  ext i j,
  rw [trace_matrix_apply, trace_form_apply, trace_form_to_matrix]
end

variable (A)

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discriminant A ι b` as the determinant of `trace_matrix A ι b`. -/
def discriminant [fintype ι] (b : ι → B) := (trace_matrix A b).det

lemma discriminant_def [fintype ι] (b : ι → B) : discriminant A b = (trace_matrix A b).det := rfl

namespace discriminant

variable [fintype ι]

section basic

lemma zero_of_not_linear_independent [is_domain A] {b : ι → B} (hli : ¬linear_independent A b) :
  discriminant A b = 0 :=
begin
  obtain ⟨g, hg, i, hi⟩ := fintype.linear_independent_iff''.1 hli,
  have : (trace_matrix A b).mul_vec g = 0,
  { ext i,
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (((g j) • (b j)) * b i),
    { intro j, simp [mul_comm], },
    simp only [mul_vec, dot_product, trace_matrix_apply, pi.zero_apply, trace_form_apply,
      λ j, this j, ← linear_map.map_sum, ← sum_mul, hg, zero_mul, linear_map.map_zero] },
  by_contra h,
  simpa [matrix.eq_zero_of_mul_vec_eq_zero h this] using hi
end

lemma of_matrix_vec_mul (b : ι → B) (P : matrix ι ι A) :
  discriminant A ((P.map (algebra_map A B)).vec_mul b) = P.det ^ 2 * discriminant A b :=
by rw [discriminant, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discriminant, pow_two]

end basic

section field

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E] [algebra L E] [is_scalar_tower K L E]
variables [module.finite K L] [is_separable K L] [is_alg_closed E]
variables (b : ι → L) (hcard : fintype.card ι = finrank K L) (pb : power_basis K L)

local notation `n` := finrank K L

include hcard
lemma not_zero_of_linear_independent [nonempty ι] (hli : linear_independent K b) :
  discriminant K b ≠ 0 :=
begin
  have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard,
  rw [discriminant, trace_matrix],
  simp_rw [← basis.mk_apply hli this],
  rw [← trace_matrix, trace_matrix_of_basis, ← bilin_form.nondegenerate_iff_det_ne_zero],
  exact trace_form_nondegenerate _ _
end

variable {L}

--give a name to the matrix first
lemma eq_det_embeddings : algebra_map K E (discriminant K b) =
  (reindex (equiv.refl ι) (equiv_of_card_eq ((alg_hom.card K L E).trans hcard.symm))
  (λ i (σ : L →ₐ[K] E), σ ( b i))).det := sorry

lemma of_power_basis_eq_prod [is_alg_closed E]  [is_separable K L] [finite_dimensional K L] :
  algebra_map K E (discriminant K pb.basis) ^ 2 =
  (univ : finset ((L →ₐ[K] E) × (L →ₐ[K] E))).off_diag.prod
  (λ σ, (σ.1.1 pb.gen - σ.1.2 pb.gen) ^ 2) := sorry

lemma of_power_basis_eq_norm : discriminant K pb.basis =
  (-1) ^ (n * (n - 1) / 2) *(norm K (aeval pb.gen (minpoly K pb.gen).derivative)) := sorry

end field

end discriminant

end algebra
