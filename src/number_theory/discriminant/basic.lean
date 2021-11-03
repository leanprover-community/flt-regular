import linear_algebra.matrix.determinant
import ring_theory.trace
import ring_theory.norm

import ready_for_mathlib.linear_algebra
import ready_for_mathlib.matrix

universes u v w z

open_locale classical matrix big_operators

noncomputable theory

open matrix finite_dimensional fintype polynomial finset

namespace algebra

variables (A : Type u) {B : Type v} (C : Type z) {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B] [comm_ring C] [algebra A C]

section matrix

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`trace_matrix A ι b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
def trace_matrix (b : ι → B) : matrix ι ι A := (λ i j, trace_form A B (b i) (b j))

@[simp] lemma trace_matrix_apply (b : ι → B) (i j : ι) :
  trace_matrix A b i j = trace_form A B (b i) (b j) := rfl

variable {A}

lemma trace_matrix_of_matrix_vec_mul [fintype ι] (b : ι → B) (P : matrix ι ι A) :
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

lemma trace_matrix_of_matrix_mul_vec [fintype ι] (b : ι → B) (P : matrix ι ι A) :
 trace_matrix A ((P.map (algebra_map A B)).mul_vec b) = P ⬝ (trace_matrix A b) ⬝ Pᵀ :=
begin
  refine add_equiv.injective transpose_add_equiv _,
  rw [transpose_add_equiv_apply, transpose_add_equiv_apply, ← vec_mul_transpose,
    ← transpose_map, trace_matrix_of_matrix_vec_mul, transpose_transpose, transpose_mul,
    transpose_transpose, transpose_mul]
end

lemma trace_matrix_of_basis [fintype ι] (b : basis ι A B) :
  trace_matrix A b = bilin_form.to_matrix b (trace_form A B) :=
begin
  ext i j,
  rw [trace_matrix_apply, trace_form_apply, trace_form_to_matrix]
end

variable (A)

/-- `embeddings_matrix A C b : matrix ι (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `fintype.card ι = finrank A B` and `C` is
  algebraically closed. -/
def embeddings_matrix (b : ι → B) : matrix ι (B →ₐ[A] C) C := (λ i (σ : B →ₐ[A] C), σ (b i))

/-- `embeddings_matrix_reindex A C b e : matrix ι ι C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : ι` given by a
  bijection `e : (B →ₐ[A] C) ≃ ι`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presnce of `h : fintype.card ι = finrank A B`, one can take
  `e := equiv_of_card_eq ((alg_hom.card A B C).trans h.symm)`. -/
def embeddings_matrix_reindex (b : ι → B) (e : (B →ₐ[A] C) ≃ ι) :=
  reindex (equiv.refl ι) e (embeddings_matrix A C b)

end matrix

section discriminant

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

variable {A}

lemma of_matrix_vec_mul (b : ι → B) (P : matrix ι ι A) :
  discriminant A ((P.map (algebra_map A B)).vec_mul b) = P.det ^ 2 * discriminant A b :=
by rw [discriminant, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discriminant, pow_two]

lemma of_matrix_mul_vec (b : ι → B) (P : matrix ι ι A) :
  discriminant A ((P.map (algebra_map A B)).mul_vec b) = P.det ^ 2 * discriminant A b :=
by rw [discriminant, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discriminant, pow_two]

end basic

section field

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E] [algebra L E] [is_scalar_tower K L E]
variables [module.finite K L] [is_separable K L]
variables (b : ι → L) (pb : power_basis K L)

local notation `n` := finrank K L

lemma not_zero_of_linear_independent [nonempty ι] (hcard : fintype.card ι = finrank K L)
  (hli : linear_independent K b) : discriminant K b ≠ 0 :=
begin
  have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard,
  rw [discriminant, trace_matrix],
  simp_rw [← basis.mk_apply hli this],
  rw [← trace_matrix, trace_matrix_of_basis, ← bilin_form.nondegenerate_iff_det_ne_zero],
  exact trace_form_nondegenerate _ _
end

lemma _root_.trace_matrix_eq_embeddings_matrix_mul_trans [is_alg_closed E] :
  (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix K E b) ⬝ (embeddings_matrix K E b)ᵀ :=
begin
  ext i j,
  have h := is_separable.is_integral K (b i * b j),
  rw [map_apply, trace_matrix_apply, trace_form_apply, trace_eq_sum_embeddings E h,
    embeddings_matrix, mul_apply],
  simp
end

lemma _root_.trace_matrix_eq_embeddings_matrix_reindex_mul_trans [is_alg_closed E]
  (e : (L →ₐ[K] E) ≃ ι) : (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix_reindex K E b e) ⬝ (embeddings_matrix_reindex K E b e)ᵀ :=
by rw [trace_matrix_eq_embeddings_matrix_mul_trans, embeddings_matrix_reindex,
  mul_transpose_eq_reindex_mul_reindex_transpose]

lemma eq_det_embeddings_matrix_reindex_pow_two [is_alg_closed E] (e : (L →ₐ[K] E) ≃ ι) :
  algebra_map K E (discriminant K b) = (embeddings_matrix_reindex K E b e).det ^ 2 :=
by rw [discriminant, ring_hom.map_det, ring_hom.map_matrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans K E b e, det_mul, det_transpose, pow_two]

lemma of_power_basis_eq_prod [is_alg_closed E]  [is_separable K L] [finite_dimensional K L] :
  algebra_map K E (discriminant K pb.basis) ^ 2 =
  (univ : finset ((L →ₐ[K] E) × (L →ₐ[K] E))).off_diag.prod
  (λ σ, (σ.1.1 pb.gen - σ.1.2 pb.gen) ^ 2) := sorry

lemma of_power_basis_eq_norm : discriminant K pb.basis =
  (-1) ^ (n * (n - 1) / 2) *(norm K (aeval pb.gen (minpoly K pb.gen).derivative)) := sorry

end field

end discriminant

end discriminant

end algebra
