import linear_algebra.matrix.determinant
import ring_theory.trace
import ring_theory.norm
import linear_algebra.vandermonde

import ready_for_mathlib.linear_algebra
import ready_for_mathlib.matrix

universes u v w z

open_locale matrix big_operators

open matrix finite_dimensional fintype polynomial finset

namespace algebra

variables (A : Type u) {B : Type v} (C : Type z) {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B] [comm_ring C] [algebra A C]

section matrix

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`trace_matrix A ι b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
noncomputable
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
  congr, ext x,
  rw [mul_apply, sum_mul],
  congr, ext y,
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

lemma trace_matrix_of_basis [decidable_eq ι] [fintype ι] (b : basis ι A B) :
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
  bijection `e : ι ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presnce of `h : fintype.card ι = finrank A B`, one can take
  `e := equiv_of_card_eq ((alg_hom.card A B C).trans h.symm)`. -/
def embeddings_matrix_reindex (b : ι → B) (e : ι ≃ (B →ₐ[A] C)) :=
  reindex (equiv.refl ι) e.symm (embeddings_matrix A C b)

variable {A}

lemma embeddings_matrix_reindex_eq_vandermonde (pb : power_basis A B)
  (e : fin pb.dim ≃ (B →ₐ[A] C)) : embeddings_matrix_reindex A C pb.basis e =
  (vandermonde (λ i, e i pb.gen))ᵀ :=
by { ext i j, simp [embeddings_matrix_reindex, embeddings_matrix] }

end matrix

section discriminant

section
open_locale classical
/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discriminant A ι b` as the determinant of `trace_matrix A ι b`. -/
noncomputable
def discriminant [fintype ι] (b : ι → B) := (trace_matrix A b).det
end

lemma discriminant_def [decidable_eq ι] [fintype ι] (b : ι → B) :
  discriminant A b = (trace_matrix A b).det := by convert rfl

namespace discriminant

variable [fintype ι]

section basic

lemma zero_of_not_linear_independent [is_domain A] {b : ι → B} (hli : ¬linear_independent A b) :
  discriminant A b = 0 :=
begin
  classical,
  obtain ⟨g, hg, i, hi⟩ := fintype.linear_independent_iff''.1 hli,
  have : (trace_matrix A b).mul_vec g = 0,
  { ext i,
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (((g j) • (b j)) * b i),
    { intro j, simp [mul_comm], },
    simp only [mul_vec, dot_product, trace_matrix_apply, pi.zero_apply, trace_form_apply,
      λ j, this j, ← linear_map.map_sum, ← sum_mul, hg, zero_mul, linear_map.map_zero] },
  by_contra h,
  rw discriminant_def at h,
  simpa [matrix.eq_zero_of_mul_vec_eq_zero h this] using hi,
end

variable {A}

lemma of_matrix_vec_mul [decidable_eq ι] (b : ι → B) (P : matrix ι ι A) :
  discriminant A ((P.map (algebra_map A B)).vec_mul b) = P.det ^ 2 * discriminant A b :=
by rw [discriminant_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discriminant_def, pow_two]


lemma of_matrix_mul_vec [decidable_eq ι] (b : ι → B) (P : matrix ι ι A) :
  discriminant A ((P.map (algebra_map A B)).mul_vec b) = P.det ^ 2 * discriminant A b :=
by rw [discriminant_def, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose,
  mul_comm, ← mul_assoc, discriminant_def, pow_two]

end basic

section field

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E] [algebra L E] [is_scalar_tower K L E]
variables [module.finite K L] [is_separable K L] [is_alg_closed E]
variables (b : ι → L) (pb : power_basis K L)

lemma not_zero_of_linear_independent [nonempty ι]
  (hcard : fintype.card ι = finrank K L) (hli : linear_independent K b) : discriminant K b ≠ 0 :=
begin
  classical,
  have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard,
  rw [discriminant_def, trace_matrix],
  simp_rw [← basis.mk_apply hli this],
  rw [← trace_matrix, trace_matrix_of_basis, ← bilin_form.nondegenerate_iff_det_ne_zero],
  exact trace_form_nondegenerate _ _
end

@[nolint unused_arguments]
lemma _root_.algebra.trace_matrix_eq_embeddings_matrix_mul_trans :
  (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix K E b) ⬝ (embeddings_matrix K E b)ᵀ :=
by { ext i j, simp [trace_eq_sum_embeddings, embeddings_matrix, mul_apply] }

lemma _root_.algebra.trace_matrix_eq_embeddings_matrix_reindex_mul_trans
  (e : ι ≃ (L →ₐ[K] E)) : (trace_matrix K b).map (algebra_map K E) =
  (embeddings_matrix_reindex K E b e) ⬝ (embeddings_matrix_reindex K E b e)ᵀ :=
by rw [trace_matrix_eq_embeddings_matrix_mul_trans, embeddings_matrix_reindex,
  mul_transpose_eq_reindex_mul_reindex_transpose]

lemma eq_det_embeddings_matrix_reindex_pow_two [decidable_eq ι]
  (e : ι ≃ (L →ₐ[K] E)) : algebra_map K E (discriminant K b) =
  (embeddings_matrix_reindex K E b e).det ^ 2 :=
by rw [discriminant_def, ring_hom.map_det, ring_hom.map_matrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans, det_mul, det_transpose, pow_two]

lemma of_power_basis_eq_prod (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discriminant K pb.basis) =
  ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j), (e j pb.gen- (e i pb.gen)) ^ 2 :=
begin
  rw [eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e,
    embeddings_matrix_reindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow],
  congr, ext i,
  rw [← prod_pow]
end

local notation `n` := finrank K L

lemma of_power_basis_eq_norm : discriminant K pb.basis =
  (-1) ^ (n * (n - 1) / 2) *(norm K (aeval pb.gen (minpoly K pb.gen).derivative)) := sorry

end field

end discriminant

end discriminant

end algebra
