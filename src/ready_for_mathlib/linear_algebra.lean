import linear_algebra.linear_independent
import linear_algebra.bilinear_form
import linear_algebra.matrix.to_linear_equiv

universes u v w

open_locale big_operators

lemma fintype.linear_independent_iff'' {ι : Type u} {R : Type v} {M : Type w} {v : ι → M}
  [semiring R] [add_comm_monoid M] [module R M] [fintype ι] :
  ¬linear_independent R v ↔ ∃ g : ι → R, (∑ i, g i • v i) = 0 ∧ (∃ i, g i ≠ 0) :=
by simpa using (not_iff_not.2 fintype.linear_independent_iff)

lemma matrix.nondegenerate_iff_to_bilin' {R : Type u} [comm_ring R] {ι : Type v} [decidable_eq ι]
  [fintype ι] {M : matrix ι ι R} : M.nondegenerate ↔ (matrix.to_bilin' M).nondegenerate :=
begin
  refine ⟨λ h, matrix.nondegenerate.to_bilin' h, λ h, λ v hv, _⟩,
  replace h := h v,
  simp_rw [matrix.to_bilin'_apply'] at h,
  exact h hv
end

lemma to_bilin.nondegenerate_iff_det_ne_zero' {R : Type u} [comm_ring R] [is_domain R] {ι : Type v}
  [decidable_eq ι] [fintype ι] {M : matrix ι ι R} : (matrix.to_bilin' M).nondegenerate ↔ M.det ≠ 0 :=
begin
  refine ⟨λ h, _, λ h, bilin_form.nondegenerate_of_det_ne_zero' _ h⟩,
  rw [← matrix.nondegenerate_iff_det_ne_zero],
  exact matrix.nondegenerate_iff_to_bilin'.2 h,
end

lemma bilin_form.nondegenerate_iff_det_ne_zero {R : Type u} [comm_ring R] [is_domain R] {ι : Type v}
  [decidable_eq ι] [fintype ι] {M : Type w} [add_comm_group M] [module R M] (B : bilin_form R M)
  (b : basis ι R M) : B.nondegenerate ↔ ((bilin_form.to_matrix b) B).det ≠ 0 :=
begin
  refine ⟨λ h, to_bilin.nondegenerate_iff_det_ne_zero'.1 (λ v hv, _),
    λ h, bilin_form.nondegenerate_of_det_ne_zero _ _ h⟩,
  rw [← linear_equiv.map_eq_zero_iff b.equiv_fun.symm],
  refine h (b.equiv_fun.symm v) (λ m, _),
  replace hv := hv (b.equiv_fun m),
  simp_rw [matrix.to_bilin'_apply, basis.equiv_fun_apply, bilin_form.to_matrix_apply] at hv,
  rw [← basis.sum_equiv_fun b m],
  rw [finset.sum_comm] at hv,
  simp [mul_comm, hv]
end
