import ready_for_mathlib.is_integral
import ring_theory.discriminant
import field_theory.adjoin
import ready_for_mathlib.intermediate_field
import ring_theory.integrally_closed

namespace algebra

open matrix intermediate_field finite_dimensional

open_locale big_operators

variables {R K L ι : Type*} [comm_ring R] [field K] [field L] [fintype ι]
variables [algebra R K] [algebra K L] [algebra R L][is_scalar_tower R K L]

lemma discr_is_integral [finite_dimensional K L] {b : ι → L} (h : ∀ i, _root_.is_integral R (b i)) :
  _root_.is_integral R (discr K b) :=
begin
  classical,
  rw [discr_def],
  exact det_is_integral (λ i j, is_integral_trace (is_integral_mul (h i) (h j)))
end

lemma adjoin_le_integral_closure {x : L} (hx : _root_.is_integral R x) :
  adjoin R {x} ≤ integral_closure R L :=
begin
  rw [adjoin_le_iff],
  simp only [set_like.mem_coe, set.singleton_subset_iff],
  exact hx
end

variable (K)

lemma discr_not_zero_of_linear_independent' [module.finite K L] [is_separable K L] (b : ι → L)
  (hcard : fintype.card ι = finrank K L) (hli : linear_independent K b) : discr K b ≠ 0 :=
begin
  by_cases h : nonempty ι,
  { classical,
    have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard,
    rw [discr_def, trace_matrix_def],
    simp_rw [← basis.mk_apply hli this],
    rw [← trace_matrix_def, trace_matrix_of_basis, ← bilin_form.nondegenerate_iff_det_ne_zero],
    exact trace_form_nondegenerate _ _  },
  letI := not_nonempty_iff.1 h,
  simp [discr],
end

variable {K}

lemma discr_mul_is_integral_mem_adjoin [is_domain R] [is_integrally_closed R]
  [is_fraction_ring R K] [is_separable K L]
  {α : L} (hα : _root_.is_integral R α) {z : K⟮α⟯}
  (hz : _root_.is_integral R z) :
  ((discr K (adjoin.power_basis
  (is_integral_of_is_scalar_tower α hα : _root_.is_integral K α)).basis) • z : L) ∈
  adjoin R ({α} : set L) :=
begin
  let pb := adjoin.power_basis (is_integral_of_is_scalar_tower α hα : _root_.is_integral K α),
  set x := (pb.basis).equiv_fun z with hx,
  set b : fin pb.dim → K := λ i, trace K K⟮α⟯ (z * (pb.basis i)) with hb,

  letI := power_basis.finite_dimensional pb,

  suffices : ∀ i, ((trace_matrix K pb.basis).det • x) i ∈ (⊥ : subalgebra R K),
  { rw [← basis.sum_repr pb.basis z, coe_sum, finset.smul_sum],
    refine subalgebra.sum_mem _ (λ i hi, _),
    replace this := this i,
    rw [← discr_def, pi.smul_apply, mem_bot] at this,
    obtain ⟨r, hr⟩ := this,
    rw [hx, basis.equiv_fun_apply] at hr,
    rw [coe_smul, ← smul_assoc, ← hr, algebra_map_smul],
    refine subalgebra.smul_mem _ _ _,
    rw [pb.basis_eq_pow i, intermediate_field.adjoin.power_basis_gen, coe_pow],
    refine subalgebra.pow_mem _ (subset_adjoin (by simpa)) _ },

  have hinv : is_unit (trace_matrix K pb.basis).det,
  { refine is_unit.mk0 _ _,
    rw [← discr_def],
    letI : is_separable K ↥K⟮α⟯ := is_separable_tower_bot_of_is_separable _ _ L,
    refine discr_not_zero_of_linear_independent' _ _ _ (pb.basis.linear_independent),
    rw [fintype.card_fin],
    exact (power_basis.finrank pb).symm },

  have H : (trace_matrix K pb.basis).det • (trace_matrix K pb.basis).mul_vec x =
    (trace_matrix K pb.basis).det • b,
  { congr, ext i,
    rw [← col_apply ((trace_matrix K pb.basis).mul_vec x) i unit.star, col_mul_vec, mul_apply,
      power_basis.coe_basis, trace_matrix_def, hb],
    simp only [col_apply, trace_form_apply],
    conv_lhs
    { congr, skip, funext,
      rw [mul_comm _ (x j), ← smul_eq_mul, ← linear_map.map_smul] },
    rw [← linear_map.map_sum],
    congr,
    conv_lhs
    { congr, skip, funext,
      rw [← mul_smul_comm] },
    rw [← finset.mul_sum, mul_comm z, power_basis.coe_basis],
    congr,
    rw [← basis.sum_repr pb.basis z],
    congr, ext j, congr,
    exact (pb.basis_eq_pow j).symm },
  have cramer := mul_vec_cramer (trace_matrix K pb.basis) b,
  rw [← H, ← mul_vec_smul] at cramer,
  replace cramer := congr_arg (mul_vec (trace_matrix K pb.basis)⁻¹) cramer,
  rw [mul_vec_mul_vec, nonsing_inv_mul _ hinv, mul_vec_mul_vec, nonsing_inv_mul _ hinv,
    one_mul_vec, one_mul_vec] at cramer,

  intro i,
  rw [← congr_fun cramer i, cramer_apply, det_apply],
  refine subalgebra.sum_mem _ (λ σ hσ, subalgebra.zsmul_mem _ (subalgebra.prod_mem _ (λ j hj, _)) _),
  rw [update_column_apply],
  by_cases hji : j = i,
  { simp only [hji, hb, if_true, eq_self_iff_true],
    have : _root_.is_integral R (z * (pb.basis) (σ i)),
    { rw [pb.basis_eq_pow],
      exact is_integral_mul hz (is_integral.pow (coe_is_integral hα) _) },
    exact mem_bot.2 (is_integrally_closed.is_integral_iff.1 (is_integral_trace this)) },
  { simp only [hji, if_false, trace_form_apply, trace_matrix],
    have : _root_.is_integral R ((pb.basis) (σ j) * (pb.basis) j),
    { rw [pb.basis_eq_pow, pb.basis_eq_pow],
      exact is_integral_mul (is_integral.pow (coe_is_integral hα) _)
        ((is_integral.pow (coe_is_integral hα) _)) },
    exact mem_bot.2 (is_integrally_closed.is_integral_iff.1 (is_integral_trace this)) }
end

end algebra
