import ready_for_mathlib.is_integral
import ring_theory.discriminant
import field_theory.adjoin
import ready_for_mathlib.intermediate_field
import ring_theory.integrally_closed

namespace algebra

open matrix intermediate_field finite_dimensional power_basis

open_locale big_operators

variables {R K L ι : Type*} [comm_ring R] [field K] [field L] [fintype ι]
variables [algebra R K] [algebra K L] [algebra R L][is_scalar_tower R K L]

local notation `is_integral` := _root_.is_integral

lemma discr_is_integral [finite_dimensional K L] {b : ι → L} (h : ∀ i, is_integral R (b i)) :
  is_integral R (discr K b) :=
begin
  classical,
  rw [discr_def],
  exact det_is_integral (λ i j, is_integral_trace (is_integral_mul (h i) (h j)))
end

lemma adjoin_le_integral_closure {x : L} (hx : is_integral R x) :
  adjoin R {x} ≤ integral_closure R L :=
begin
  rw [adjoin_le_iff],
  simp only [set_like.mem_coe, set.singleton_subset_iff],
  exact hx
end

variable (K)

lemma discr_is_unit_of_basis [finite_dimensional K L] [is_separable K L] (b : basis ι K L) :
  is_unit (discr K b) :=
is_unit.mk0 _ (discr_not_zero_of_basis _ _)

variable {K}

lemma trace_matrix_of_basis_mul_vec (b : basis ι K L) (z : L) :
  (trace_matrix K b).mul_vec (b.equiv_fun z) = (λ i, trace K L (z * (b i))) :=
begin
  ext i,
  rw [← col_apply ((trace_matrix K b).mul_vec (b.equiv_fun z)) i unit.star, col_mul_vec, mul_apply,
    trace_matrix_def],
  simp only [col_apply, trace_form_apply],
  conv_lhs
  { congr, skip, funext,
    rw [mul_comm _ (b.equiv_fun z _), ← smul_eq_mul, ← linear_map.map_smul] },
    rw [← linear_map.map_sum],
    congr,
    conv_lhs
    { congr, skip, funext,
      rw [← mul_smul_comm] },
    rw [← finset.mul_sum, mul_comm z],
    congr,
    rw [b.sum_equiv_fun ]
end

lemma discr_mul_is_integral_mem_adjoin [is_domain R] [is_separable K L] [module.finite K L]
  [is_integrally_closed R] [is_fraction_ring R K] {B : power_basis K L}
  (hint : is_integral R B.gen) {z : L} (hz : is_integral R z) :
  (discr K B.basis) • z ∈ adjoin R ({B.gen} : set L) :=
begin
  have hinv : is_unit (trace_matrix K B.basis).det :=
    by simpa [← discr_def] using discr_is_unit_of_basis _ B.basis,

  have H : (trace_matrix K B.basis).det • (trace_matrix K B.basis).mul_vec (B.basis.equiv_fun z) =
    (trace_matrix K B.basis).det • (λ i, trace K L (z * B.basis i)),
  { congr, exact trace_matrix_of_basis_mul_vec _ _ },
  have cramer := mul_vec_cramer (trace_matrix K B.basis) (λ i, trace K L (z * B.basis i)),

  suffices : ∀ i, ((trace_matrix K B.basis).det • (B.basis.equiv_fun z)) i ∈ (⊥ : subalgebra R K),
  { rw [← B.basis.sum_repr z, finset.smul_sum],
    refine subalgebra.sum_mem _ (λ i hi, _),
    replace this := this i,
    rw [← discr_def, pi.smul_apply, mem_bot] at this,
    obtain ⟨r, hr⟩ := this,
    rw [basis.equiv_fun_apply] at hr,
    rw [← smul_assoc, ← hr, algebra_map_smul],
    refine subalgebra.smul_mem _ _ _,
    rw [B.basis_eq_pow i],
    refine subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton _)) _},
  intro i,
  rw [← H, ← mul_vec_smul] at cramer,
  replace cramer := congr_arg (mul_vec (trace_matrix K B.basis)⁻¹) cramer,
  rw [mul_vec_mul_vec, nonsing_inv_mul _ hinv, mul_vec_mul_vec, nonsing_inv_mul _ hinv,
    one_mul_vec, one_mul_vec] at cramer,
  rw [← congr_fun cramer i, cramer_apply, det_apply],
  refine subalgebra.sum_mem _ (λ σ _, subalgebra.zsmul_mem _ (subalgebra.prod_mem _ (λ j _, _)) _),
  by_cases hji : j = i,
  { simp only [update_column_apply, hji, eq_self_iff_true, power_basis.coe_basis],
    exact mem_bot.2 (is_integrally_closed.is_integral_iff.1 $ is_integral_trace $
      is_integral_mul hz $ is_integral.pow hint _) },
  { simp only [update_column_apply, hji, power_basis.coe_basis],
    exact mem_bot.2 (is_integrally_closed.is_integral_iff.1 $ is_integral_trace
      $ is_integral_mul (is_integral.pow hint _) (is_integral.pow hint _)) }
end

end algebra
