import linear_algebra.matrix.determinant
import ring_theory.trace
import ring_theory.norm
import linear_algebra.vandermonde
import ring_theory.discriminant

import ready_for_mathlib.linear_algebra
import ready_for_mathlib.matrix
import ready_for_mathlib.fin

universes u v w z

open_locale matrix big_operators

namespace algebra

open matrix finite_dimensional fintype polynomial finset

variables (A : Type u) {B : Type v} (C : Type z) {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B] [comm_ring C] [algebra A C]

section field

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E] [algebra L E]
variables [module.finite K L] [is_separable K L] [is_alg_closed E]
variables (b : ι → L) (pb : power_basis K L)

lemma of_power_basis_eq_prod' (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j),
  -((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))) :=
begin
  rw [discr_power_basis_eq_prod _ _ _ e],
  congr, ext i, congr, ext j,
  ring
end

local notation `n` := finrank K L

lemma of_power_basis_eq_prod'' (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  (-1) ^ (n * (n - 1) / 2) * ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j),
  ((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))) :=
begin
  rw [of_power_basis_eq_prod' _ _ _ e],
  simp_rw [λ i j, neg_eq_neg_one_mul ((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))),
    prod_mul_distrib],
  congr,
  simp only [prod_pow_eq_pow_sum, prod_const],
  congr,
  simp_rw [fin.filter_lt_card],
  apply (@nat.cast_inj ℚ _ _ _ _ _).1,
  rw [nat.cast_sum],
  have : ∀ (x : fin pb.dim), (↑x + 1) ≤ pb.dim := by simp [nat.succ_le_iff, fin.is_lt],
  simp_rw [nat.sub_sub],
  simp only [nat.cast_sub, this, finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    nat.cast_add, nat.cast_one, sum_add_distrib, mul_one],
  rw [← nat.cast_sum, ← @finset.sum_range ℕ _ pb.dim (λ i, i), sum_range_id ],
  have hn : n = pb.dim,
  { rw [← alg_hom.card K L E, ← fintype.card_fin pb.dim],
    exact card_congr (equiv.symm e) },
  have h₂ : 2 ∣ (pb.dim * (pb.dim - 1)) := even_iff_two_dvd.1 (nat.even_mul_self_pred _),
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp,
  have hle : 1 ≤ pb.dim,
  { rw [← hn, nat.one_le_iff_ne_zero, ← zero_lt_iff, finite_dimensional.finrank_pos_iff],
    apply_instance },
  rw [hn, nat.cast_dvd h₂ hne, nat.cast_mul, nat.cast_sub hle],
  field_simp,
  ring,
end

lemma of_power_basis_eq_norm : discr K pb.basis =
  (-1) ^ (n * (n - 1) / 2) * (norm K (aeval pb.gen (minpoly K pb.gen).derivative)) :=
begin
  let E := algebraic_closure L,
  letI := λ (a b : E), classical.prop_decidable (eq a b),

  have e : fin pb.dim ≃ (L →ₐ[K] E),
  { refine equiv_of_card_eq _,
    rw [fintype.card_fin, alg_hom.card],
    exact (power_basis.finrank pb).symm },
  have hnodup : (map (algebra_map K E) (minpoly K pb.gen)).roots.nodup :=
    nodup_roots (separable.map (is_separable.separable K pb.gen)),
  have H : ∀ i j, (e j) pb.gen - (e i) pb.gen = -((e i) pb.gen - (e j) pb.gen) := by simp,
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (map (algebra_map K E) (minpoly K pb.gen)).roots,
  { intro σ,
    rw [mem_roots, is_root.def, eval_map, ← aeval_def, aeval_alg_hom_apply],
    repeat { simp [minpoly.ne_zero (is_separable.is_integral K pb.gen)] } },

  apply (algebra_map K E).injective,
  rw [ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_neg, ring_hom.map_one,
    of_power_basis_eq_prod'' _ _ _ e],
  congr,
  rw [norm_eq_prod_embeddings, fin.prod_filter_gt_mul_neg_eq_prod_off_diag H],
  conv_rhs { congr, skip, funext,
    rw [← aeval_alg_hom_apply, aeval_root_derivative_of_splits (minpoly.monic
      (is_separable.is_integral K pb.gen)) (is_alg_closed.splits_codomain _) (hroots σ),
      ← finset.prod_mk _ (multiset.nodup_erase_of_nodup _ hnodup)] },
  rw [prod_sigma', prod_sigma'],
  refine prod_bij (λ i hi, ⟨e i.2, e i.1 pb.gen⟩) (λ i hi, _) (λ i hi, by simp at hi)
    (λ i j hi hj hij, _) (λ σ hσ, _),
  { simp only [true_and, mem_mk, mem_univ, mem_sigma],
    rw [multiset.mem_erase_of_ne (λ h, _)],
    { exact hroots _ },
    { simp only [true_and, mem_filter, mem_univ, ne.def, mem_sigma] at hi,
      refine hi (equiv.injective e (equiv.injective (power_basis.lift_equiv pb) _)),
      rw [← power_basis.lift_equiv_apply_coe, ← power_basis.lift_equiv_apply_coe] at h,
      exact subtype.eq h } },
  { simp only [equiv.apply_eq_iff_eq, heq_iff_eq] at hij,
    have h := hij.2,
    rw [← power_basis.lift_equiv_apply_coe, ← power_basis.lift_equiv_apply_coe] at h,
    refine sigma.eq (equiv.injective e (equiv.injective _ (subtype.eq h))) (by simp [hij.1]) },
  { simp only [true_and, mem_mk, mem_univ, mem_sigma] at hσ,
    simp only [sigma.exists, true_and, exists_prop, mem_filter, mem_univ, ne.def, mem_sigma],
    refine ⟨e.symm (power_basis.lift pb σ.2 _), e.symm σ.1, ⟨λ h, _, sigma.eq _ _⟩⟩,
    { rw [aeval_def, eval₂_eq_eval_map, ← is_root.def, ← mem_roots],
      { exact multiset.erase_subset _ _ hσ },
      { simp [minpoly.ne_zero (is_separable.is_integral K pb.gen)] } },
    { replace h := alg_hom.congr_fun (equiv.injective _ h) pb.gen,
      rw [power_basis.lift_gen] at h,
      rw [← h] at hσ,
      refine multiset.mem_erase_of_nodup hnodup hσ, },
    all_goals { simp } }
end

end field

end algebra
