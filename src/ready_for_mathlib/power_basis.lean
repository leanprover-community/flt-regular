import ring_theory.power_basis
import linear_algebra.matrix.basis
import ring_theory.algebraic
import ring_theory.adjoin.power_basis

import ready_for_mathlib.integral_closure

universes u v z w

variables {R : Type z} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S]
variables {K : Type u} [field K] [algebra K S] (B : power_basis K S)

open algebra polynomial subalgebra algebra.adjoin

open_locale polynomial

namespace power_basis

lemma is_integral_coord_gen_pow {A : Type w} [comm_ring A] [algebra R A] [algebra S A]
  [is_scalar_tower R S A] [is_domain S] {B : power_basis S A} (hB : is_integral R B.gen)
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) (n : ℕ) :
  ∀ i, is_integral R (B.basis.repr (B.gen ^ n) i) :=
begin
  intro i,
  let Q := (X ^ n) %ₘ (minpoly R B.gen),
  have : B.gen ^ n = aeval B.gen Q,
  { rw [← @aeval_X_pow R _ _ _ _ B.gen, ← mod_by_monic_add_div (X ^ n) (minpoly.monic hB)],
    simp },
  by_cases hQ : Q = 0,
  { simp [this, hQ, is_integral_zero] },
  have hlt : Q.nat_degree < B.dim,
  { rw [← B.nat_degree_minpoly, hmin, nat_degree_map_of_monic (minpoly.monic hB),
      nat_degree_lt_nat_degree_iff hQ],
    letI : nontrivial R := nontrivial.of_polynomial_ne hQ,
    exact degree_mod_by_monic_lt _ (minpoly.monic hB),
    apply_instance },
  rw [this, aeval_eq_sum_range' hlt],
  simp only [linear_equiv.map_sum, linear_equiv.map_smulₛₗ, ring_hom.id_apply, finset.sum_apply'],
  refine is_integral.sum _ (λ j hj, _),
  replace hj := finset.mem_range.1 hj,
  rw [← fin.coe_mk hj, ← B.basis_eq_pow, algebra.smul_def,
    is_scalar_tower.algebra_map_apply R S A, ← algebra.smul_def, linear_equiv.map_smul],
  simp only [algebra_map_smul, finsupp.coe_smul, pi.smul_apply, B.basis.repr_self_apply],
  by_cases hij : (⟨j, hj⟩ : fin _) = i,
  { simp only [hij, eq_self_iff_true, if_true],
    rw [algebra.smul_def, mul_one],
    exact is_integral_algebra_map },
  { simp [hij, is_integral_zero] }
end

lemma is_integral_coord_prod {A : Type w} [comm_ring A] [algebra R A] [algebra S A] [is_domain S]
  [is_scalar_tower R S A] {B : power_basis S A} {x y : A} (hB : is_integral R B.gen)
  (hx : ∀ i, is_integral R (B.basis.repr x i)) (hy : ∀ i, is_integral R (B.basis.repr y i))
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) :
  ∀ i, is_integral R ((B.basis.repr (x * y) i)) :=
begin
  intro i,
  rw [← B.basis.sum_repr x, ← B.basis.sum_repr y, finset.sum_mul_sum, linear_equiv.map_sum,
    finset.sum_apply'],
  refine is_integral.sum _ (λ I hI, _),
  simp only [algebra.smul_mul_assoc, algebra.mul_smul_comm, linear_equiv.map_smulₛₗ,
    ring_hom.id_apply, finsupp.coe_smul, pi.smul_apply, id.smul_eq_mul],
  refine is_integral_mul (hy _) (is_integral_mul (hx _) _),
  simp only [coe_basis, ← pow_add],
  refine is_integral_coord_gen_pow hB hmin _ _,
end

lemma is_integral_coord_pow {A : Type w} [comm_ring A] [algebra R A] [algebra S A] [is_domain S]
  [is_scalar_tower R S A] {B : power_basis S A} {x : A} (hB : is_integral R B.gen)
  (hx : ∀ i, is_integral R (B.basis.repr x i))
  (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebra_map R S)) (n : ℕ) :
  ∀ i, is_integral R ((B.basis.repr (x ^ n) i)) :=
begin
  by_cases htriv : nontrivial A, swap,
  { intro i,
    rw [subsingleton_iff.1 (not_nontrivial_iff_subsingleton.1 htriv) (x ^ n) 0],
    simp [is_integral_zero] },
  letI := htriv,
  revert hx,
  refine nat.case_strong_induction_on n _ (λ n hn, _),
  { intros hx i,
    rw [pow_zero, ← pow_zero B.gen, ← fin.coe_mk B.dim_pos, ← B.basis_eq_pow,
      B.basis.repr_self_apply],
    by_cases hi : (⟨0, B.dim_pos⟩ : fin _) = i,
    { simp [hi, is_integral_one] },
    { simp [hi, is_integral_zero] } },
  { intros hx i,
    rw [pow_succ],
    refine is_integral_coord_prod hB hx (λ _, hn _ le_rfl (λ _, hx _) _) hmin _ }
end

lemma adjoin_gen_eq_top (B : power_basis R S) : adjoin R ({B.gen} : set S) = ⊤ :=
begin
  rw [← to_submodule_eq_top, _root_.eq_top_iff, ← B.basis.span_eq, submodule.span_le],
  rintros x ⟨i, rfl⟩,
  rw [B.basis_eq_pow i],
  exact subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton _)) _,
end

lemma adjoin_eq_top_of_gen_mem {B : power_basis R S} {x : S} (hx : B.gen ∈ adjoin R ({x} : set S)) :
  adjoin R ({x} : set S) = ⊤ :=
begin
  rw [_root_.eq_top_iff, ← B.adjoin_gen_eq_top],
  refine adjoin_le _,
  simp [hx],
end

/-- The power basis given by `x` if `B.gen ∈ adjoin K {x}`. -/
noncomputable def of_mem_adjon {x : S} (hint : is_integral K x)
  (hx : B.gen ∈ adjoin K ({x} : set S)) : power_basis K S :=
(power_basis hint).map ((equiv_of_eq _ _ $ adjoin_eq_top_of_gen_mem hx).trans top_equiv)

lemma of_mem_adjon_gen {x : S} (hint : is_integral K x)
  (hs : B.gen ∈ adjoin K ({x} : set S)) : (B.of_mem_adjon hint hs).gen = x := rfl

variables [algebra R K] [is_scalar_tower R K S] {B}

lemma to_matrix_is_integral_coeff {B' : power_basis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
  (hB : is_integral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebra_map R K)) :
  ∀ i j, _root_.is_integral R (B.basis.to_matrix B'.basis i j) :=
begin
  intros i j,
  rw [B.basis.to_matrix_apply, B'.coe_basis],
  refine is_integral_coord_pow hB (λ i, _) hmin _ _,
  rw [← h, aeval_eq_sum_range, linear_equiv.map_sum, finset.sum_apply'],
  refine is_integral.sum _ (λ n hn, _),
  rw [algebra.smul_def, is_scalar_tower.algebra_map_apply R K S, ← algebra.smul_def,
    linear_equiv.map_smul, algebra_map_smul],
  exact is_integral_smul _ (is_integral_coord_gen_pow hB hmin _ _),
end

end power_basis
