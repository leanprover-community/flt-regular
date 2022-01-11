/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import ready_for_mathlib.cyclotomic.basic
import ring_theory.polynomial.homogenization

open_locale big_operators

open polynomial finset mv_polynomial

-- TODO might be nice to have an explicit two variable version of this factorization
-- in an mv_polynomial ring with two chosen variables

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
lemma pow_sub_pow_eq_prod_sub_zeta_runity_mul {K : Type*} [comm_ring K] [is_domain K] {ζ : K}
  {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) (x y : K) :
  x ^ (n : ℕ) - y ^ (n : ℕ) = ∏ (ζ : K) in nth_roots_finset n K, (x - ζ * y) :=
begin
  -- suffices to show the identity in a multivariate polynomial ring with two generators over K
  suffices : (X 0 : mv_polynomial (fin 2) K) ^ (n : ℕ) - (X 1) ^ (n : ℕ) =
    ∏ ζ in nth_roots_finset n K, (X 0 - C ζ * X 1),
  { apply_fun (mv_polynomial.eval ((λ i : fin 2, if i = 0 then x else y))) at this,
    simpa [mv_polynomial.eval_prod] using this, },
  -- we know the univariate / one argument version of the identity
  have := X_pow_sub_one_eq_prod hpos h,
  -- transfer this to a polynomial ring with two variables
  have := congr_arg (aeval (X 0 : mv_polynomial (fin 2) K)) this,
  simp only [polynomial.aeval_prod, polynomial.aeval_X_pow, polynomial.aeval_X,
    polynomial.aeval_one, polynomial.aeval_C, alg_hom.map_sub] at this,
  -- the homogenization of the identity is also true
  have := congr_arg (homogenization 1) this,
  -- simplify to get the result we want
  simpa [homogenization_prod, algebra_map_eq, hpos],
end

/-- If there is a primitive `n`th root of unity in `K` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
lemma pow_add_pow_eq_prod_add_zeta_runity_mul {K : Type*} [comm_ring K] [is_domain K] {ζ : K}
  {n : ℕ} (hodd : n % 2 = 1) (h : is_primitive_root ζ n) (x y : K) :
  x ^ (n : ℕ) + y ^ (n : ℕ) = ∏ (ζ : K) in nth_roots_finset n K, (x + ζ * y) :=
begin
  -- TODO rename nat.odd_gt_zero
  have := pow_sub_pow_eq_prod_sub_zeta_runity_mul (nat.odd_gt_zero (nat.odd_iff.mpr hodd)) h x (-y),
  simp only [mul_neg_eq_neg_mul_symm, sub_neg_eq_add] at this,
  rw [neg_pow, neg_one_pow_eq_pow_mod_two] at this,
  simpa [hodd] using this,
end
