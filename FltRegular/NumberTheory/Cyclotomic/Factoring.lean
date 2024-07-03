/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module number_theory.cyclotomic.factoring
-/
import  Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import FltRegular.ReadyForMathlib.Homogenization

open Polynomial Finset MvPolynomial

-- TODO might be nice to have an explicit two variable version of this factorization
-- in an mv_polynomial ring with two chosen variables
/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
theorem pow_sub_pow_eq_prod_sub_zeta_runity_mul {K : Type _} [CommRing K] [IsDomain K] {ζ : K}
    {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) (x y : K) :
    x ^ (n : ℕ) - y ^ (n : ℕ) = ∏ ζ : K in nthRootsFinset n K, (x - ζ * y) :=
  by
  -- suffices to show the identity in a multivariate polynomial ring with two generators over K
  suffices
    (X 0 : MvPolynomial (Fin 2) K) ^ (n : ℕ) - X 1 ^ (n : ℕ) =
      ∏ ζ in nthRootsFinset n K, (X 0 - MvPolynomial.C ζ * X 1)
    by
    apply_fun MvPolynomial.eval fun i : Fin 2 => if i = 0 then x else y at this
    simpa [MvPolynomial.eval_prod] using this
  -- we know the univariate / one argument version of the identity
  have := X_pow_sub_one_eq_prod hpos h
  -- transfer this to a polynomial ring with two variables
  have := congr_arg (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) K)) this
  simp only [map_prod, aeval_X_pow, Polynomial.aeval_X, aeval_one, Polynomial.aeval_C,
    AlgHom.map_sub] at this
  -- the homogenization of the identity is also true
  have := congr_arg (homogenization 1) this
  -- simplify to get the result we want
  simpa [homogenization_prod, Polynomial.algebraMap_eq, hpos]

/-- If there is a primitive `n`th root of unity in `K` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
theorem pow_add_pow_eq_prod_add_zeta_runity_mul {K : Type _} [CommRing K] [IsDomain K] {ζ : K}
    {n : ℕ} (hodd : n % 2 = 1) (h : IsPrimitiveRoot ζ n) (x y : K) :
    x ^ (n : ℕ) + y ^ (n : ℕ) = ∏ ζ : K in nthRootsFinset n K, (x + ζ * y) :=
  by
  have := pow_sub_pow_eq_prod_sub_zeta_runity_mul (Nat.odd_iff.mpr hodd).pos h x (-y)
  simp only [mul_neg, sub_neg_eq_add] at this
  rw [neg_pow, neg_one_pow_eq_pow_mod_two] at this
  simpa [hodd] using this
