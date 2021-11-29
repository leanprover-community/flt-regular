/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import number_theory.cyclotomic.basic
import ring_theory.polynomial.homogenization


open polynomial finset mv_polynomial
open_locale big_operators
namespace polynomial

lemma aeval_sum {σ ι R : Type*} [comm_semiring R] (s : finset ι) (f : ι → polynomial R)
  (g : σ → R) : aeval g (∑ i in s, f i) = ∑ i in s, aeval g (f i) :=
(polynomial.aeval g : polynomial R →ₐ[_] _).map_sum f s

@[to_additive]
lemma aeval_prod {ι R T : Type*} [comm_semiring R] [comm_semiring T] [algebra R T] (s : finset ι)
  (f : ι → polynomial R) (g : T) : aeval g (∏ i in s, f i) = ∏ i in s, aeval g (f i) :=
(polynomial.aeval g : polynomial R →ₐ[_] _).map_prod f s

end polynomial

namespace mv_polynomial
lemma aeval_sum {σ ι R : Type*} [comm_semiring R] (s : finset ι) (f : ι → mv_polynomial σ R)
  (g : σ → R) :
  aeval g (∑ i in s, f i) = ∑ i in s, aeval g (f i) :=
(mv_polynomial.aeval g).map_sum _ _

@[to_additive]
lemma aeval_prod {σ ι R : Type*} [comm_semiring R] (s : finset ι) (f : ι → mv_polynomial σ R)
  (g : σ → R) :
  aeval g (∏ i in s, f i) = ∏ i in s, aeval g (f i) :=
(mv_polynomial.aeval g).map_prod _ _
end mv_polynomial

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
lemma pow_sub_pow_eq_prod_sub_zeta_mul {K : Type*} [field K] {ζ : K} {n : ℕ} (hpos : 0 < n)
  (h : is_primitive_root ζ n) (x y : K) :
  x ^ (n : ℕ) - y ^ (n : ℕ) = ∏ (ζ : K) in nth_roots_finset n K, (x - ζ * y) :=
begin
  suffices : (X 0 : mv_polynomial (fin 2) K) ^ (n : ℕ) - (X 1) ^ (n : ℕ) =
    ∏ ζ in nth_roots_finset n K, (X 0 - C ζ * X 1),
  { apply_fun (mv_polynomial.eval ((λ i : fin 2, if i = 0 then x else y))) at this,
    simpa [mv_polynomial.eval_prod] using this, },
  have := X_pow_sub_one_eq_prod hpos h,
  have := congr_arg (aeval (X 0 : mv_polynomial (fin 2) K)) this,
  simp only [polynomial.aeval_prod, polynomial.aeval_X_pow, polynomial.aeval_X,
    polynomial.aeval_one, polynomial.aeval_C, alg_hom.map_sub] at this,
  have hh := congr_arg (homogenization 1) this,
  rw [homogenization_prod, algebra_map_eq, ← mv_polynomial.C_1] at hh, -- TODO homog x_pow_sub_one?
  simp only [hpos, homogenization_X_pow_sub_C, homogenization_X_sub_C] at hh,
  simpa using hh,
end

/-- If there is a primitive `n`th root of unity in `K` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
lemma pow_add_pow_eq_prod_add_zeta_mul {K : Type*} [field K] {ζ : K} {n : ℕ} (hodd : n % 2 = 1)
  (h : is_primitive_root ζ n) (x y : K) :
  x ^ (n : ℕ) + y ^ (n : ℕ) = ∏ (ζ : K) in nth_roots_finset n K, (x + ζ * y) :=
begin
  -- TODO rename nat.odd_gt_zero
  have := pow_sub_pow_eq_prod_sub_zeta_mul (nat.odd_gt_zero (nat.odd_iff.mpr hodd)) h x (-y),
  simp only [mul_neg_eq_neg_mul_symm, sub_neg_eq_add] at this,
  rw [neg_pow, neg_one_pow_eq_pow_mod_two] at this,
  simpa [hodd] using this,
end
