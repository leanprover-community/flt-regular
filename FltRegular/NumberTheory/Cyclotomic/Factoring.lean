/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

-/
import  Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Polynomial Finset

variable {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {n : ℕ} (x y : R)

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
theorem pow_sub_pow_eq_prod_sub_zeta_runity_mul_field {K : Type*} [Field K] {ζ : K} (x y : K)
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n K, (x - ζ * y) := by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.not_eq_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  have := congr_arg (eval (x/y)) <| X_pow_sub_one_eq_prod hpos h
  rw [eval_sub, eval_pow, eval_one, eval_X, eval_prod] at this
  simp_rw [eval_sub, eval_X, eval_C] at this
  apply_fun (· * y ^ n) at this
  rw [sub_mul, one_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero n hy)] at this
  nth_rw 4 [← h.card_nthRootsFinset] at this
  rw [mul_comm, pow_card_mul_prod] at this
  convert this using 2
  field_simp [hy]
  rw [mul_comm]

/-- If there is a primitive `n`th root of unity in `R`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
theorem pow_sub_pow_eq_prod_sub_zeta_runity_mul (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n R, (x - ζ * y) := by
  let K := FractionRing R
  apply NoZeroSMulDivisors.algebraMap_injective R K
  rw [map_sub, map_pow, map_pow, map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
    h.map_of_injective <| NoZeroSMulDivisors.algebraMap_injective R K
  rw [pow_sub_pow_eq_prod_sub_zeta_runity_mul_field _ _ hpos h']
  symm
  refine prod_nbij (algebraMap R K) (fun a ha ↦ ?_) (fun a _ b _ H ↦
    NoZeroSMulDivisors.algebraMap_injective R K H) (fun a ha ↦ ?_) (fun _ _ ↦ rfl)
  · rw [mem_nthRootsFinset hpos, ← map_pow, (mem_nthRootsFinset hpos).1 ha, map_one]
  · rw [mem_coe, mem_nthRootsFinset hpos] at ha
    simp only [Set.mem_image, mem_coe]
    obtain ⟨i, -, hζ⟩ := h'.eq_pow_of_pow_eq_one ha hpos
    refine ⟨ζ ^ i, ?_, by rwa [map_pow]⟩
    rw [mem_nthRootsFinset hpos, ← pow_mul, mul_comm, pow_mul, h.pow_eq_one, one_pow]

/-- If there is a primitive `n`th root of unity in `K` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
theorem pow_add_pow_eq_prod_add_zeta_runity_mul (hodd : n % 2 = 1) (h : IsPrimitiveRoot ζ n) :
    x ^ n + y ^ n = ∏ ζ ∈ nthRootsFinset n R, (x + ζ * y) :=  by
  have := pow_sub_pow_eq_prod_sub_zeta_runity_mul x (-y) (Nat.odd_iff.mpr hodd).pos h
  simp only [mul_neg, sub_neg_eq_add] at this
  rw [neg_pow, neg_one_pow_eq_pow_mod_two] at this
  simpa [hodd] using this
