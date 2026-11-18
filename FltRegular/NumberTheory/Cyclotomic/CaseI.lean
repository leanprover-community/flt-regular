module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

/-!
# Cyclotomic lemmas for Case I

This file establishes the complex-conjugation congruence used in the first case of Fermat's Last
Theorem for regular primes.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

open FractionalIdeal NumberField IsCMField

namespace FltRegular.CaseI

omit [NeZero p] in
/-- The difference between a `p`-th power and its complex conjugate is divisible by `p`. -/
theorem pow_sub_intGalConj_mem (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨a, γ, hγ⟩ := exists_dvd_pow_sub_Int_pow hp.ne' α
  rw [Ideal.mem_span_singleton, sub_eq_iff_eq_add.mp hγ, _root_.map_add, _root_.map_mul,
    map_natCast, map_pow, map_intCast, add_sub_add_right_eq_sub, ← mul_sub]
  exact dvd_mul_right _ _

/-- Complex conjugation negates the exponent of the distinguished cyclotomic unit. -/
theorem exists_int_sum_eq_zero'_aux (x y i : ℤ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ringOfIntegersComplexConj K (x + y * ↑(zetaUnit ^ i) : 𝓞 K) =
      x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ) := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  ext
  simp [NumberField.Units.coe_zpow, coe_ringOfIntegersComplexConj,
    show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from rfl, complexConj_zeta hζ hp]

/-- A natural exponent giving the Case I complex-conjugation congruence modulo `p`. -/
theorem exists_int_sum_eq_zero' (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hroot⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux _ _ _ _ hp, h, ← hroot, Units.val_mul, mul_assoc,
    ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u (pow_sub_intGalConj_mem α hp) using 3
  ext
  simp [coe_ringOfIntegersComplexConj]

/-- An integer exponent giving the Case I complex-conjugation congruence modulo `p`. -/
theorem exists_int_sum_eq_zero (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ x y i h hp
  exact ⟨k, by rwa [zpow_mul', zpow_natCast, zpow_ofNat]⟩

end FltRegular.CaseI
