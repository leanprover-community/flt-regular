module

import FltRegular.NumberTheory.Cyclotomic.CyclRat
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

@[expose] public section

open scoped NumberField nonZeroDivisors

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

open FractionalIdeal NumberField IsCMField

namespace FltRegular.CaseI

omit [NeZero p] in
theorem pow_sub_intGalConj_mem (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨a, γ, hγ⟩ := exists_dvd_pow_sub_Int_pow hp.ne' α
  rw [Ideal.mem_span_singleton]
  rw [sub_eq_iff_eq_add] at hγ
  rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_pow, map_intCast,
    add_sub_add_right_eq_sub, ← mul_sub]
  exact dvd_mul_right _ _

theorem exists_int_sum_eq_zero'_aux (x y i : ℤ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ringOfIntegersComplexConj K (x + y * ↑(zetaUnit ^ i) : 𝓞 K) =
      x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ) := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  ext
  simp only [map_add, map_intCast, map_mul, coe_ringOfIntegersComplexConj, zpow_neg, map_units_inv,
    add_right_inj, mul_eq_mul_left_iff, Int.cast_eq_zero]
  simp_rw [NumberField.Units.coe_zpow]
  left
  simp only [map_zpow₀]
  rw [← inv_zpow]
  congr
  change (complexConj K) ζ = ζ⁻¹
  exact complexConj_zeta hζ hp

theorem exists_int_sum_eq_zero' (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, H⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux _ _ _ _ hp, h, ← H, Units.val_mul, mul_assoc, ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u (pow_sub_intGalConj_mem α hp) using 3
  ext
  simp

theorem exists_int_sum_eq_zero (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ x y i h hp
  refine ⟨k, ?_⟩
  have hz : ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) = (zetaUnit ^ (2 * (k : ℤ)) : (𝓞 K)ˣ) := by
    rw [← zpow_natCast (zetaUnit ^ k) 2, ← zpow_natCast zetaUnit k, ← zpow_mul]
    grind
  grind

end FltRegular.CaseI
