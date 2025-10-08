/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module number_theory.cyclotomic.cyclotomic_units
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section

open Polynomial Finset

variable {A : Type*} [CommRing A] [IsDomain A]

section CyclotomicUnit

namespace CyclotomicUnit

-- this result holds for all primitive roots; dah.
theorem associated_one_sub_pow_primitive_root_of_coprime {n j k : ℕ} {ζ : A}
    (hζ : IsPrimitiveRoot ζ n) (hk : k.Coprime n) (hj : j.Coprime n) :
    Associated (1 - ζ ^ j) (1 - ζ ^ k) := by
  suffices ∀ {j : ℕ}, j.Coprime n → Associated (1 - ζ) (1 - ζ ^ j) by
    exact (this hj).symm.trans (this hk)
  clear k j hk hj
  intro j hj
  refine associated_of_dvd_dvd (one_sub_dvd_one_sub_pow _ _) ?_
  -- is there an easier way to do this?
  rcases eq_or_ne n 0 with rfl | hn'
  · simp [j.coprime_zero_right.mp hj]
  rcases eq_or_ne n 1 with rfl | hn
  · simp [IsPrimitiveRoot.one_right_iff.mp hζ]
  replace hn : 1 < n := by omega
  obtain ⟨m, hm⟩ := Nat.exists_mul_emod_eq_one_of_coprime hj hn
  have : ζ = (ζ ^ j) ^ m := by rw [← pow_mul, ←pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]
  nth_rw 2 [this]
  exact one_sub_dvd_one_sub_pow _ _

theorem IsPrimitiveRoot.sum_pow_unit {n k : ℕ} {ζ : A} (hn : 2 ≤ n) (hk : k.Coprime n)
    (hζ : IsPrimitiveRoot ζ n) : IsUnit (∑ i ∈ range k, ζ ^ i) := by
  have h1 : (1 : ℕ).Coprime n := Nat.coprime_one_left n
  obtain ⟨u, hu⟩ := associated_one_sub_pow_primitive_root_of_coprime hζ hk h1
  simp only [pow_one] at hu
  convert u.isUnit
  refine mul_left_cancel₀ (sub_ne_zero_of_ne (hζ.ne_one (by cutsat) |>.symm)) ?_
  rw [hu, mul_neg_geom_sum]

theorem IsPrimitiveRoot.zeta_pow_sub_eq_unit_zeta_sub_one {p i j : ℕ} {ζ : A} (hn : 2 ≤ p)
    (hp : p.Prime) (hi : i < p) (hj : j < p) (hij : i ≠ j) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : Aˣ, ζ ^ i - ζ ^ j = u * (1 - ζ) := by
  by_cases hilj : j < i
  · have h1 : ζ ^ i - ζ ^ j = ζ ^ j * (ζ ^ (i - j) - 1) := by
      ring_nf
      rw [pow_mul_pow_sub _ hilj.le]
      ring
    rw [h1]
    have hic : (i - j).Coprime p := by
      rw [Nat.coprime_comm]; apply Nat.coprime_of_lt_prime _ _ hp
      rw [← Nat.pos_iff_ne_zero]
      apply Nat.sub_pos_of_lt hilj
      by_cases hj : 0 < j
      · apply lt_trans _ hi
        apply Nat.sub_lt_of_pos_le hj hilj.le
      · simp only [not_lt, _root_.le_zero_iff] at hj
        simp only [hi, tsub_zero, hj]
    obtain ⟨v, hv⟩ : IsUnit (-ζ ^ j * ∑ k ∈ range (i - j), ζ ^ k) := by
      apply IsUnit.mul _ (IsPrimitiveRoot.sum_pow_unit hn hic hζ); apply IsUnit.neg
      apply IsUnit.pow; apply hζ.isUnit hp.ne_zero
    use v
    have h2 := mul_neg_geom_sum ζ (i - j)
    rw [mul_comm] at h2
    rw [hv, mul_assoc, h2]
    ring
  · simp only [ne_eq, not_lt] at hij hilj
    have h1 : ζ ^ i - ζ ^ j = ζ ^ i * (1 - ζ ^ (j - i)) := by
      ring_nf
      rw [sub_right_inj, pow_mul_pow_sub _ hilj]
    rw [h1]
    have h2 := mul_neg_geom_sum ζ (j - i)
    have hjc : (j - i).Coprime p := by
      rw [Nat.coprime_comm]
      apply Nat.coprime_of_lt_prime _ _ hp
      have hilj' : i < j := by rw [lt_iff_le_and_ne]; simp [hij, hilj]
      rw [← Nat.pos_iff_ne_zero]
      apply Nat.sub_pos_of_lt hilj'
      by_cases hii : 0 < i
      · apply lt_trans _ hj
        apply Nat.sub_lt_of_pos_le hii hilj
      · simp only [not_lt, _root_.le_zero_iff] at hii
        simpa [hii]
    have h3 : IsUnit (ζ ^ i * ∑ k ∈ range (j - i), ζ ^ k) := by
      apply IsUnit.mul _ (IsPrimitiveRoot.sum_pow_unit hn hjc hζ); apply IsUnit.pow
      apply hζ.isUnit hp.ne_zero
    obtain ⟨v, hv⟩ := h3
    use v
    rw [mul_comm] at h2
    rw [hv, mul_assoc, h2]

end CyclotomicUnit

lemma IsPrimitiveRoot.associated_sub_one {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ p) {η₁ : A}
    (hη₁ : η₁ ∈ nthRootsFinset p 1) {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p 1) (e : η₁ ≠ η₂) :
    Associated (ζ - 1) (η₁ - η₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, ⟨hi, rfl⟩⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, ⟨hj, rfl⟩⟩ :=
    hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  have : i ≠ j := ne_of_apply_ne _ e
  obtain ⟨u, h⟩ := CyclotomicUnit.IsPrimitiveRoot.zeta_pow_sub_eq_unit_zeta_sub_one
    hp.two_le hp hi hj this hζ
  rw [h, associated_isUnit_mul_right_iff u.isUnit, ← associated_isUnit_mul_right_iff isUnit_one.neg,
    neg_one_mul, neg_sub]
  exact Associates.mk_eq_mk_iff_associated.mp (by simp)

end CyclotomicUnit
