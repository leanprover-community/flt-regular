/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import FltRegular.FltThree.FltThree
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.FLT.Four
import Modformsported.ModForms.ModularityConjecture

def frey (p : ℕ) (a b : ℤ)
    (Δ_ne_zero : (16 : ℚ) * ((a : ℚ) ^ p * (b : ℚ) ^ p * ((a : ℚ) ^ p + (b : ℚ) ^ p : ℚ)) ^ 2 ≠ 0) :
    EllipticCurve ℚ where
  a₁ := 0
  a₂ := b ^ p - a ^p
  a₃ := 0
  a₄ := - (a ^ p * b ^ p)
  a₆ := 0
  Δ' := Units.mk0 _ Δ_ne_zero
  coe_Δ' := by
    simp [EllipticCurve.Δ', WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring

def frey.mk (p : ℕ) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (H : a ^ p + b ^ p = c ^ p) :
    EllipticCurve ℚ :=
  frey p a b <| by
    let Δ : ℚ := (16 : ℚ) * ((a : ℚ) ^ p * (b : ℚ) ^ p * (c : ℚ) ^ p) ^ 2
    have Δ_ne_zero : Δ ≠ 0 := by
      dsimp
      refine mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)) <;>
        apply pow_ne_zero <;> assumption_mod_cast
    rw [← @Int.cast_inj ℚ, Int.cast_add, Int.cast_pow, Int.cast_pow, Int.cast_pow] at H
    rwa [H]

lemma flt_primes {p : ℕ} (h : 5 ≤ p) (hp : p.Prime) : FermatLastTheoremWith ℤ p := by
  intro a b c ha hb hc H
  let frey := frey.mk p ha hb hc H
  obtain ⟨n, f, hf, h'⟩ := modularity_conjecture frey
  -- by wiles
  sorry

theorem flt : FermatLastTheorem := by
  intro n h
  rw [ge_iff_le, Nat.succ_le_iff] at h
  zify at h
  obtain ⟨p, hdvd, hp⟩ := OddPrimeOrFour.exists_and_dvd h
  rw [Int.coe_nat_dvd_right] at hdvd
  apply FermatLastTheoremWith.mono hdvd
  have := (fermatLastTheoremWith_nat_int_rat_tfae p.natAbs).out 0 1
  rw [this]
  obtain rfl|⟨hp, hodd⟩ := hp
  · have : Int.natAbs 4 = 4 := by norm_num
    rw [this]
    exact fermatLastTheoremFour
  · by_cases h3 : p.natAbs = 3
    · rw [h3]
      exact flt_three
    · rw [Int.prime_iff_natAbs_prime] at hp
      rw [←Int.natAbs_odd, Nat.odd_iff_not_even] at hodd
      refine flt_primes ?_ hp
      by_contra' hcon
      have := hp.two_le
      interval_cases hp' : p.natAbs
      · exact hodd (by decide)
      · exact Ne.irrefl h3
      · exact hodd (by decide)
