module

public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import FltRegular.NumberTheory.Hilbert94
import FltRegular.NumberTheory.KummersLemma.Field

/-!
# Kummer's lemma for regular primes

This file proves the unit form of Kummer's lemma for regular primes.
-/

@[expose] public section

open Polynomial IsCyclotomicExtension.Rat
open scoped NumberField

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hp hreg

theorem exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one {u : (𝓞 K)ˣ}
    (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ p = u := by
  by_contra! hu
  have hirr := irreducible_X_pow_sub_C_of_prime hpri.out hu
  have := Fact.mk hirr
  have hζ' : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩
  let L := AdjoinRoot (X ^ p - C (u : K))
  have := isSplittingField_AdjoinRoot_X_pow_sub_C hζ' hirr
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ' hirr L
  have := IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C hζ' hirr L
  have : NumberField L :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
      to_finiteDimensional := Module.Finite.trans K L }
  have hKL : Module.finrank K L = p := finrank_of_isSplittingField_X_pow_sub_C hζ' hirr L
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := dvd_card_classGroup_of_unramified_isCyclic (hKL.symm ▸ hpri.out) (hKL.symm ▸ hp)
  exact (hpri.out.dvd_iff_not_coprime.mp (hKL ▸ this)) (by convert hreg)

variable [IsCyclotomicExtension {p} ℚ K]

/-- A regular prime criterion: if a unit of the cyclotomic field is congruent to an integer
modulo `p`, then it is a `p`-th power. -/
theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) :
    ∃ v, u = v ^ p := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1) - 1 := by
      refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := Int.cast_dvd_cast (α := 𝓞 K) _ _ h
      simp only [Int.cast_natCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_isUnit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime _ hζ).dvd.trans h) u.isUnit))
      simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := Int.cast_dvd_cast (α := 𝓞 K) _ _ hn'
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have hdvd : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    have H := norm_add_one_smul_of_isUnit hpri.out hp x
      (nsmul_eq_mul p x ▸ add_comm (p * x) 1 ▸ sub_eq_iff_eq_add.mp hx ▸ (u ^ (p - 1)).isUnit)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ x
    simpa [nsmul_eq_mul, ← hx] using this
  obtain ⟨v, hv⟩ := exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one hp hreg hζ hdvd
  let w : 𝓞 K := ⟨v, IsIntegral.of_pow (NeZero.pos p)
    (hv ▸ NumberField.RingOfIntegers.isIntegral_coe _)⟩
  have hw : IsUnit w := (isUnit_pow_iff (NeZero.ne p)).mp <| by
    rw [show w ^ p = ↑(u ^ (p - 1) : (𝓞 K)ˣ) by ext; exact hv]
    exact (u ^ (p - 1)).isUnit
  have hv'' : hw.unit ^ p = u ^ (p - 1) := Units.ext (Subtype.ext hv)
  exact ⟨u / hw.unit, by rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le hpri.out.one_lt.le, pow_one]⟩
