module

public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Bounding the exponent of a number-field class group

These are exponent analogues of the principal-ideal criteria in
`Mathlib.NumberTheory.NumberField.ClassNumber`.  They deliberately conclude
only that every ideal class has `e`-th power one; no PID instance is produced.
-/

@[expose] public section

open Ideal NumberField Module NumberField.InfinitePlace Nat Real
open scoped NumberField Pointwise nonZeroDivisors

namespace BealRegular.ClassGroupExponentMinkowski

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- Ideals whose `e`-th powers are principal form a submonoid. -/
private def powerPrincipalSubmonoid (R : Type*) [CommRing R] (e : ℕ) :
    Submonoid (Ideal R) where
  carrier := {I | Submodule.IsPrincipal (I ^ e)}
  one_mem' := by
    change Submodule.IsPrincipal ((1 : Ideal R) ^ e)
    exact (Ideal.isPrincipalSubmonoid R).pow_mem
      (Ideal.isPrincipalSubmonoid R).one_mem e
  mul_mem' := by
    intro I J hI hJ
    change Submodule.IsPrincipal ((I * J) ^ e)
    rw [mul_pow]
    exact (Ideal.isPrincipalSubmonoid R).mul_mem hI hJ

/-- If every prime ideal below the Minkowski bound has principal `e`-th
power, then every class in the class group has `e`-th power one. -/
theorem classGroup_pow_eq_one_of_isPrincipal_pow_of_norm_le_of_isPrime
    (e : ℕ)
    (h : ∀ {P : (Ideal (𝓞 K))⁰}, (P : Ideal (𝓞 K)).IsPrime →
      absNorm (P : Ideal (𝓞 K)) ≤ M K →
        Submodule.IsPrincipal ((P : Ideal (𝓞 K)) ^ e)) :
    ∀ C : ClassGroup (𝓞 K), C ^ e = 1 := by
  intro C
  obtain ⟨I, hIC, hIN⟩ := exists_ideal_in_class_of_norm_le C
  have hIpow : Submodule.IsPrincipal ((I : Ideal (𝓞 K)) ^ e) := by
    change (I : Ideal (𝓞 K)) ∈ powerPrincipalSubmonoid (𝓞 K) e
    rw [← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
    refine Submonoid.multiset_prod_mem _ _ (fun J hJ ↦ ?_)
    change Submodule.IsPrincipal (J ^ e)
    by_cases hJ0 : J = 0
    · subst J
      exact (Ideal.isPrincipalSubmonoid (𝓞 K)).pow_mem bot_isPrincipal e
    rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
    refine h (((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1) ?_
    exact (cast_le.mpr <| le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
      absNorm_dvd_absNorm_of_le <| le_of_dvd <|
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ).trans hIN
  rw [← hIC, ← map_pow]
  exact (ClassGroup.mk0_eq_one_iff (I ^ e).property).mpr (by simpa using hIpow)

/-- In a Galois number field it is enough, for each rational prime in the
Minkowski interval, to exhibit one prime above it whose `e`-th power is
principal (unless its norm already exceeds the bound). -/
theorem classGroup_pow_eq_one_of_one_prime_above
    [IsGalois ℚ K] (e : ℕ)
    (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
      ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        ⌊(M K)⌋₊ < p ^ P.inertiaDeg ℤ ∨
          Submodule.IsPrincipal (P ^ e)) :
    ∀ C : ClassGroup (𝓞 K), C ^ e = 1 := by
  apply classGroup_pow_eq_one_of_isPrincipal_pow_of_norm_le_of_isPrime e
  intro P hP hPN
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal <| under ℤ (P : Ideal (𝓞 K))
  have hp0 : p ≠ 0 := fun hpzero ↦ nonZeroDivisors.coe_ne_zero P <|
    eq_bot_of_comap_eq_bot (R := ℤ) <| by
      simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hlies : (P : Ideal (𝓞 K)).LiesOver (span {p}) := by
    rcases abs_choice p with hpabs | hpabs <;>
      simpa [hpabs, span_singleton_neg p, ← submodule_span_eq, ← hp] using
        over_under (P : Ideal (𝓞 K))
  have hspan : span {(↑p.natAbs : ℤ)} = span {p} := by
    rcases abs_choice p with hpabs | hpabs <;> simp [hpabs]
  have hple : p.natAbs ^ (P : Ideal (𝓞 K)).inertiaDeg ℤ ≤ ⌊(M K)⌋₊ := by
    refine le_floor ?_
    have : (P : Ideal (𝓞 K)).IsMaximal := hP.isMaximal (by simpa using P.property.2)
    have : (span {p}).IsMaximal := (hpprime (hP.under ℤ)).isMaximal_span_singleton
    simpa only [hspan, ← cast_pow, ← natAbs_pow_inertiaDeg p (P : Ideal (𝓞 K))] using hPN
  have hpabsprime := Int.prime_iff_natAbs_prime.mp
    (hpprime (hP.under ℤ))
  have hpmem : p.natAbs ∈ Finset.Icc 1 ⌊(M K)⌋₊ := by
    suffices 0 < (P : Ideal (𝓞 K)).inertiaDeg ℤ by
      exact Finset.mem_Icc.mpr ⟨hpabsprime.one_le, le_trans (le_pow this) hple⟩
    have := (isPrime_of_prime (prime_span_singleton_iff.mpr <|
      hpprime (hP.under ℤ))).isMaximal <| by
        simp [(hpprime (hP.under ℤ)).ne_zero]
    exact inertiaDeg_pos (P : Ideal (𝓞 K)) ℤ
  obtain ⟨Q, ⟨hQprime, hQlies⟩, H⟩ := h p.natAbs hpmem hpabsprime
  letI : (span {(↑p.natAbs : ℤ)}).IsMaximal :=
    (isPrime_of_prime (prime_span_singleton_iff.mpr
      (prime_iff_prime_int.mp hpabsprime))).isMaximal (by simpa using hp0)
  by_cases hlarge : ⌊(M K)⌋₊ < p.natAbs ^ (P : Ideal (𝓞 K)).inertiaDeg ℤ
  · linarith
  have hPlies : (P : Ideal (𝓞 K)).LiesOver (span {(↑p.natAbs : ℤ)}) := by
    rw [hspan]
    exact hlies
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver (span {(↑p.natAbs : ℤ)}) := hQlies
  letI : (P : Ideal (𝓞 K)).IsPrime := hP
  letI : (P : Ideal (𝓞 K)).LiesOver (span {(↑p.natAbs : ℤ)}) := hPlies
  rw [inertiaDeg_eq_of_isGaloisGroup (span {(↑p.natAbs : ℤ)}) Q
    (P : Ideal (𝓞 K)) (K ≃ₐ[ℚ] K)] at H
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup (span {(↑p.natAbs : ℤ)}) Q
    (P : Ideal (𝓞 K)) (K ≃ₐ[ℚ] K)
  rw [← hσ, pointwise_smul_def, ← Ideal.map_pow]
  exact (H.resolve_left hlarge).map_ringHom
    (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ)

end BealRegular.ClassGroupExponentMinkowski
