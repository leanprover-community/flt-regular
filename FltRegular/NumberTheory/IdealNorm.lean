import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra
section intNorm

variable (R S K L) [CommRing R] [CommRing S] [Field K] [Field L]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

instance : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰

open nonZeroDivisors

end intNorm

section SpanNorm

namespace Ideal

open Submodule

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable [IsIntegrallyClosed R] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

section

variable [hRS : Module.Finite R S]

variable [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.Free R S]

theorem IsLocalization.AtPrime.PID_of_dedekind_domain {A} [CommRing A]
    [IsDedekindDomain A]
    (P : Ideal A) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsPrincipalIdealRing Aₘ :=
  have : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  have : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain Aₘ).out 2 0).mp
    (IsLocalization.AtPrime.isDedekindDomain A P _)

end

variable [Module.Finite R S] [IsDedekindDomain R] [IsDedekindDomain S]

/-- Multiplicativity of `Ideal.spanIntNorm`. simp-normal form is `map_mul (Ideal.relNorm R)`. -/
theorem spanNorm_map (I : Ideal R) :
    spanNorm R (I.map (algebraMap R S)) =
      I ^ (Module.finrank (FractionRing R) (FractionRing S)) := by
  nontriviality R
  nontriviality S
  refine eq_of_localization_maximal ?_
  intro P hPd
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let Sₚ := Localization P'
  let _ : Algebra Rₚ Sₚ := localizationAlgebra P.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  have : IsDomain Sₚ := IsLocalization.isDomain_localization h
  have : IsDedekindDomain Sₚ := IsLocalization.isDedekindDomain S h _
  have : IsPrincipalIdealRing Rₚ := IsLocalization.AtPrime.PID_of_dedekind_domain P Rₚ
  have := isIntegrallyClosed_of_isLocalization Rₚ P.primeCompl P.primeCompl_le_nonZeroDivisors
  have := NoZeroSMulDivisors_of_isLocalization R S Rₚ Sₚ P.primeCompl_le_nonZeroDivisors
  have := Module.Finite_of_isLocalization R S Rₚ Sₚ P.primeCompl
  let K := FractionRing R
  let f : Rₚ →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) P.primeCompl_le_nonZeroDivisors
  letI := f.toAlgebra
  have : IsScalarTower R Rₚ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl Rₚ K
  let L := FractionRing S
  let g : Sₚ →+* L := IsLocalization.map _ (M := P') (T := S⁰) (RingHom.id S) h
  letI := g.toAlgebra
  haveI : IsScalarTower S Sₚ (FractionRing S) := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHom.comp_id])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    P' Sₚ (FractionRing S)
  let _ := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Rₚ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Rₚ Sₚ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext P.primeCompl
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Sₚ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₚ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have : IsIntegralClosure Sₚ Rₚ L := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv Rₚ (FractionRing R)).symm.toRingEquiv
      (FractionRing.algEquiv Sₚ (FractionRing S)).symm.toRingEquiv
    apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R Rₚ (FractionRing R), AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply S Sₚ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    simp only [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R Rₚ (FractionRing Rₚ), ← IsScalarTower.algebraMap_apply Rₚ,
      ← IsScalarTower.algebraMap_apply]
  have : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (S := S)
    (Rₘ := Localization.AtPrime P) (Sₘ := Localization P') _ _ P.primeCompl_le_nonZeroDivisors]
  rw [Ideal.map_pow, I.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R Rₚ Sₚ,
    ← I.map_map, ← (I.map _).span_singleton_generator, Ideal.map_span, Set.image_singleton,
    spanNorm_singleton, Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply Rₚ K L, Algebra.norm_algebraMap, map_pow]

end Ideal

end SpanNorm
