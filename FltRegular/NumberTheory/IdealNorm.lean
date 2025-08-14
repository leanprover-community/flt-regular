import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
    .of_isLocalization R S R⁰

open nonZeroDivisors

end intNorm

section SpanNorm

namespace Ideal

open Submodule

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable [IsIntegrallyClosed R] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

variable [Module.Finite R S] [IsDedekindDomain R] [IsDedekindDomain S]

attribute [local instance] FractionRing.liftAlgebra

/-- Multiplicativity of `Ideal.spanIntNorm`. simp-normal form is `map_mul (Ideal.relNorm R)`. -/
theorem spanNorm_algebraMap (I : Ideal R) :
    spanNorm R (I.map (algebraMap R S)) =
      I ^ (Module.finrank (FractionRing R) (FractionRing S)) := by
  refine eq_of_localization_maximal (fun P hPd ↦ ?_)
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let K := FractionRing R
  simp only [← spanIntNorm_localization (R := R) (Sₘ := Localization P') _ _
    P.primeCompl_le_nonZeroDivisors]
  rw [Ideal.map_pow, I.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R Rₚ,
    ← I.map_map, ← (I.map _).span_singleton_generator, Ideal.map_span, Set.image_singleton,
    spanNorm_singleton, Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := FractionRing S), ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply Rₚ K, Algebra.norm_algebraMap, map_pow]

end Ideal

end SpanNorm
