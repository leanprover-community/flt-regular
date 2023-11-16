import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalProperties
import Mathlib.NumberTheory.RamificationInertia
import FltRegular.NumberTheory.AuxLemmas
/-!

Generalizes `Ideal.spanNorm` in `Mathlib/RingTheory/Ideal/Norm.lean` to non-free extensions.

-/
open scoped nonZeroDivisors

section intNorm

universe u v w

variable (R S K L) [CommRing R] [CommRing S] [Field K] [Field L]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] [IsSeparable K L]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [IsSeparable (FractionRing R) (FractionRing S)]

instance : IsIntegralClosure S R (FractionRing S) :=
  isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
instance : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
instance : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰

noncomputable
def Algebra.intNormAux (R S K L) [CommRing R] [CommRing S] [Field K] [Field L]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] [IsSeparable K L] :
    S →* R where
  toFun := fun s ↦ IsIntegralClosure.mk' (R := R) R (Algebra.norm K (algebraMap S L s))
    (isIntegral_norm K <| map_isIntegral (IsScalarTower.toAlgHom R S L)
      (IsIntegralClosure.isIntegral R L s))
  map_one' := by simp
  map_mul' := fun x y ↦ by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

lemma Algebra.map_intNormAux {R S K L} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain S] [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] [IsSeparable K L] (x : S) :
    algebraMap R K (Algebra.intNormAux R S K L x) = Algebra.norm K (algebraMap S L x) := by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

open nonZeroDivisors

example (R S) [CommRing R] [CommRing S] [IsIntegrallyClosed R] [CharZero R]
    [Algebra R S] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [Module.Finite R S]
    [IsIntegrallyClosed S] : IsSeparable (FractionRing R) (FractionRing S) :=
  inferInstance

noncomputable
def Algebra.intNorm (R S) [CommRing R] [CommRing S] [IsIntegrallyClosed R]
    [Algebra R S] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [IsSeparable (FractionRing R) (FractionRing S)] : S →* R := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  exact Algebra.intNormAux R S (FractionRing R) (FractionRing S)

lemma Algebra.algebraMap_intNorm {R S K L} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsIntegralClosure S R L] [IsIntegrallyClosed S] [IsFractionRing R K] [FiniteDimensional K L]
    [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsSeparable (FractionRing R) (FractionRing S)] (x : S) :
    algebraMap R K (Algebra.intNorm R S x) = Algebra.norm K (algebraMap S L x) := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  apply (FractionRing.algEquiv R K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intNorm, Algebra.map_intNormAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv S L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv R K).toRingEquiv
    (FractionRing.algEquiv S L).toRingEquiv
  apply IsLocalization.ringHom_ext R⁰
  simp only [AlgEquiv.toRingEquiv_eq_coe, ← AlgEquiv.coe_ringHom_commutes, RingHom.comp_assoc,
    AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq, RingHom.comp_assoc]

@[simp]
lemma Algebra.algebraMap_intNorm_fractionRing {R S} [CommRing R] [CommRing S]
    [IsIntegrallyClosed R] [Algebra R S]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [IsSeparable (FractionRing R) (FractionRing S)] (x : S) :
    algebraMap R (FractionRing R) (Algebra.intNorm R S x) =
      Algebra.norm (FractionRing R) (algebraMap S (FractionRing S)  x) := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  exact Algebra.map_intNormAux x

lemma Algebra.intNorm_eq_norm (R S) [CommRing R] [CommRing S] [IsIntegrallyClosed R] [Algebra R S]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [Module.Free R S]
    [IsSeparable (FractionRing R) (FractionRing S)] : Algebra.intNorm R S = Algebra.norm R := by
  ext x
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
  apply IsFractionRing.injective R (FractionRing R)
  rw [Algebra.algebraMap_intNorm_fractionRing, Algebra.norm_localization R R⁰]

variable {R S}

@[simp]
lemma Algebra.intNorm_zero : Algebra.intNorm R S 0 = 0 := by
  apply (IsFractionRing.injective R (FractionRing R))
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_zero]

@[simp]
lemma Algebra.intNorm_eq_zero : Algebra.intNorm R S x = 0 ↔ x = 0 := by
  rw [← (IsFractionRing.injective R (FractionRing R)).eq_iff,
    ← (IsFractionRing.injective S (FractionRing S)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]

lemma Algebra.intNorm_ne_zero : Algebra.intNorm R S x ≠ 0 ↔ x ≠ 0 := by simp

lemma Algebra.intNorm_eq_of_isLocalization (M : Submonoid R) (hM : M ≤ R⁰)
    {Rₘ Sₘ} [CommRing Rₘ] [CommRing Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
    [Algebra R Rₘ] [Algebra S Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [Module.Finite R S] [IsIntegrallyClosed S]
    [IsDomain Rₘ] [IsDomain Sₘ] [NoZeroSMulDivisors Rₘ Sₘ] [Module.Finite Rₘ Sₘ]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rₘ] [IsIntegrallyClosed Sₘ]
    [IsSeparable (FractionRing Rₘ) (FractionRing Sₘ)] (x : S) :
    algebraMap R Rₘ (Algebra.intNorm R S x) = Algebra.intNorm Rₘ Sₘ (algebraMap S Sₘ x) := by
  let K := FractionRing R
  let f : Rₘ →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := f.toAlgebra
  have : IsScalarTower R Rₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  let L := FractionRing S
  let g : Sₘ →+* L := IsLocalization.map _ (M := algebraMapSubmonoid S M) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _)))
  letI := g.toAlgebra
  have : IsScalarTower S Sₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := ((algebraMap K L).comp f).toAlgebra
  haveI : IsScalarTower Rₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rₘ Sₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Sₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid S M) Sₘ L
  haveI : IsIntegralClosure S R L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (A := S)))
  haveI : FiniteDimensional K L := Module.Finite_of_isLocalization R S _ _ R⁰
  haveI : IsIntegralClosure Sₘ Rₘ L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := Rₘ) (A := Sₘ))
  apply IsFractionRing.injective Rₘ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm_fractionRing,
    Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply]

end intNorm

section SpanNorm

namespace Ideal

open Submodule

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable [IsIntegrallyClosed R] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
    [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [IsSeparable (FractionRing R) (FractionRing S)]

/-- `Ideal.spanIntNorm R (I : Ideal S)` is the ideal generated by mapping `Algebra.norm R` over `I`.

See also `Ideal.relNorm`.
-/
def spanIntNorm (I : Ideal S) : Ideal R :=
  Ideal.span (Algebra.intNorm R S '' (I : Set S))

@[simp]
theorem spanIntNorm_bot [Nontrivial S] [Module.Free R S] [Module.Finite R S] :
    spanIntNorm R (⊥ : Ideal S) = ⊥ := span_eq_bot.mpr fun x hx => by simpa using hx

variable {R}

@[simp]
theorem spanIntNorm_eq_bot_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    {I : Ideal S} : spanIntNorm R I = ⊥ ↔ I = ⊥ := by
  simp only [spanIntNorm, span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Algebra.intNorm_eq_zero, @eq_bot_iff _ _ _ I, SetLike.le_def]
  rfl

variable (R)

theorem intNorm_mem_spanIntNorm {I : Ideal S} (x : S) (hx : x ∈ I) :
    Algebra.intNorm R S x ∈ I.spanIntNorm R :=
  subset_span (Set.mem_image_of_mem _ hx)

@[simp]
theorem spanIntNorm_singleton {r : S} :
    spanIntNorm R (span ({r} : Set S)) = span {Algebra.intNorm R S r} :=
  le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          exact map_dvd _ (mem_span_singleton.mp hx')))
    ((span_singleton_le_iff_mem _).mpr (intNorm_mem_spanIntNorm _ _ (mem_span_singleton_self _)))

@[simp]
theorem spanIntNorm_top : spanIntNorm R (⊤ : Ideal S) = ⊤ := by
  rw [← Ideal.span_singleton_one, spanIntNorm_singleton]
  simp

theorem map_spanIntNorm (I : Ideal S) {T : Type*} [CommRing T] (f : R →+* T) :
    map f (spanIntNorm R I) = span (f ∘ Algebra.intNorm R S '' (I : Set S)) := by
  rw [spanIntNorm, map_span, Set.image_image]
  rfl

@[mono]
theorem spanIntNorm_mono {I J : Ideal S} (h : I ≤ J) : spanIntNorm R I ≤ spanIntNorm R J :=
  Ideal.span_mono (Set.monotone_image h)

theorem spanIntNorm_localization (I : Ideal S) (M : Submonoid R) (hM : M ≤ R⁰)
    {Rₘ : Type*} (Sₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
    [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [IsIntegrallyClosed Rₘ] [IsDomain Rₘ] [IsDomain Sₘ] [NoZeroSMulDivisors Rₘ Sₘ]
    [Module.Finite Rₘ Sₘ] [IsIntegrallyClosed Sₘ]
    [IsSeparable (FractionRing Rₘ) (FractionRing Sₘ)] :
    spanIntNorm Rₘ (I.map (algebraMap S Sₘ)) = (spanIntNorm R I).map (algebraMap R Rₘ) := by
  let K := FractionRing R
  let f : Rₘ →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := f.toAlgebra
  have : IsScalarTower R Rₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  let L := FractionRing S
  let g : Sₘ →+* L := IsLocalization.map _ (M := Algebra.algebraMapSubmonoid S M) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _)))
  letI := g.toAlgebra
  have : IsScalarTower S Sₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := ((algebraMap K L).comp f).toAlgebra
  haveI : IsScalarTower Rₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rₘ Sₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Sₘ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₘ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid S M) Sₘ L
  haveI : IsIntegralClosure Sₘ Rₘ L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := Rₘ) (A := Sₘ))
  cases h : subsingleton_or_nontrivial R
  · haveI := IsLocalization.unique R Rₘ M
    simp
  rw [map_spanIntNorm]
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · rintro a' ha'
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanIntNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    refine ⟨⟨Algebra.intNorm R S a, intNorm_mem_spanIntNorm _ _ ha⟩,
      ⟨s ^ FiniteDimensional.finrank K L, pow_mem hs _⟩, ?_⟩
    simp only [Submodule.coe_mk, Subtype.coe_mk, map_pow] at has ⊢
    apply_fun algebraMap _ L at has
    apply_fun Algebra.norm K at has
    simp only [_root_.map_mul, IsScalarTower.algebraMap_apply R Rₘ Sₘ] at has
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L,
      Algebra.norm_algebraMap] at has
    apply IsFractionRing.injective Rₘ K
    simp only [_root_.map_mul, map_pow]
    rwa [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm (L := L)]
  · intro a ha
    rw [Set.mem_preimage, Function.comp_apply, Algebra.intNorm_eq_of_isLocalization
      (R := R) (S := S) M hM (Rₘ := Rₘ) (Sₘ := Sₘ)]
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))

theorem spanIntNorm_mul_spanIntNorm_le (I J : Ideal S) :
    spanIntNorm R I * spanIntNorm R J ≤ spanIntNorm R (I * J) := by
  rw [spanIntNorm, spanIntNorm, spanIntNorm, Ideal.span_mul_span', ← Set.image_mul]
  refine Ideal.span_mono (Set.monotone_image ?_)
  rintro _ ⟨x, y, hxI, hyJ, rfl⟩
  exact Ideal.mul_mem_mul hxI hyJ

/-- This condition `eq_bot_or_top` is equivalent to being a field.
However, `Ideal.spanIntNorm_mul_of_field` is harder to apply since we'd need to upgrade a `CommRing R`
instance to a `Field R` instance. -/
theorem spanIntNorm_mul_of_bot_or_top [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    (eq_bot_or_top : ∀ I : Ideal R, I = ⊥ ∨ I = ⊤) (I J : Ideal S) :
    spanIntNorm R (I * J) = spanIntNorm R I * spanIntNorm R J := by
  refine le_antisymm ?_ (spanIntNorm_mul_spanIntNorm_le R _ _)
  cases' eq_bot_or_top (spanIntNorm R I) with hI hI
  · rw [hI, spanIntNorm_eq_bot_iff.mp hI, bot_mul, spanIntNorm_bot]
    exact bot_le
  rw [hI, Ideal.top_mul]
  cases' eq_bot_or_top (spanIntNorm R J) with hJ hJ
  · rw [hJ, spanIntNorm_eq_bot_iff.mp hJ, mul_bot, spanIntNorm_bot]
  rw [hJ]
  exact le_top

variable [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]

variable [Module.Finite R S] [Module.Free R S]

open Polynomial nonZeroDivisors in
lemma NoZeroSMulDivisors_of_isLocalization (R S Rₚ Sₚ) [CommRing R] [CommRing S] [CommRing Rₚ]
    [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R) (hM : M ≤ R⁰)
    [IsLocalization M Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ] [NoZeroSMulDivisors R S]
    [IsDomain S] :
    NoZeroSMulDivisors Rₚ Sₚ := by
  have e : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _))
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors S e
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M)
  · apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [NoZeroSMulDivisors.iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
    RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective M x
  simp only [RingHom.algebraMap_toAlgebra, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    Subtype.exists, exists_prop, this] at hx ⊢
  obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
  simp only [← _root_.map_mul,
    (injective_iff_map_eq_zero' _).mp (NoZeroSMulDivisors.algebraMap_injective R S)] at H
  refine ⟨a, ha, H⟩

theorem IsLocalization.AtPrime.PID_of_dedekind_domain {A} [CommRing A]
    [IsDedekindDomain A]
    (P : Ideal A) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsPrincipalIdealRing Aₘ := by
  classical
  letI : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  letI : LocalRing Aₘ := IsLocalization.AtPrime.localRing Aₘ P
  by_cases h : IsField Aₘ
  · letI := h.toField; infer_instance
  · haveI := ((DiscreteValuationRing.TFAE Aₘ ‹_›).out 0 2).mpr
        (IsLocalization.AtPrime.isDedekindDomain A P _)
    exact this.toIsPrincipalIdealRing

/-- Multiplicativity of `Ideal.spanIntNorm`. simp-normal form is `map_mul (Ideal.relNorm R)`. -/
theorem spanIntNorm_mul (I J : Ideal S) :
    spanIntNorm R (I * J) = spanIntNorm R I * spanIntNorm R J := by
  classical
  nontriviality R
  cases subsingleton_or_nontrivial S
  · have : ∀ I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    simp [this I, this J, this (I * J)]
  refine eq_of_localization_maximal ?_
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [spanIntNorm_mul_of_bot_or_top]
    intro I
    refine or_iff_not_imp_right.mpr fun hI => ?_
    exact (hP.eq_of_le hI bot_le).symm
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let Sₚ := Localization P'
  letI : Algebra Rₚ Sₚ := localizationAlgebra P.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain Sₚ := IsLocalization.isDomain_localization h
  haveI : IsDedekindDomain Sₚ := IsLocalization.isDedekindDomain S h _
  haveI : IsPrincipalIdealRing Sₚ :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P hP0
  haveI := isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors Rₚ
  haveI := NoZeroSMulDivisors_of_isLocalization R S Rₚ Sₚ _ P.primeCompl_le_nonZeroDivisors
  haveI := Module.Finite_of_isLocalization R S Rₚ Sₚ P.primeCompl
  let L := FractionRing S
  let g : Sₚ →+* L := IsLocalization.map _ (M := P') (T := S⁰) (RingHom.id S) h
  letI := g.toAlgebra
  haveI : IsScalarTower S Sₚ (FractionRing S) := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHom.comp_id])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    P' Sₚ (FractionRing S)
  haveI : IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) := by
    haveI : IsScalarTower R Rₚ (FractionRing R) := IsScalarTower.of_algebraMap_eq'
      (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_comp])
    letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      P.primeCompl Rₚ (FractionRing R)
    apply IsSeparable_of_equiv_equiv (FractionRing.algEquiv Rₚ (FractionRing R)).symm.toRingEquiv
      (FractionRing.algEquiv Sₚ (FractionRing S)).symm.toRingEquiv
    apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
    simp only [IsScalarTower.algebraMap_apply R Rₚ (FractionRing R), AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply S Sₚ L]
    simp only [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R Rₚ (FractionRing Rₚ), ← IsScalarTower.algebraMap_apply Rₚ,
      ← IsScalarTower.algebraMap_apply]
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (S := S)
    (Rₘ := Localization.AtPrime P) (Sₘ := Localization P') _ _ P.primeCompl_le_nonZeroDivisors]
  rw [← (I.map _).span_singleton_generator, ← (J.map _).span_singleton_generator,
    span_singleton_mul_span_singleton, spanIntNorm_singleton, spanIntNorm_singleton,
      spanIntNorm_singleton, span_singleton_mul_span_singleton, _root_.map_mul]

/-- Multiplicativity of `Ideal.spanIntNorm`. simp-normal form is `map_mul (Ideal.relNorm R)`. -/
theorem spanIntNorm_map (I : Ideal R) :
    spanIntNorm R (I.map (algebraMap R S)) =
      I ^ (FiniteDimensional.finrank (FractionRing R) (FractionRing S)) := by
  classical
  nontriviality R
  nontriviality S
  refine eq_of_localization_maximal ?_
  intro P hPd
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let Sₚ := Localization P'
  letI : Algebra Rₚ Sₚ := localizationAlgebra P.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain Sₚ := IsLocalization.isDomain_localization h
  haveI : IsDedekindDomain Sₚ := IsLocalization.isDedekindDomain S h _
  haveI : IsPrincipalIdealRing Rₚ := IsLocalization.AtPrime.PID_of_dedekind_domain P Rₚ
  haveI := isIntegrallyClosed_of_isLocalization P.primeCompl P.primeCompl_le_nonZeroDivisors Rₚ
  haveI := NoZeroSMulDivisors_of_isLocalization R S Rₚ Sₚ _ P.primeCompl_le_nonZeroDivisors
  haveI := Module.Finite_of_isLocalization R S Rₚ Sₚ P.primeCompl
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
  letI := ((algebraMap K L).comp f).toAlgebra
  haveI : IsScalarTower Rₚ K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rₚ Sₚ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext P.primeCompl
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Sₚ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₚ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  haveI : IsIntegralClosure Sₚ Rₚ L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := Rₚ) (A := Sₚ))
  haveI : IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) := by
    apply IsSeparable_of_equiv_equiv (FractionRing.algEquiv Rₚ (FractionRing R)).symm.toRingEquiv
      (FractionRing.algEquiv Sₚ (FractionRing S)).symm.toRingEquiv
    apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
    simp only [IsScalarTower.algebraMap_apply R Rₚ (FractionRing R), AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply R S L,
      IsScalarTower.algebraMap_apply S Sₚ L]
    simp only [← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R Rₚ (FractionRing Rₚ), ← IsScalarTower.algebraMap_apply Rₚ,
      ← IsScalarTower.algebraMap_apply]
  haveI : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (S := S)
    (Rₘ := Localization.AtPrime P) (Sₘ := Localization P') _ _ P.primeCompl_le_nonZeroDivisors]
  rw [Ideal.map_pow, I.map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R Rₚ Sₚ,
    ← I.map_map, ← (I.map _).span_singleton_generator, Ideal.map_span, Set.image_singleton,
    spanIntNorm_singleton, Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply Rₚ K L, Algebra.norm_algebraMap, map_pow]


end Ideal

end SpanNorm
