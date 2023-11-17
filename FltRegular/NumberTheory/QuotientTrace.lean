import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalProperties
import Mathlib.NumberTheory.RamificationInertia
import FltRegular.NumberTheory.AuxLemmas
/-!

## Main Definition & Result
- `Algebra.intTrace`:
  The trace map on `Frac(B)/Frac(A)` restricted onto `B → A` (under suitable conditions).
- `trace_quotient_eq_trace_localization_quotient`:
  The trace map on `B → A` coincides with the trace map on `B⧸pB → A⧸p`.

-/
section LocalRing

variable {R S} [CommRing R] [CommRing S] [Algebra R S] [LocalRing R] [Module.Free R S] [Module.Finite R S]
variable {p : Ideal R} [p.IsMaximal] [LocalRing R]

open LocalRing FiniteDimensional

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) (maximalIdeal R)
attribute [local instance] Ideal.Quotient.field

theorem quotient_span_eq_top_iff_span_eq_top_of_localRing (s : Set S) :
    Submodule.span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔
    Submodule.span R s = ⊤ := by
  have H : (Submodule.span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
    (Submodule.span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS))
  · rw [Submodule.map_span, ← Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]
    rfl
  constructor
  · intro hs
    rw [← top_le_iff]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [sup_of_le_right le_top, Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS)) =
        Submodule.restrictScalars R pS
      · ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this, ← Submodule.comap_map_eq, Submodule.mem_comap, ← H, hs]
      trivial
  · intro hs
    rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective,
      Submodule.restrictScalars_eq_top_iff] at H

theorem finrank_quotient_map_of_localRing :
    finrank (R ⧸ p) (S ⧸ pS) = finrank R S := by
  classical
  have : Module.Finite R (S ⧸ pS) := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R S (S ⧸ pS)).toLinearMap (Ideal.Quotient.mk_surjective (I := pS))
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top (IsScalarTower.toAlgHom R S (S ⧸ pS) ∘ b)
    rw [Set.range_comp]
    apply (quotient_span_eq_top_iff_span_eq_top_of_localRing _).mpr b.span_eq
  · let b := Module.Free.chooseBasis (R ⧸ p) (S ⧸ pS)
    choose b' hb' using fun i ↦ Ideal.Quotient.mk_surjective (b i)
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top b'
    apply (quotient_span_eq_top_iff_span_eq_top_of_localRing _).mp
    rw [← Set.range_comp, show Ideal.Quotient.mk pS ∘ b' = ⇑b from funext hb']
    exact b.span_eq

noncomputable
def basisQuotientOfLocalRing {ι} [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b) (by
    rw [Set.range_comp]
    exact ((quotient_span_eq_top_iff_span_eq_top_of_localRing _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map_of_localRing, finrank_eq_card_basis b])

open BigOperators

lemma basisQuotientOfLocalRing_apply {ι} [Fintype ι] (b : Basis ι R S) (i) :
    (basisQuotientOfLocalRing b) i = Ideal.Quotient.mk pS (b i) := by
  delta basisQuotientOfLocalRing
  rw [coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply]

lemma basisQuotientOfLocalRing_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) :
  (basisQuotientOfLocalRing b).repr (Ideal.Quotient.mk pS x) i =
    Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotientOfLocalRing b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.total_eq_fintype_total_apply _ (R ⧸ p), Fintype.total_apply]
  simp only [Function.comp_apply, basisQuotientOfLocalRing_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]

lemma Algebra.trace_quotient_mk (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.trace R S x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Basis ι R S := Module.Free.chooseBasis R S
  rw [trace_eq_matrix_trace b, trace_eq_matrix_trace (basisQuotientOfLocalRing b)]
  show _ = (Ideal.Quotient.mk p).toAddMonoidHom _
  rw [AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [leftMulMatrix_apply, coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotientOfLocalRing_apply, LinearMap.mul_apply', RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.mapMatrix_apply, AddMonoidHom.coe_coe, Matrix.map_apply, ← map_mul,
    basisQuotientOfLocalRing_repr]

end LocalRing

section intTrace

noncomputable
def Algebra.intTraceAux (R S K L) [CommRing R] [CommRing S] [Field K] [Field L]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] :
    S →ₗ[R] R :=
  (IsIntegralClosure.equiv R (integralClosure R K) K R).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars R).comp
      (IsScalarTower.toAlgHom R S L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure R K) (fun x ↦ isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral R L x))))

lemma Algebra.map_intTraceAux {R S K L} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain S] [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [IsFractionRing R K] [FiniteDimensional K L] (x : S) :
    algebraMap R K (Algebra.intTraceAux R S K L x) = Algebra.trace K L (algebraMap S L x) :=
  IsIntegralClosure.algebraMap_equiv R (integralClosure R K) K R _

open nonZeroDivisors

noncomputable
def Algebra.intTrace (R S) [CommRing R] [CommRing S] [IsIntegrallyClosed R]
    [Algebra R S] [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] : S →ₗ[R] R := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite _ _)
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  exact Algebra.intTraceAux R S (FractionRing R) (FractionRing S)

lemma Algebra.algebraMap_intTrace {R S K L} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [Algebra R S] [Algebra R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [IsIntegralClosure S R L] [IsIntegrallyClosed S] [IsFractionRing R K] [FiniteDimensional K L]
    [NoZeroSMulDivisors R S] [hRS : Module.Finite R S] (x : S) :
    algebraMap R K (Algebra.intTrace R S x) = Algebra.trace K L (algebraMap S L x) := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  apply (FractionRing.algEquiv R K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intTrace, Algebra.map_intTraceAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv S L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv R K).toRingEquiv
    (FractionRing.algEquiv S L).toRingEquiv
  apply IsLocalization.ringHom_ext R⁰
  simp only [AlgEquiv.toRingEquiv_eq_coe, ← AlgEquiv.coe_ringHom_commutes, RingHom.comp_assoc,
    AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq, RingHom.comp_assoc]

lemma Algebra.algebraMap_intTrace_fractionRing {R S} [CommRing R] [CommRing S]
    [IsIntegrallyClosed R] [Algebra R S]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] (x : S) :
    algebraMap R (FractionRing R) (Algebra.intTrace R S x) =
      Algebra.trace (FractionRing R) (FractionRing S) (algebraMap S _ x) := by
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S)))
  haveI : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite_of_isLocalization R S _ _ R⁰
  exact Algebra.map_intTraceAux x

lemma Algebra.intTrace_eq_trace (R S) [CommRing R] [CommRing S] [IsIntegrallyClosed R] [Algebra R S]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [hRS : Module.Finite R S]
    [IsIntegrallyClosed S] [Module.Free R S] : Algebra.intTrace R S = Algebra.trace R S := by
  ext x
  haveI : IsIntegralClosure S R (FractionRing S) :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S)))
  apply IsFractionRing.injective R (FractionRing R)
  rw [Algebra.algebraMap_intTrace_fractionRing, Algebra.trace_localization R R⁰]

open nonZeroDivisors

lemma Algebra.intTrace_eq_of_isLocalization {R S} [CommRing R] [CommRing S] [Algebra R S]
    {p : Ideal R} [p.IsMaximal] {Rₚ Sₚ} [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [Module.Finite R S] [IsIntegrallyClosed S]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [IsDomain Rₚ] [IsDomain Sₚ] [NoZeroSMulDivisors Rₚ Sₚ] [Module.Finite Rₚ Sₚ]
    [IsIntegrallyClosed R] [IsIntegrallyClosed Rₚ] [IsIntegrallyClosed Sₚ] (x : S) :
    algebraMap R Rₚ (Algebra.intTrace R S x) = Algebra.intTrace Rₚ Sₚ (algebraMap S Sₚ x) := by
  let K := FractionRing R
  let f : Rₚ →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) p.primeCompl_le_nonZeroDivisors
  letI := f.toAlgebra
  have : IsScalarTower R Rₚ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rₚ K
  let L := FractionRing S
  let g : Sₚ →+* L := IsLocalization.map _ (M := algebraMapSubmonoid S p.primeCompl) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _)))
  letI := g.toAlgebra
  have : IsScalarTower S Sₚ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  letI := ((algebraMap K L).comp f).toAlgebra
  haveI : IsScalarTower Rₚ K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Rₚ Sₚ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra (R := Sₚ), RingHom.comp_assoc,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S Sₚ,
      IsLocalization.map_comp, RingHom.comp_id, ← RingHom.comp_assoc, IsLocalization.map_comp,
      RingHom.comp_id, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  letI := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid S p.primeCompl) Sₚ L
  haveI : IsIntegralClosure S R L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S))
  haveI : IsLocalization (algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization' _ (FractionRing R) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := R) (B := S)))
  haveI : FiniteDimensional K L := Module.Finite_of_isLocalization R S _ _ R⁰
  haveI : IsIntegralClosure Sₚ Rₚ L :=
    isIntegralClosure_of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := Rₚ) (B := Sₚ))
  apply IsFractionRing.injective Rₚ K
  rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intTrace_fractionRing,
    Algebra.algebraMap_intTrace (L := L), ← IsScalarTower.algebraMap_apply]

end intTrace

section IsDedekindDomain

variable {R S} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} [p.IsMaximal]
variable {Rₚ Sₚ} [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
variable [LocalRing Rₚ] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [Algebra Rₚ Sₚ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

attribute [local instance] Ideal.Quotient.field

open LocalRing

variable (p Rₚ)

noncomputable
def equivQuotMaximalIdealOfIsLocalization : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ
    · rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstanceAs <| (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      ← map_mul, ← map_sub, ← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p,
      mul_left_comm,
      ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hs, mul_inv_cancel, mul_one,
      sub_self]
    rw [Ne.def, Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

lemma IsLocalization.AtPrime.map_eq_maximalIdeal :
    p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert congr_arg (Ideal.map (algebraMap R Rₚ))
    (IsLocalization.AtPrime.comap_maximalIdeal Rₚ p).symm
  rw [map_comap p.primeCompl]

lemma comap_map_eq_map_of_isLocalization_algebraMapSubmonoid :
    (Ideal.map (algebraMap R Sₚ) p).comap (algebraMap S Sₚ) = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← Ideal.map_map, eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : ∃ α ∉ p, α • x ∈ pS
  · have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul,
      IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def, e, Submonoid.coe_mul, mul_assoc, mul_comm _ x, hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ β * α = 1 + γ
  · obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel, sub_self]
      rwa [Ne.def, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel'_right]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def, smul_smul, hβ, add_smul, one_smul] at this
  refine (Submodule.add_mem_iff_left _ ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

variable (S Sₚ)

noncomputable
def quotMapEquivQuotMapMaximalIdealOfIsLocalization : S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rₚ, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      comap_map_eq_map_of_isLocalization_algebraMapSubmonoid]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ α * β = 1 + γ
    · obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel, sub_self]
        rwa [Ne.def, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel'_right]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ), Ideal.Quotient.algebraMap_eq,
      RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [h, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm, mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mul_cancel_left, ← map_mul, ← e, ← Algebra.smul_def, smul_smul,
      hβ, ← map_sub, add_smul, one_smul, add_comm x, add_sub_cancel]

lemma trace_quotient_eq_trace_localization_quotient (x) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      (equivQuotMaximalIdealOfIsLocalization p Rₚ).symm
        (Algebra.trace (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) (algebraMap S _ x)) := by
  have : IsScalarTower R (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ)
  · apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _), IsScalarTower.algebraMap_eq R Rₚ (Sₚ ⧸ _),
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Rₚ]
  rw [Algebra.trace_eq_of_equiv_equiv (equivQuotMaximalIdealOfIsLocalization p Rₚ)
    (quotMapEquivQuotMapMaximalIdealOfIsLocalization S p Rₚ Sₚ)]
  · congr
  · ext x
    simp only [equivQuotMaximalIdealOfIsLocalization, RingHom.quotientKerEquivOfSurjective,
      RingEquiv.coe_ringHom_trans, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk,
      quotMapEquivQuotMapMaximalIdealOfIsLocalization,
      Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

open nonZeroDivisors

lemma Algebra.trace_quotient_eq_of_isDedekindDomain
  [IsDedekindDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
  [Module.Finite R S] [IsIntegrallyClosed S] :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _))
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors S e
  haveI : NoZeroSMulDivisors Rₚ Sₚ := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    simp only [RingHom.algebraMap_toAlgebra, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
      mul_eq_zero, Subtype.exists, exists_prop] at hx ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
    simp only [(injective_iff_map_eq_zero' _).mp (NoZeroSMulDivisors.algebraMap_injective R S)] at H
    refine ⟨a, ha, H⟩
  haveI : Module.Finite Rₚ Sₚ := Module.Finite_of_isLocalization R S _ _ p.primeCompl
  haveI : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ e _
  have : IsPrincipalIdealRing Rₚ := by
    by_cases hp : p = ⊥
    · have : IsFractionRing R Rₚ
      · delta IsFractionRing
        convert inferInstanceAs (IsLocalization p.primeCompl Rₚ)
        ext; simp [hp, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      letI : Field Rₚ := IsFractionRing.toField R
      infer_instance
    · have := (IsDedekindDomain.isDedekindDomainDvr R).2 p hp inferInstance
      infer_instance
  haveI : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'

  apply (equivQuotMaximalIdealOfIsLocalization p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization (S := S) (p := p) (Rₚ := Rₚ) (Sₚ := Sₚ) x,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [equivQuotMaximalIdealOfIsLocalization, RingHom.quotientKerEquivOfSurjective,
    RingEquiv.coe_trans, Function.comp_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk]

end IsDedekindDomain
