
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.AuxLemmas
import FltRegular.NumberTheory.GaloisPrime

open scoped NumberField nonZeroDivisors
open FiniteDimensional

variable {K L : Type*} [Field K] [Field L] [NumberField K] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

--This is proved in #8599
theorem hilbert90 (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : ∀ (g h : (L ≃ₐ[K] L)), f (g * h) = g (f h) * f g) :
    ∃ β : Lˣ, ∀ g : (L ≃ₐ[K] L), f g * Units.map g β = β := by sorry

lemma Hilbert90 (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    (η : L) (hη : Algebra.norm K η = 1) : ∃ ε : L, η = ε / σ ε := by
  have hηunit : IsUnit η := sorry
  let ηu : Lˣ := hηunit.unit
  let E := AlgebraicClosure K
  have := Algebra.norm_eq_prod_embeddings K E η
  rw [hη] at this
  let f : (L ≃ₐ[K] L) → Lˣ := fun τ ↦ ηu ^ (Classical.choose (Subgroup.mem_zpowers_iff.1 (hσ τ)))
  have hf : ∀ (g h : (L ≃ₐ[K] L)), f (g * h) = g (f h) * f g := sorry
  have hfσ : f σ = ηu := sorry
  obtain ⟨ε, hε⟩ := hilbert90 f hf
  use ε
  specialize hε σ
  simp [hfσ] at hε
  nth_rewrite 1 [← hε]
  simp

variable {A B} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]
variable [IsIntegralClosure B A L] [IsDomain B]

lemma Hilbert90_integral (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    (η : B) (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K B L σ ε = ε := by
  haveI : NoZeroSMulDivisors A L := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization' A K L B
      (Algebra.isAlgebraic_iff_isIntegral.mpr <| Algebra.IsIntegral.of_finite (R := K) (B := L))
  obtain ⟨ε, hε⟩ := Hilbert90 σ hσ _ hη
  obtain ⟨x, y, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B A⁰) ε
  obtain ⟨t, ht, ht'⟩ := y.prop
  have : t • IsLocalization.mk' L x y = algebraMap _ _ x
  · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, map_zero, ne_eq, not_true, div_zero] at hε
    rw [hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · rw [eq_div_iff_mul_eq] at hε
    replace hε := congr_arg (t • ·) hε
    simp only at hε
    rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t, ← AlgHom.coe_coe,
      ← AlgHom.map_smul_of_tower, this] at hε
    apply IsIntegralClosure.algebraMap_injective B A L
    rw [map_mul, ← hε]
    congr 1
    exact algebraMap_galRestrictHom_apply A K B L σ x
    · intro e
      rw [(map_eq_zero _).mp e, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη
