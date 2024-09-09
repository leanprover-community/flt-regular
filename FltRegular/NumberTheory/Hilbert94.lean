import FltRegular.NumberTheory.Unramified
import FltRegular.NumberTheory.Hilbert92
import FltRegular.NumberTheory.Hilbert90
import FltRegular.NumberTheory.IdealNorm
import FltRegular.NumberTheory.RegularPrimes
import Mathlib.NumberTheory.NumberField.ClassNumber

open scoped NumberField

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K]

open Polynomial

variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (hKL : FiniteDimensional.finrank K L = p)

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]

include hσ in
lemma comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ) (hβ : η * (galRestrict A K L B σ) β = β)
    (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by
  suffices (Ideal.span {β}).map
      (galRestrict A K L B σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β} by
    rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K L B σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = σ'
  obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
  rw [map_pow]
  induction n with
  | zero =>
    simp only [Nat.zero_eq, pow_zero, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, pow_succ] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH

variable [IsGalois K L]

include hσ in
open FiniteDimensional in
theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [IsUnramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  obtain ⟨β, hβ_zero, hβ⟩ := Hilbert90_integral (A := A) (B := B) σ hσ η hη
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have hβ' := comap_map_eq_of_isUnramified K L _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    apply hη'
    use a
    conv_rhs => enter [1]; rw [← hβ]
    rw [map_mul, ← AlgHom.coe_coe σ, ← algebraMap_galRestrictHom_apply A K L B σ a]
    refine (mul_div_cancel_right₀ _ ?_).symm
    · rw [ne_eq, (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
        (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
      exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩

open FiniteDimensional (finrank)

theorem Ideal.isPrincipal_pow_finrank_of_isPrincipal_map [IsDedekindDomain A] (I : Ideal A)
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI := IsIntegralClosure.isNoetherian A K L B
  haveI := IsIntegralClosure.isDedekindDomain A K L B
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB : Function.Injective (algebraMap A B) := by
    refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  rw [← NoZeroSMulDivisors.iff_algebraMap_injective] at hAB
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
    (FractionRing.algEquiv A K).symm.toRingEquiv =
      RingHom.comp (FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have hLK : finrank (FractionRing A) (FractionRing B) = finrank K L := by
    simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
      (Algebra.lift_rank_eq_of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
        (FractionRing.algEquiv B L).symm.toRingEquiv H).symm
  rw [← hLK, ← Ideal.spanIntNorm_map, ← (I.map (algebraMap A B)).span_singleton_generator,
    Ideal.spanIntNorm_singleton]
  exact ⟨⟨_, rfl⟩⟩

/-- This is the first part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then there is an ideal that capitulates in `K`. -/
theorem exists_not_isPrincipal_and_isPrincipal_map (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsUnramified (𝓞 K) (𝓞 L)] [h : IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧ (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')

/-- This is the second part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
  cyclic finite extension of number fields of odd prime degree,
  then the degree divides the class number of `K`. -/
theorem dvd_card_classGroup_of_isUnramified_isCyclic (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsUnramified (𝓞 K) (𝓞 L)] [IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by
  obtain ⟨I, hI, hI'⟩ := exists_not_isPrincipal_and_isPrincipal_map K L hKL hKL'
  letI := Fact.mk hKL
  rw [← Int.ofNat_dvd, (Nat.prime_iff_prime_int.mp hKL).irreducible.dvd_iff_not_coprime,
    Nat.isCoprime_iff_coprime]
  exact fun h ↦ hI (IsPrincipal_of_IsPrincipal_pow_of_Coprime _ _ h _
    (Ideal.isPrincipal_pow_finrank_of_isPrincipal_map _ hI'))
