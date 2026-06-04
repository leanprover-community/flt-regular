module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Unramified extensions

## Main results
- `comap_map_eq_of_unramified`: If `K/L` is galois, `S/R` is unramified, then any
  ideal `I` fixed by `Gal(L/K)` satisfies `(I ∩ R)S = I`.
- `isUnramifiedAt_of_Separable_minpoly`: If `L = K[α]` with `α` integral over `R`, and
  `f'(α) mod p` is separable for the prime below `P`, then `S/R` is unramified at `P`.
-/

@[expose] public section
open UniqueFactorizationMonoid Ideal

attribute [local instance] FractionRing.liftAlgebra

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

variable {R} {S}

lemma prod_primesOverFinset_of_unramified [Algebra.Unramified R S] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    ∏ P ∈ IsDedekindDomain.primesOverFinset p S, P = p.map (algebraMap R S) := by
  classical
  have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective
      (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)).not.mpr hp
  rw [← associated_iff_eq.mp (factors_pow_count_prod hpbot')]
  apply Finset.prod_congr rfl
  intros P hP
  convert (pow_one _).symm
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp ‹_›
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp] at hP
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count hpbot' hP.1
    (ne_bot_of_mem_primesOver hp hP)]
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  rw [Ideal.ramificationIdx_eq_ramificationIdx' p P hp]
  exact Ideal.ramificationIdx'_eq_one P R

lemma comap_map_eq_of_unramified [IsGalois K L] [Algebra.Unramified R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  haveI : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hIbot
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) →
      ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp₁, hp₂⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hp₂
    exact ⟨P, hP1, hP2, ⟨hP3.symm⟩⟩
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p ∈ (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := (Ideal.comap (algebraMap R S) : Ideal S → Ideal R))
    (t := (factors (I.comap (algebraMap R S))).toFinset)]
  · apply Finset.prod_congr rfl
    intros p hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot'] at hp
    have hpbot : p ≠ ⊥ := fun hp' ↦ hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
    have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hRS).not.mpr
      hpbot
    have := hp.1
    rw [← prod_primesOverFinset_of_unramified p hpbot, ← Finset.prod_pow]
    have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot this
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hIbot, ← Finset.mem_coe,
          IsDedekindDomain.coe_primesOverFinset hpbot S]
      refine ⟨fun H ↦ ⟨H.1.1, ⟨H.2.symm⟩⟩, fun H ↦ ⟨⟨H.1, ?_⟩, ?_⟩⟩
      · have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) H
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (h𝔓 _ hp)
      · have := H.2.1
        rw [Ideal.under_def] at this
        exact this.symm
    · intro P hP
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hpbot S] at hP
      congr
      rw [dif_pos hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P,
        factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (𝔓 p hp), ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
          emultiplicity_eq_emultiplicity_iff]
      intro n
      have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot']
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩

section KummerDedekind

end KummerDedekind

open nonZeroDivisors Polynomial

omit [IsDedekindDomain R] in
lemma isUnramifiedAt_bot [IsDomain R] [IsDomain S] [Module.IsTorsionFree R S]
    [Algebra.IsIntegral R S] [Algebra.EssFiniteType R S] [CharZero R] :
    Algebra.IsUnramifiedAt R (⊥ : Ideal S) := by
  letI : Algebra (Localization.AtPrime (⊥ : Ideal R)) (Localization.AtPrime (⊥ : Ideal S)) :=
    Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  rw [Algebra.isUnramifiedAt_iff_map_eq R (⊥ : Ideal R) (⊥ : Ideal S)]
  constructor
  · haveI : CharZero (⊥ : Ideal R).ResidueField :=
      charZero_of_injective_algebraMap (R := R) (A := (⊥ : Ideal R).ResidueField) <| by
        rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    haveI : PerfectField (⊥ : Ideal R).ResidueField := by infer_instance
    haveI : Algebra.IsAlgebraic (⊥ : Ideal R).ResidueField
        (⊥ : Ideal S).ResidueField := by infer_instance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · haveI : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
      change IsLocalization (nonZeroDivisors S) (Localization.AtPrime (⊥ : Ideal S))
      rw [← Ideal.primeCompl_bot]
      infer_instance
    letI := IsFractionRing.toField S (K := Localization.AtPrime (⊥ : Ideal S))
    rw [Ideal.map_bot, IsLocalRing.maximalIdeal_eq_bot]

attribute [local instance] Ideal.Quotient.field in
lemma isUnramifiedAt_of_Separable_minpoly' [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : S)
    (hx' : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  have := IsIntegralClosure.isNoetherian R K L S
  have := IsIntegralClosure.isDedekindDomain R K L S
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  haveI : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  haveI : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := aeval_derivative_mem_differentIdeal R K L x hx'
  have H : RingHom.comp (algebraMap (FractionRing R) (FractionRing S))
    (FractionRing.algEquiv R K).symm.toRingEquiv =
      RingHom.comp (FractionRing.algEquiv S L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  rw [← not_dvd_differentIdeal_iff (A := R) (B := S) (P := P)]
  intro hPdiv
  have hxP : aeval x (derivative (minpoly R x)) ∈ P :=
    (Ideal.dvd_iff_le.mp hPdiv) (aeval_derivative_mem_differentIdeal R K L _ hx')
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hxP
  let p : Ideal R := P.under R
  haveI : p.IsPrime := inferInstance
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot R hPbot
  haveI : p.IsMaximal := (show p.IsPrime from inferInstance).isMaximal hpbot
  haveI : P.IsMaximal := (show P.IsPrime from inferInstance).isMaximal hPbot
  letI : IsScalarTower S (S ⧸ P) (S ⧸ P) := IsScalarTower.right
  have hle : p ≤ P.comap (algebraMap R S) := by
    change P.under R ≤ P.comap (algebraMap R S)
    rw [Ideal.under_def]
  have := (separable_map (Ideal.quotientMap P (algebraMap R S) hle)).mpr h
  rw [Polynomial.map_map, Ideal.quotientMap_comp_mk] at this
  obtain ⟨a, b, e⟩ := this
  apply_fun (aeval (Ideal.Quotient.mk P x)) at e
  simp_rw [← Ideal.Quotient.algebraMap_eq, ← Polynomial.map_map, derivative_map, map_add,
    _root_.map_mul, aeval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, hxP, map_zero,
    mul_zero, zero_add, map_one, zero_ne_one] at e

lemma isUnramifiedAt_of_Separable_minpoly [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : L) (hx : IsIntegral R x)
    (hx' : Algebra.adjoin K {x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  rw [← IsIntegralClosure.algebraMap_mk' S x hx, minpoly.algebraMap_eq
    (IsIntegralClosure.algebraMap_injective S R L)] at h
  exact isUnramifiedAt_of_Separable_minpoly' K L P hPbot (IsIntegralClosure.mk' S x hx)
    (by rwa [IsIntegralClosure.algebraMap_mk']) h
