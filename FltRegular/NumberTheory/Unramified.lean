import FltRegular.NumberTheory.GaloisPrime
import Mathlib.NumberTheory.KummerDedekind
import FltRegular.NumberTheory.Different
/-!
# Unramified extensions

## Main definition
- `IsUnramifiedAt`:
  `IsUnramifiedAt S p` states that every prime in `S` over `p` has ramification index `1`.
- `IsUnramified`:
  An extension is unramified if it is unramified at every (finite) primes.

## Main results
- `comap_map_eq_of_isUnramified`: If `K/L` is galois, `S/R` is unramified, then any
  ideal `I` fixed by `Gal(L/K) satisfies `(I ∩ R)S = I`.
- `isUnramifiedAt_of_Separable_minpoly`: If `L = K[α]` with `α` integral over `R`, and `f'(α) mod p`
  is separable for some ideal `p` of `R` (with `f` being the minpoly of `α` over `R`), then `S/R` is
  unramified at `p`.
-/
open BigOperators UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (R K S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L] -- [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] -- [IsNoetherian R S]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

def IsUnramifiedAt {R} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) : Prop :=
  ∀ P ∈ primesOver S p, Ideal.ramificationIdx (algebraMap R S) p P = 1

/-- TODO: Link this to `FormallyUnramified`. -/
-- Should we name this `IsUnramifiedAtFinitePrimes`?
class IsUnramified (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  isUnramifiedAt : ∀ (p : Ideal R) [p.IsPrime] (_ : p ≠ ⊥), IsUnramifiedAt S p

variable {R} {S}

lemma prod_primesOverFinset_of_isUnramified [IsUnramified R S] [IsDedekindDomain S]
    [NoZeroSMulDivisors R S] (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    ∏ P in primesOverFinset S p, P = p.map (algebraMap R S) := by
  classical
  have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective
    (NoZeroSMulDivisors.iff_algebraMap_injective.mp ‹_›)).not.mpr hp
  rw [← associated_iff_eq.mp (factors_pow_count_prod hpbot')]
  apply Finset.prod_congr rfl
  intros P hP
  convert (pow_one _).symm
  rw [← Finset.mem_coe, coe_primesOverFinset S p hp] at hP
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count hpbot' hP.1
    (ne_bot_of_mem_primesOver hp hP)]
  exact IsUnramified.isUnramifiedAt _ hp _ hP

lemma comap_map_eq_of_isUnramified [IsGalois K L] [IsUnramified R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K S L σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S)
  · refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := NoZeroSMulDivisors.iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := mt (Ideal.eq_bot_of_comap_eq_bot
    (IsIntegralClosure.isIntegral_algebra R L)) hIbot
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) → ∃ P ≥ I, P ∈ primesOver S p
  · intro p ⟨hp₁, hp₂⟩
    exact Ideal.exists_ideal_over_prime_of_isIntegral''
      (IsIntegralClosure.isIntegral_algebra R L) _ _ hp₂
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p in (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := (Ideal.comap (algebraMap R S) : Ideal S → Ideal R))
    (t := (factors (I.comap (algebraMap R S))).toFinset)]
  apply Finset.prod_congr rfl
  intros p hp
  simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
    Ideal.mem_normalizedFactors_iff hIbot'] at hp
  have hpbot : p ≠ ⊥ := fun hp' ↦ hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
  have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hRS).not.mpr hpbot
  have := hp.1
  rw [← prod_primesOverFinset_of_isUnramified p hpbot, ← Finset.prod_pow]
  apply Finset.prod_congr
  · ext P
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hpbot', Finset.filter_congr_decidable,
      Ideal.mem_normalizedFactors_iff hIbot, and_imp, Finset.mem_filter]
    rw [← Finset.mem_coe, coe_primesOverFinset S p hpbot]
    refine ⟨fun H ↦ ⟨H.1.1, H.2⟩, fun H ↦ ⟨⟨H.1, ?_⟩, H.2⟩⟩
    have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K S L (h𝔓' _ hp) H
    rw [← hσ, ← hI σ]
    exact Ideal.comap_mono (h𝔓 _ hp)
  · intro P hP
    rw [← Finset.mem_coe, coe_primesOverFinset S p hpbot] at hP
    congr
    rw [dif_pos hp]
    apply PartENat.natCast_inj.mp
    rw [← normalize_eq P, factors_eq_normalizedFactors,
      ← multiplicity_eq_count_normalizedFactors
        (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
      ← normalize_eq (𝔓 p hp), ← multiplicity_eq_count_normalizedFactors
        (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
      multiplicity.multiplicity_eq_multiplicity_iff]
    intro n
    have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K S L (h𝔓' _ hp) hP
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

open scoped Classical in
lemma isUnramifiedAt_iff_normalizedFactors_nodup [NoZeroSMulDivisors R S] [IsDedekindDomain S]
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    IsUnramifiedAt S p ↔ (normalizedFactors (p.map (algebraMap R S))).Nodup := by
  simp_rw [Multiset.nodup_iff_count_eq_one, ← Multiset.mem_toFinset,
    ← factors_eq_normalizedFactors]
  show _ ↔ ∀ P ∈ (primesOverFinset S p : Set (Ideal S)), _
  simp_rw [IsUnramifiedAt, coe_primesOverFinset S p hp]
  refine forall₂_congr (fun P hP ↦ ?_)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count]
  · exact (Ideal.map_eq_bot_iff_of_injective
      (NoZeroSMulDivisors.algebraMap_injective R S)).not.mpr hp
  · exact hP.1
  · exact ne_bot_of_mem_primesOver hp hP

section KummerDedekind

end KummerDedekind

attribute [local instance] Ideal.Quotient.field in
lemma isUnramifiedAt_iff_SquareFree_minpoly [NoZeroSMulDivisors R S] [IsDedekindDomain S]
    (p : Ideal R) [hp : p.IsPrime] (hpbot : p ≠ ⊥) (x : S)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ p = ⊤) (hx' : IsIntegral R x) :
    IsUnramifiedAt S p ↔ Squarefree ((minpoly R x).map (Ideal.Quotient.mk p)) := by
  classical
  have := hp.isMaximal hpbot
  rw [isUnramifiedAt_iff_normalizedFactors_nodup p hpbot,
    KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
    this hpbot hx hx', Multiset.nodup_map_iff_of_injective, Multiset.nodup_attach,
    ← squarefree_iff_nodup_normalizedFactors (Polynomial.map_monic_ne_zero (minpoly.monic hx'))]
  exact Subtype.val_injective.comp
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
      this hpbot hx hx').symm.injective

lemma isUnramifiedAt_iff_SquareFree_minpoly_powerBasis [NoZeroSMulDivisors R S] [IsDedekindDomain S]
    (hRS : Algebra.IsIntegral R S) (pb : PowerBasis R S)
    (p : Ideal R) [p.IsPrime] (hpbot : p ≠ ⊥) :
    IsUnramifiedAt S p ↔ Squarefree ((minpoly R pb.gen).map (Ideal.Quotient.mk p)) := by
  rw [isUnramifiedAt_iff_SquareFree_minpoly p hpbot pb.gen _ (hRS _)]
  rw [conductor_eq_top_of_powerBasis, Ideal.comap_top, top_sup_eq]

open nonZeroDivisors Polynomial

attribute [local instance] Ideal.Quotient.field in
lemma isUnramifiedAt_of_Separable_minpoly' [IsSeparable K L]
    (p : Ideal R) [hp : p.IsPrime] (hpbot : p ≠ ⊥) (x : S)
    (hx' : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk p))) :
    IsUnramifiedAt S p := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have hRS : Function.Injective (algebraMap R S)
  · refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := NoZeroSMulDivisors.iff_algebraMap_injective.mpr hRS
  have := IsIntegralClosure.isNoetherian R K L S
  have := IsIntegralClosure.isDedekindDomain R K L S
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have := aeval_derivative_mem_differentIdeal R K S L x hx'
  have H : RingHom.comp (algebraMap (FractionRing R) (FractionRing S))
    ↑(FractionRing.algEquiv R K).symm.toRingEquiv =
      RingHom.comp ↑(FractionRing.algEquiv S L).symm.toRingEquiv (algebraMap K L)
  · apply IsLocalization.ringHom_ext R⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R S L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsSeparable (FractionRing R) (FractionRing S) := IsSeparable_of_equiv_equiv _ _ H
  have := hp.isMaximal hpbot

  intro P hP
  have := isMaximal_of_mem_primesOver hpbot hP
  apply le_antisymm
  · rw [← tsub_eq_zero_iff_le]
    by_contra H
    have hxP : aeval x (derivative (minpoly R x)) ∈ P
    · have : differentIdeal R S ≤ P
      · rw [← Ideal.dvd_iff_le]
        exact (dvd_pow_self _ H).trans (pow_sub_one_dvd_differentIdeal R S P _ hpbot
        (Ideal.dvd_iff_le.mpr <| Ideal.le_pow_ramificationIdx (p := p) (f := algebraMap R S)))
      exact this (aeval_derivative_mem_differentIdeal R K S L _ hx')
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hxP

    have := (separable_map (Ideal.quotientMap P (algebraMap R S) hP.2.ge)).mpr h
    rw [map_map, Ideal.quotientMap_comp_mk] at this
    obtain ⟨a, b, e⟩ := this
    apply_fun (aeval (Ideal.Quotient.mk P x)) at e
    simp only [← Ideal.Quotient.algebraMap_eq, ← map_map, derivative_map, map_add, map_mul,
      aeval_map_algebraMap, aeval_algebraMap, minpoly.aeval, map_zero, mul_zero, hxP, zero_add,
      coe_aeval_eq_eval, eval_one] at e
    exact zero_ne_one e
  · rwa [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count _
      (isMaximal_of_mem_primesOver hpbot hP).isPrime (ne_bot_of_mem_primesOver hpbot hP),
      Multiset.one_le_count_iff_mem, ← Multiset.mem_toFinset, ← primesOverFinset,
      ← Finset.mem_coe, coe_primesOverFinset _ p hpbot]
    rwa [ne_eq, Ideal.map_eq_bot_iff_of_injective hRS]

lemma isUnramifiedAt_of_Separable_minpoly [IsSeparable K L]
    (p : Ideal R) [hp : p.IsPrime] (hpbot : p ≠ ⊥) (x : L) (hx : IsIntegral R x)
    (hx' : Algebra.adjoin K {x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk p))) :
    IsUnramifiedAt S p := by
  rw [← IsIntegralClosure.algebraMap_mk' S x hx, minpoly.algebraMap_eq
    (IsIntegralClosure.algebraMap_injective S R L)] at h
  exact isUnramifiedAt_of_Separable_minpoly' K L p hpbot (IsIntegralClosure.mk' S x hx)
    (by rwa [IsIntegralClosure.algebraMap_mk']) h
