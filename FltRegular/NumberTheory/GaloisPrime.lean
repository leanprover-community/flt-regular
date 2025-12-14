import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Galois action on primes

## Main Result
- `exists_comap_galRestrict_eq`: The galois action on `primesOver` is transitive.

-/
open Ideal

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
    {P₁ P₂ : Ideal S} (hP₁ : P₁ ∈ primesOver p S) (hP₂ : P₂ ∈ primesOver p S) :
    ∃ σ, P₁.comap (galRestrict R K L S σ) = P₂ := by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := hP₂.2
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let :  MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  have : IsGaloisGroup Gal(L/K) R S := IsGaloisGroup.of_isFractionRing _ _ _ K L
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup p P₂ P₁ Gal(L/K)
  exact ⟨σ, hσ ▸ comap_map_of_bijective _ (((galRestrict R K L S) σ).bijective)⟩
