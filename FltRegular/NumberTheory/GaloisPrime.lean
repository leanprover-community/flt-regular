import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Galois action on primes

## Main Result
- `exists_comap_galRestrict_eq`: The galois action on `primesOver` is transitive.

-/
open Ideal

section primesOver
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma ne_bot_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) :
    P ≠ ⊥ := by
  have :  P.LiesOver p := hP.2
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hp _

lemma isMaximal_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) : P.IsMaximal :=
  hP.1.isMaximal (ne_bot_of_mem_primesOver hp hP)

lemma prime_of_mem_primesOver [IsDedekindDomain S] [NoZeroSMulDivisors R S] {p : Ideal R}
    (hp : p ≠ ⊥) {P : Ideal S} (hP : P ∈ primesOver p S) : Prime P :=
  prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

end primesOver

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
  obtain ⟨σ, hσ⟩ := exists_map_eq_of_isGalois p P₂ P₁ K L
  refine ⟨(galRestrict R K L S).symm σ, ?_⟩
  simp only [MulEquiv.apply_symm_apply, ← hσ]
  refine comap_map_of_bijective _ (AlgEquiv.bijective σ)
