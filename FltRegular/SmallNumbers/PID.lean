module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# A principal ideal domain criterion for Galois number fields

This file packages a class-number bound and Kummer--Dedekind factorization into a criterion for the
ring of integers of a Galois number field to be a principal ideal domain.
-/

@[expose] public section

open Ideal NumberField Module NumberField.InfinitePlace Nat Real

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace RingOfIntegers

/-- A Galois number field has principal ring of integers when the ideals arising from all relevant
small primes satisfy the stated norm or principality alternative. -/
theorem PIDGalois [IsGalois ℚ K] {θ : 𝓞 K} (hθ : exponent θ = 1)
    (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) →
      haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P, ∃ hP : P ∈ monicFactorsMod θ p, ⌊(M K)⌋₊ < p ^ P.natDegree ∨
        Submodule.IsPrincipal
          ((Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm
            ⟨P, hP⟩).1) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp I hI hple ↦ ?_)
  obtain ⟨Q, hQ, hQalt⟩ := h p hpmem hp
  have : Fact (p.Prime) := ⟨hp⟩
  let J := (Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm ⟨Q, hQ⟩
  have := hI.1
  have := hI.2
  by_cases hbound : ⌊(M K)⌋₊ < p ^ (I.inertiaDeg ℤ)
  · linarith
  rw [← Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      (hθ ▸ hp.not_dvd_one) hQ,
    inertiaDeg_eq_of_isGaloisGroup (span {↑p}) J I Gal(K/ℚ)] at hQalt
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span ({↑p} : Set ℤ)) J I Gal(K/ℚ)
  exact (hQalt.resolve_left hbound).map_ringHom _

end RingOfIntegers
