import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

open Ideal NumberField Module NumberField.InfinitePlace Nat Real

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace RingOfIntegers

theorem PIDGalois [IsGalois ℚ K] {θ : 𝓞 K} (hθ : exponent θ = 1)
  (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P, ∃ hP : P ∈ monicFactorsMod θ p, ⌊(M K)⌋₊ < p ^ P.natDegree ∨
        Submodule.IsPrincipal ((Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm
          ⟨P, hP⟩).1) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp I hI hple ↦ ?_)
  obtain ⟨Q, hQ, H⟩ := h p hpmem hp
  have : Fact (p.Prime) := ⟨hp⟩
  let P := Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one) ⟨I, hI⟩
  let J := (Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm ⟨Q, hQ⟩
  have := hI.1; have := hI.2; have := J.2.1; have := J.2.2
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])
  by_cases h : ⌊(M K)⌋₊ < p ^ ((span ({↑p} : Set ℤ)).inertiaDeg I)
  · linarith
  rw [← Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (hθ ▸ hp.not_dvd_one) hQ, inertiaDeg_eq_of_isGalois _ J I ℚ K] at H
  obtain ⟨σ, rfl⟩ := exists_map_eq_of_isGalois (span ({↑p} : Set ℤ)) J I ℚ K
  exact (H.resolve_left h).map_ringHom σ

end RingOfIntegers
