module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

open Ideal NumberField Module NumberField.InfinitePlace Nat Real

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace RingOfIntegers

theorem PIDGalois [IsGalois ℚ K] {θ : 𝓞 K} (hθ : exponent θ = 1)
    (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) →
      haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P, ∃ hP : P ∈ monicFactorsMod θ p, ⌊(M K)⌋₊ < p ^ P.natDegree ∨
        Submodule.IsPrincipal
          ((Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm
            ⟨P, hP⟩).1) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp I hI hple ↦ ?_)
  obtain ⟨Q, hQ, H⟩ := h p hpmem hp
  have : Fact (p.Prime) := ⟨hp⟩
  let P := Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one) ⟨I, hI⟩
  let J := (Ideal.primesOverSpanEquivMonicFactorsMod (hθ ▸ hp.not_dvd_one)).symm ⟨Q, hQ⟩
  have := hI.1; have := hI.2
  by_cases h : ⌊(M K)⌋₊ < p ^ (I.inertiaDeg ℤ)
  · linarith
  rw [← Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (hθ ▸ hp.not_dvd_one) hQ, inertiaDeg_eq_of_isGaloisGroup (span {↑p}) J I Gal(K/ℚ)] at H
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span ({↑p} : Set ℤ)) J I Gal(K/ℚ)
  exact (H.resolve_left h).map_ringHom _

end RingOfIntegers
