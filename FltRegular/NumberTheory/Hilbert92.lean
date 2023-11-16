
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas

open scoped NumberField nonZeroDivisors
open FiniteDimensional

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma Hilbert92 [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {L : Type*} [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 L)ˣ, Algebra.norm K (η : L) = 1 ∧ ∀ ε : (𝓞 L)ˣ, (η : L) ≠ ε / (σ ε : L) := sorry
