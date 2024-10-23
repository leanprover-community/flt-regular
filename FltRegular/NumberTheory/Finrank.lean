import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Localization

open Module
section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

instance torsion.module : Module R (M ⧸ AddCommGroup.torsion M) := by
  letI : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      Nat.isUnit_iff, smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  exact inferInstanceAs (Module R (M ⧸ this))

end

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)

variable [Module.Finite R M]

lemma FiniteDimensional.finrank_add_finrank_quotient [IsDomain R] (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N = finrank R M := by
  rw [← Nat.cast_inj (R := Cardinal), Module.finrank_eq_rank, Nat.cast_add, Module.finrank_eq_rank,
    Submodule.finrank_eq_rank]
  exact HasRankNullity.rank_quotient_add_rank _

lemma FiniteDimensional.finrank_quotient [IsDomain R] (N : Submodule R M) :
    finrank R (M ⧸ N) = finrank R M - finrank R N := by
  rw [← FiniteDimensional.finrank_add_finrank_quotient N]
  omega

lemma FiniteDimensional.finrank_quotient' [IsDomain R] {S : Type*} [Ring S] [SMul R S] [Module S M]
    [IsScalarTower R S M] (N : Submodule S M) : finrank R (M ⧸ N) = finrank R M - finrank R N :=
  FiniteDimensional.finrank_quotient (N.restrictScalars R)

lemma FiniteDimensional.exists_of_finrank_lt [IsDomain R] (N : Submodule R M)
    (h : finrank R N < finrank R M) : ∃ m : M, ∀ r : R, r ≠ 0 → r • m ∉ N := by
  obtain ⟨s, hs, hs'⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := R) (M := M ⧸ N) le_rfl
  obtain ⟨v, hv⟩ : s.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero,
    hs, FiniteDimensional.finrank_quotient, tsub_eq_zero_iff_le, not_le]
  obtain ⟨v, rfl⟩ := N.mkQ_surjective v
  use v
  intro r hr
  have := linearIndependent_iff.mp hs' (Finsupp.single ⟨_, hv⟩ r)
  rw [Finsupp.linearCombination_single, Finsupp.single_eq_zero, ← LinearMap.map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact mt this hr
