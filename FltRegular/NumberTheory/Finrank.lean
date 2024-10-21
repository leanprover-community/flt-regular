import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization

open Module

section

universe u v

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

variable {R M}

variable [StrongRankCondition R] [Module.Finite R M]

instance torsion.module {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) := by
  letI : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      Nat.isUnit_iff, smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  exact inferInstanceAs (Module R (M ⧸ this))

end

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
variable [Module R M] (N : Submodule R M)

lemma FiniteDimensional.finrank_quotient_of_le_torsion (hN : N ≤ Submodule.torsion R M) :
    finrank R (M ⧸ N) = finrank R M := congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion hN)

lemma FiniteDimensional.finrank_map_of_le_torsion {M'} [AddCommGroup M'] [Module R M']
    (l : M →ₗ[R] M') [Module.Finite R N]
    (hN : N ⊓ LinearMap.ker l ≤ Submodule.torsion R M) : finrank R (N.map l) = finrank R N := by
  conv_lhs => rw [← N.range_subtype, ← LinearMap.range_comp,
    ← (LinearMap.quotKerEquivRange (l.comp N.subtype)).finrank_eq]
  apply FiniteDimensional.finrank_quotient_of_le_torsion
  rintro x hx
  obtain ⟨a, ha⟩ := hN ⟨x.prop, hx⟩
  exact ⟨a, Subtype.val_injective ha⟩

variable [Module.Finite R M]

lemma FiniteDimensional.finrank_of_surjective_of_le_torsion {M'} [AddCommGroup M'] [Module R M']
    (l : M →ₗ[R] M') (hl : Function.Surjective l)
    (hl' : LinearMap.ker l ≤ Submodule.torsion R M) : finrank R M' = finrank R M := by
  have := FiniteDimensional.finrank_map_of_le_torsion ⊤ l (inf_le_right.trans hl')
  rw [← LinearMap.range_eq_map l, LinearMap.range_eq_top.mpr hl] at this
  simpa only [finrank_top] using this

instance [IsDomain R] : NoZeroSMulDivisors R (M ⧸ Submodule.torsion R M) := by
  constructor
  intros c x hcx
  rw [or_iff_not_imp_left]
  intro hc
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hcx
  obtain ⟨n, hn⟩ := hcx
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submonoid.mk_smul, exists_prop]
  refine ⟨n * ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
  simpa [Submonoid.smul_def, smul_smul] using hn

instance [IsDomain R] [IsPrincipalIdealRing R] : Module.Free R (M ⧸ Submodule.torsion R M) :=
  Module.free_of_finite_type_torsion_free'

lemma FiniteDimensional.finrank_add_finrank_quotient [IsDomain R] (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N = finrank R M := by
  rw [← Cardinal.natCast_inj.{v}, Module.finrank_eq_rank, Nat.cast_add, Module.finrank_eq_rank,
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
