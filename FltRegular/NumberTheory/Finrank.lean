import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.PID

open Module

section

universe u v

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

variable {R M}

variable [StrongRankCondition R] [Module.Finite R M]

lemma FiniteDimensional.finrank_add_finrank_quotient_le (N : Submodule R M) :
    finrank R N + finrank R (M ⧸ N) ≤ finrank R M := by
  by_cases h : Subsingleton R
  · rw [finrank_zero_iff.2 (Module.subsingleton R _), finrank_zero_iff.2 (Module.subsingleton R _),
      finrank_zero_iff.2 (Module.subsingleton R _)]
  rw [not_subsingleton_iff_nontrivial] at h
  have := rank_quotient_add_rank_le N
  have H : Module.rank R N = finrank R N := by
    rw [finrank, Cardinal.cast_toNat_of_lt_aleph0]
    exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)
  rw [← finrank_eq_rank R M, ← finrank_eq_rank R, H, add_comm] at this
  exact mod_cast this

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

lemma FiniteDimensional.finrank_add_finrank_quotient_of_free [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M]
    (N : Submodule R M) :
    finrank R N + finrank R (M ⧸ N) = finrank R M := by
  apply (finrank_add_finrank_quotient_le N).antisymm
  let B := Submodule.smithNormalForm (Module.Free.chooseBasis R M) N
  rw [← tsub_le_iff_left]
  have : LinearIndependent R (N.mkQ ∘ B.2.bM ∘ Subtype.val : ((Set.range B.2.f)ᶜ : _) → _) := by
    rw [linearIndependent_iff]
    intros l hl
    ext i
    rw [← Finsupp.apply_linearCombination, N.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl
    simpa only [Function.comp_apply, map_sum, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply, Finsupp.finset_sum_apply,
      ← Subtype.ext_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      B.2.repr_eq_zero_of_nmem_range ⟨_, hl⟩ i.prop
  have := this.fintype_card_le_finrank
  rwa [Fintype.card_compl_set, ← finrank_eq_card_chooseBasisIndex,
    Fintype.card_range, ← finrank_eq_card_basis B.2.bN] at this

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

lemma FiniteDimensional.finrank_add_finrank_quotient [IsDomain R] [IsPrincipalIdealRing R]
    (N : Submodule R M) :
    finrank R N + finrank R (M ⧸ N) = finrank R M := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  have := FiniteDimensional.finrank_add_finrank_quotient_of_free (N.map (Submodule.torsion R M).mkQ)
  rw [FiniteDimensional.finrank_quotient_of_le_torsion _ le_rfl,
    FiniteDimensional.finrank_map_of_le_torsion] at this
  convert this using 2
  symm
  fapply FiniteDimensional.finrank_of_surjective_of_le_torsion
  · refine Submodule.liftQ N ((Submodule.mkQ _).comp (Submodule.mkQ _)) ?_
    rw [LinearMap.ker_comp, ← Submodule.map_le_iff_le_comap, Submodule.ker_mkQ]
  · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
    exact (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  · rw [Submodule.ker_liftQ, Submodule.map_le_iff_le_comap, LinearMap.ker_comp,
      Submodule.ker_mkQ, Submodule.comap_map_eq, Submodule.ker_mkQ]
    apply sup_le (N.le_comap_mkQ _)
    rintro x ⟨r, hrx⟩
    exact ⟨r, by rw [← LinearMap.map_smul_of_tower, hrx, map_zero]⟩
  · rw [Submodule.ker_mkQ]
    exact inf_le_right

lemma FiniteDimensional.finrank_quotient [IsDomain R] [IsPrincipalIdealRing R]
    (N : Submodule R M) :
    finrank R (M ⧸ N) = finrank R M - finrank R N := by
  rw [← FiniteDimensional.finrank_add_finrank_quotient N, add_tsub_cancel_left]

lemma FiniteDimensional.finrank_quotient' [IsDomain R] [IsPrincipalIdealRing R]
    {S} [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M]
    (N : Submodule S M) :
    finrank R (M ⧸ N) = finrank R M - finrank R N :=
  FiniteDimensional.finrank_quotient (N.restrictScalars R)

lemma FiniteDimensional.exists_of_finrank_lt [IsDomain R] [IsPrincipalIdealRing R]
    (N : Submodule R M) (h : finrank R N < finrank R M) :
    ∃ m : M, ∀ r : R, r ≠ 0 → r • m ∉ N := by
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
