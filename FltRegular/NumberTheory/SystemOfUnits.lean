import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.CyclotomicRing
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Localization

open FiniteDimensional
open NumberField

variable (p : ℕ) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open Module BigOperators Finset
open CyclotomicIntegers(zeta)

variable
  (G : Type*) {H : Type*} [AddCommGroup G] (s : ℕ)
  (hf : finrank ℤ G = s * (p - 1))

local notation "A" => (CyclotomicIntegers p)

section

variable [Module (CyclotomicIntegers p) G]

structure systemOfUnits (s : ℕ)
  where
  units : Fin s → G
  linearIndependent : LinearIndependent A units

namespace systemOfUnits

lemma existence0 : Nonempty (systemOfUnits p G 0) := by
  exact ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

theorem _root_.PowerBasis.finrank' {R S} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) : finrank R S = pb.dim := by
  rw [finrank_eq_card_basis pb.basis, Fintype.card_fin]

open Cardinal Submodule in
theorem _root_.finrank_span_set_eq_card' {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Nontrivial R] (s : Set M) [Fintype s] (hs : LinearIndependent R ((↑) : s → M)) :
    finrank R (span R s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)

include hp

lemma finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by
  classical
  have := Fact.mk hp
  have := finrank_span_set_eq_card' (R := A) (Set.range f)
    ((linearIndepOn_id_range_iff hf.injective).mpr hf)
  simp only [Set.toFinset_range, Finset.card_image_of_injective _ hf.injective, card_fin] at this
  rw [← CyclotomicIntegers.powerBasis_dim, ← PowerBasis.finrank']
  conv_rhs => rw [← this]
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_basis (Basis.span hf)
  rw [finrank_mul_finrank]

include hf

lemma ex_not_mem [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
  have := Fact.mk hp
  have : Module.Finite ℤ G := Module.finite_of_finrank_pos
    (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine Submodule.exists_of_finrank_lt
    ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) ?_
  change finrank ℤ (Submodule.span A _) < _
  rw [finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le hR rfl.le hp.pred_pos

end systemOfUnits

end

namespace systemOfUnits

include hp hf

variable [Module.Free ℤ G]

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
        Nonempty (systemOfUnits p G (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p hp G s hf S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra! ha
    have := Fact.mk hp
    obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    rw [smul_zero, smul_add, smul_smul, mul_comm f,
      ← Hf, ← eq_neg_iff_add_eq_zero, Int.cast_smul_eq_zsmul] at hy
    apply hg _ h0
    rw [hy]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ y.2)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ s) :  Nonempty (systemOfUnits p G R) := by
    induction R with
    | zero => exact existence0 p G
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p hp G s hf S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence [Module A G] : Nonempty (systemOfUnits p G s) := existence'' p hp G s hf rfl.le

end systemOfUnits
