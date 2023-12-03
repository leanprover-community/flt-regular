import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.GaloisPrime
import FltRegular.NumberTheory.CyclotomicRing
import FltRegular.NumberTheory.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open FiniteDimensional
open NumberField

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open FiniteDimensional BigOperators Finset
open CyclotomicIntegers(zeta)

variable
  (G : Type*) {H : Type*} [AddCommGroup G] -- [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  -- (σ : H) (hσ : Subgroup.zpowers σ = ⊤)
  (r : ℕ)
  -- [DistribMulAction H G]
  [Module.Free ℤ G]  (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation "A" => (CyclotomicIntegers (PNat.val p))

variable [Module (CyclotomicIntegers p) G]

structure systemOfUnits (r : ℕ)
  where
  units : Fin r → G
  linearIndependent : LinearIndependent A units

namespace systemOfUnits

lemma nontrivial (hr : r ≠ 0) : Nontrivial G := by
    by_contra! h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [FiniteDimensional.finrank_zero_of_subsingleton] at hf
    simp only [ge_iff_le, zero_eq_mul, tsub_eq_zero_iff_le] at hf
    cases hf with
    | inl h => exact hr h
    | inr h => simpa [Nat.lt_succ_iff, h] using not_lt.2 (Nat.prime_def_lt.1 hp).1

lemma existence0 : Nonempty (systemOfUnits p G 0) := by
    exact ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

lemma spanA_eq_spanZ {R : ℕ} (f : Fin R → G) :
    (Submodule.span A (Set.range f)).restrictScalars ℤ = Submodule.span ℤ
      (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p) ^ e.2.1 • f e.1)) := by
  letI := Fact.mk hp
  rw [← Submodule.span_smul_of_span_eq_top (CyclotomicIntegers.powerBasis p).basis.span_eq,
    Set.range_smul_range]
  congr
  ext
  simp only [PowerBasis.coe_basis, CyclotomicIntegers.powerBasis_gen, Set.mem_range, Prod.exists]
  rw [exists_comm, CyclotomicIntegers.powerBasis_dim]

theorem _root_.PowerBasis.finrank' {R S} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) : FiniteDimensional.finrank R S = pb.dim := by
  rw [FiniteDimensional.finrank_eq_card_basis pb.basis, Fintype.card_fin]

lemma finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by
  classical
  letI := Fact.mk hp
  have := finrank_span_set_eq_card' (R := A) (Set.range f)
    ((linearIndependent_subtype_range hf.injective).mpr hf)
  simp only [Set.toFinset_range, Finset.card_image_of_injective _ hf.injective, card_fin] at this
  rw [← CyclotomicIntegers.powerBasis_dim, ← PowerBasis.finrank']
  conv_rhs => rw [← this]
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_fintype_basis (Basis.span hf)
  rw [finrank_mul_finrank']


lemma ex_not_mem {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
  have := Fact.mk hp
  have : Module.Finite ℤ G := Module.finite_of_finrank_pos
    (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine FiniteDimensional.exists_of_finrank_lt
    ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) ?_
  show finrank ℤ (Submodule.span A _) < _
  rw [finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul hR rfl.le hp.pred_pos

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
        Nonempty (systemOfUnits p G (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p hp G r hf S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra! ha
    letI := Fact.mk hp
    obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    rw [smul_zero, smul_add, smul_smul, mul_comm f,
      ← Hf, ← eq_neg_iff_add_eq_zero, intCast_smul] at hy
    apply hg _ h0
    rw [hy]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ y.2)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ r) :  Nonempty (systemOfUnits p G R) := by
    induction R with
    | zero => exact existence0 p G
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p hp G r hf S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence [Module A G] : Nonempty (systemOfUnits p G r) := existence'' p hp G r hf rfl.le

end systemOfUnits
