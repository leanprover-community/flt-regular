import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.GaloisPrime
import Mathlib

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open FiniteDimensional
open NumberField

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open FiniteDimensional BigOperators Finset

variable
  (G : Type*) {H : Type*} [AddCommGroup G] [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (r : ℕ)
  [DistribMulAction H G] [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation3 "A" =>
  MonoidAlgebra ℤ H ⧸ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i}

structure systemOfUnits (r : ℕ) [Module A G]
  where
  units : Fin r → G
  linearIndependent : LinearIndependent A units

namespace systemOfUnits

lemma nontrivial (hr : r ≠ 0) : Nontrivial G := by
    by_contra' h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [FiniteDimensional.finrank_zero_of_subsingleton] at hf
    simp only [ge_iff_le, zero_eq_mul, tsub_eq_zero_iff_le] at hf
    cases hf with
    | inl h => exact hr h
    | inr h => simpa [Nat.lt_succ_iff, h] using not_lt.2 (Nat.prime_def_lt.1 hp).1

lemma bezout [Module A G] {a : A} (ha : a ≠ 0) : ∃ (f : A) (n : ℤ),
        f * a = n := sorry

lemma existence0 [Module A G] : Nonempty (systemOfUnits p G σ 0) := by
    exact ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

lemma span_eq_span [Module A G] {R : ℕ} (f : Fin R → G) :
        (Submodule.span A (Set.range f) : Set G) =
        Submodule.span ℤ (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ f e.1)) := sorry

lemma ex_not_mem [Module A G] {R : ℕ} (S : systemOfUnits p G σ R) (hR : R < r) :
        ∃ g, ∀ (k : ℤ), ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
    by_contra' h
    sorry

set_option synthInstance.maxHeartbeats 0 in
lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G σ R) (hR : R < r) :
        Nonempty (systemOfUnits p G σ (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p G σ r S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra' ha
    obtain ⟨f, n, Hf⟩ := bezout p G σ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    let mon : Monoid A := inferInstance
    rw [smul_zero, smul_add, smul_smul, Hf, ← eq_neg_iff_add_eq_zero, intCast_smul] at hy
    apply hg n
    rw [hy]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ y.2)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ r) :  Nonempty (systemOfUnits p G σ R) := by
    induction R with
    | zero => exact existence0 p G σ
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p G σ r S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence (r) [Module A G] : Nonempty (systemOfUnits p G σ r) := existence'' p G σ r rfl.le

end systemOfUnits
