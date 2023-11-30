import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.GaloisPrime
import FltRegular.NumberTheory.CyclotomicRing
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
  [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation3 "A" => CyclotomicIntegers p

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

lemma existence0 [Module A G] : Nonempty (systemOfUnits p G 0) := by
    exact ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

lemma spanA_eq_spanA [Module A G] {R : ℕ} (f : Fin R → G) :
        Submodule.span A (Set.range f) =
        Submodule.span A (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p) ^ e.2.1 • f e.1)) := by
    refine le_antisymm (Submodule.span_mono (fun x hx ↦ ?_)) ?_
    · obtain ⟨a, ha⟩ := hx
      refine ⟨⟨a, ⟨0, hp.pred_pos⟩⟩, ?_⟩
      simp only [MonoidAlgebra.of_apply, pow_zero, ha]
      exact one_smul A _
    · rw [Submodule.span_le (R := A)]
      intro x ⟨⟨a, b⟩, hx⟩
      simp only [← hx, MonoidAlgebra.of_apply, SetLike.mem_coe]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span (R := A)
      use a

def _root_.Submodule.stabilizer {R M} (S)
    [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [Algebra R S] [IsScalarTower R S M] (N : Submodule R M) : Subalgebra R S where
  carrier := { x | ∀ n ∈ N, x • n ∈ N }
  mul_mem' := fun {a} {b} ha hb n hn ↦ mul_smul a b n ▸ ha _ (hb n hn)
  add_mem' := fun {a} {b} ha hb n hn ↦ add_smul a b n ▸ add_mem (ha n hn) (hb n hn)
  algebraMap_mem' := fun r n hn ↦ algebraMap_smul S r n ▸ N.smul_mem r hn

lemma Submodule.mem_stabilizer_span {R M} (S)
    [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [Algebra R S] [IsScalarTower R S M] (s : Set M) (x : S) :
    x ∈ (Submodule.span R s).stabilizer S ↔ ∀ i ∈ s, x • i ∈ Submodule.span R s := by
  constructor
  · intro H i hi
    exact H i (Submodule.subset_span hi)
  · intro H m hm
    refine Submodule.span_induction hm H ?_ ?_ ?_
    · rw [smul_zero]; exact zero_mem _
    · intros _ _ h₁ h₂; rw [smul_add]; exact add_mem h₁ h₂
    · intros r m h; rw [smul_comm]; exact Submodule.smul_mem _ r h

lemma mem_spanS [Module A G] {R : ℕ} {g : G} (a : A) (f : Fin R → G)
    (hg : g ∈ Submodule.span ℤ
    (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1))) :
    a • g ∈ Submodule.span ℤ
    (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1)) := by
  revert hg g
  letI := Fact.mk hp
  suffices : ⊤ ≤ Submodule.stabilizer A
    (Submodule.span ℤ (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1)))
  · exact @this a trivial
  rw [← CyclotomicIntegers.adjoin_zeta, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
    SetLike.mem_coe, Submodule.mem_stabilizer_span]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simp only
  rw [smul_smul, ← pow_succ]
  by_cases hj : j + 1 < (p : ℕ) - 1
  · exact Submodule.subset_span ⟨⟨i, ⟨_, hj⟩⟩, rfl⟩
  replace hj : j + 1 = (p : ℕ) - 1
  · linarith [j.prop]
  rw [hj, CyclotomicIntegers.zeta_pow_sub_one, neg_smul, sum_smul]
  apply neg_mem
  apply sum_mem
  intro _ _
  exact Submodule.subset_span ⟨⟨i, _⟩, rfl⟩

lemma spanA_eq_spanZ [Module A G] {R : ℕ} (f : Fin R → G) :
        (Submodule.span A (Set.range f) : Set G) =
        Submodule.span ℤ (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p) ^ e.2.1 • f e.1)) := by
    let S := Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p) ^ e.2.1 • f e.1)
    have := Submodule.span_le_restrictScalars ℤ A S
    rw [← spanA_eq_spanA p hp] at this
    refine le_antisymm ?_ this
    intro x hx
    refine Submodule.span_induction hx ?_ ?_ ?_ ?_
    · intro z ⟨a, ha⟩
      apply Submodule.subset_span
      refine ⟨⟨a, ⟨0, hp.pred_pos⟩⟩, ?_⟩
      simp only [MonoidAlgebra.of_apply, pow_zero, ← ha]
      exact one_smul A _
    · simp
    · intro z w hz hw
      exact Submodule.add_mem _ hz hw
    · intro a _ hx
      exact mem_spanS p hp G _ f hx

lemma ex_not_mem [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
        ∃ g, ∀ (k : ℤ), ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
    by_contra' h
    sorry

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
        Nonempty (systemOfUnits p G (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p G r S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra' ha
    letI := Fact.mk hp
    obtain ⟨n, _, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    rw [smul_zero, smul_add, smul_smul, mul_comm f,
      ← Hf, ← eq_neg_iff_add_eq_zero, intCast_smul] at hy
    apply hg n
    rw [hy]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ y.2)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ r) :  Nonempty (systemOfUnits p G R) := by
    induction R with
    | zero => exact existence0 p G
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p hp G r S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence (r) [Module A G] : Nonempty (systemOfUnits p G r) := existence'' p hp G r rfl.le

end systemOfUnits
