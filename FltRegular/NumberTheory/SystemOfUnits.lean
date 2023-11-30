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

lemma bezout [Module A G] {a : A} (ha : a ≠ 0) : ∃ (f : A) (n : ℤ),
        f * a = n := sorry

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

lemma mem_spanZ [Module A G] {R : ℕ} (n : Fin R) (m : Fin (p - 1)) (f : Fin R → G) :
    (zeta p) ^ m.1 • f n ∈ Submodule.span ℤ
    (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1)) := by
  exact Submodule.subset_span ⟨⟨n, m⟩, rfl⟩
  -- have hσmon : ∀ x, x ∈ Submonoid.powers σ := fun τ ↦ by
  --   have : τ ∈ Subgroup.zpowers σ := by simp [hσ]
  --   exact mem_powers_iff_mem_zpowers.2 this
  -- obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (hσmon h)
  -- rw [← hk, map_pow, map_pow (Ideal.Quotient.mk (Ideal.span
  --   {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i})), smul_smul (M := A),
  --   ← pow_add]
  -- rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.quot_mk_eq_mk]
  -- sorry

-- #exit

set_option synthInstance.maxHeartbeats 0 in
lemma mem_spanS [Module A G] {R : ℕ} {g : G} (a : A) (f : Fin R → G)
    (hg : g ∈ Submodule.span ℤ
    (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1))) :
    a • g ∈ Submodule.span ℤ
    (Set.range (fun (e : Fin R × (Fin (p - 1))) ↦ (zeta p)^e.2.1 • f e.1)) := by
  rcases a with ⟨x⟩
  revert hg
  sorry
  -- apply MonoidAlgebra.induction_on x
  -- · intro h hg
  --   refine Submodule.span_induction hg ?_ ?_ ?_ ?_
  --   · intro g₁ ⟨⟨n, m⟩, key⟩
  --     simp only at key
  --     rw [← key]
  --     apply mem_spanZ
  --       --have : h ∈ Subgroup.zpowers σ := by simp [hσ]
  --       --rw [Subgroup.mem_zpowers_iff] at this
  --       --obtain ⟨k, hk⟩ := this
  --       --rw [← key, ← hk]
  --       --refine ⟨⟨?_, m⟩, ?_⟩
  --   · rw [smul_zero]
  --     apply Submodule.zero_mem
  --   · intro g₁ g₂ hg₁ hg₂
  --     rw [smul_add]
  --     exact Submodule.add_mem _ hg₁ hg₂
  --   · intro n g hg
  --     rw [smul_algebra_smul_comm]
  --     apply Submodule.smul_mem
  --     exact hg
  -- · intro f₁ f₂ hf₁ hf₂ hg
  --   simp only [MonoidAlgebra.of_apply, Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk,
  --     map_add]
  --   rw [add_smul (R := A)]
  --   exact Submodule.add_mem _ (hf₁ hg) (hf₂ hg)
  -- · intro n f₁ hf₁ hg
  --   rw [Submodule.Quotient.quot_mk_eq_mk, ← intCast_smul (k := MonoidAlgebra ℤ H),
  --     Submodule.Quotient.mk_smul, intCast_smul, smul_assoc]
  --   apply Submodule.smul_mem
  --   specialize hf₁ hg
  -- rwa [Submodule.Quotient.quot_mk_eq_mk] at hf₁

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
      exact mem_spanS p G a f hx

lemma ex_not_mem [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
        ∃ g, ∀ (k : ℤ), ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
    by_contra' h
    sorry

set_option synthInstance.maxHeartbeats 0 in
lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < r) :
        Nonempty (systemOfUnits p G (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p G r S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra' ha
    letI := Fact.mk hp
    obtain ⟨n, hn, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    let mon : Monoid A := inferInstance
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
