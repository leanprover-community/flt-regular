import Mathlib.LinearAlgebra.SModEq
import Mathlib.NumberTheory.NumberField.Norm

open scoped NumberField

open RingOfIntegers Ideal Finset Nat FiniteDimensional

variable {K : Type _} [Field K] (pb : PowerBasis ℤ (𝓞 K))

instance : Module (𝓞 K) (𝓞 K) := Semiring.toModule

theorem exists_int_sModEq (x : 𝓞 K) :
    ∃ (n : ℤ), SModEq (span ({ pb.gen } : Set (𝓞 K))) x n := by
  refine' ⟨(pb.basis.repr x) ⟨0, pb.dim_pos⟩, _⟩
  have H := Basis.sum_repr pb.basis x
  rw [PowerBasis.coe_basis, ← insert_erase (mem_univ (⟨0, pb.dim_pos⟩ : Fin pb.dim)), sum_insert] at H
  · have :
      ∀ i : (univ : Finset (Fin pb.dim)).erase ⟨0, pb.dim_pos⟩,
        ↑((pb.basis.repr x) i) * pb.gen ^ ((i : Fin pb.dim) : ℕ) =
          ↑((pb.basis.repr x) i) * pb.gen ^ (i : ℕ).pred.succ := by
      rintro ⟨i, hi⟩
      congr 1
      rw [succ_pred_eq_of_pos]
      rw [Subtype.coe_mk]
      refine' Nat.pos_of_ne_zero fun h => _
      cases' i with i₁ hi₁
      simp only [Subtype.coe_mk] at h
      simp only [mem_univ, not_true, mem_erase, ne_eq, Fin.mk.injEq, and_true] at hi
      exact hi h
    simp only [Fin.val_mk, _root_.pow_zero, Int.smul_one_eq_coe, zsmul_eq_mul] at H
    rw [← Finset.sum_finset_coe] at H
    conv_lhs at H =>
      congr
      rfl
      congr
      rfl
      ext i
      rw [this i, _root_.pow_succ, ← mul_assoc, mul_comm _ pb.gen, mul_assoc]
    rw [← mul_sum] at H
    nth_rw 1 [← H]
    rw [SModEq.sub_mem, mul_one, add_sub_cancel', mul_comm, mem_span_singleton']
    exact ⟨_, rfl⟩
  · exact not_mem_erase (⟨0, pb.dim_pos⟩ : Fin pb.dim) univ

variable [NumberField K] {pb}

variable (hpr : Prime (norm ℚ pb.gen))

theorem gen_ne_zero : pb.gen ≠ 0 := by
  intro h
  simp only [norm, MonoidHom.restrict_apply, MonoidHom.codRestrict_apply,
    Algebra.norm_eq_zero_iff.2 (show (pb.gen : K) = 0 by exact_mod_cast h)] at hpr
  apply Prime.ne_zero hpr
  rfl

theorem quotient_not_trivial : Nontrivial ((𝓞 K) ⧸ span ({pb.gen} : Set (𝓞 K))) :=
  Quotient.nontrivial fun h => hpr.not_unit ((isUnit_norm ℚ).2 (span_singleton_eq_top.1 h))

lemma SModEq.Ideal_def {R : Type*} [CommRing R] (I : Ideal R) (x y : R) :
  x ≡ y [SMOD I] ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I y :=
Iff.rfl

instance {K : Type*} [Field K] [NumberField K] :
  Module (𝓞 ℚ) (𝓞 K) := Algebra.toModule

instance {K : Type*} [Field K] [NumberField K] :
  SMul (𝓞 ℚ) (𝓞 K) := Algebra.toSMul

lemma norm_intCast {K : Type*} [Field K] [NumberField K] (n : ℤ) :
  norm ℚ (n : 𝓞 K) = n ^ (finrank ℚ K) := by
  rw [← eq_intCast (algebraMap ℤ (𝓞 K)) n, IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) (𝓞 K)]
  simp only [norm_algebraMap, algebraMap_int_eq, Int.coe_castRingHom, eq_intCast, Int.cast_pow]
