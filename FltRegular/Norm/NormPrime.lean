import Mathlib.LinearAlgebra.SModEq
import Mathlib.NumberTheory.NumberField.Norm

open scoped NumberField

open RingOfIntegers Ideal Finset Nat FiniteDimensional

variable {K : Type _} [Field K] (pb : PowerBasis ℤ (𝓞 K))

local notation "R" => 𝓞 K

theorem exists_int_sModEq (x : R) : ∃ n : ℤ, SModEq (span ({pb.gen} : Set R)) x n :=
  by
  refine' ⟨(pb.basis.repr x) ⟨0, pb.dim_pos⟩, _⟩
  have H := Basis.sum_repr pb.basis x
  rw [PowerBasis.coe_basis, ←
    insert_erase (mem_univ ⟨0, pb.dim_pos⟩ : (⟨0, pb.dim_pos⟩ : Fin pb.dim) ∈ univ), sum_insert] at
    H 
  · have :
      ∀ i : (univ : Finset (Fin pb.dim)).eraseₓ ⟨0, pb.dim_pos⟩,
        ↑((pb.basis.repr x) i) * pb.gen ^ ((i : Fin pb.dim) : ℕ) =
          ↑((pb.basis.repr x) i) * pb.gen ^ (i : ℕ).pred.succ :=
      by
      rintro ⟨i, hi⟩
      congr 1
      rw [succ_pred_eq_of_pos]
      rw [coe_coe, Subtype.coe_mk]
      refine' Nat.pos_of_ne_zero fun h => _
      cases' i with i₁ hi₁
      simp only [coe_coe, Subtype.coe_mk] at h 
      simpa [h] using hi
    simp only [Fin.val_mk, pow_zero, Int.smul_one_eq_coe, zsmul_eq_mul] at H 
    rw [← Finset.sum_finset_coe] at H 
    conv_lhs at H =>
      congr
      skip
      congr
      skip
      ext
      rw [this i, pow_succ, ← mul_assoc, mul_comm _ pb.gen, mul_assoc]
    rw [← mul_sum] at H 
    nth_rw 1 [← H]
    rw [mul_one, SModEq.def, quotient.mk_eq_mk, map_add, _root_.map_mul, ← submodule_span_eq,
      quotient.eq_zero_iff_mem.2 (Submodule.mem_span_singleton_self pb.gen), MulZeroClass.zero_mul,
      add_zero, quotient.mk_eq_mk]
  · exact not_mem_erase ⟨0, pb.dim_pos⟩ univ

variable [NumberField K] {pb}

variable (hpr : Prime (norm ℚ pb.gen))

theorem gen_ne_zero : pb.gen ≠ 0 := by
  intro h
  simp only [norm, MonoidHom.restrict_apply, MonoidHom.codRestrict_apply,
    Algebra.norm_eq_zero_iff.2 (show (pb.gen : K) = 0 by exact_mod_cast h)] at hpr 
  simpa using Prime.ne_zero hpr

theorem quotient_not_trivial : Nontrivial (R ⧸ span ({pb.gen} : Set R)) :=
  Quotient.nontrivial fun h => hpr.not_unit ((isUnit_norm ℚ).2 (span_singleton_eq_top.1 h))

attribute [local instance] NumberField.ringOfIntegersAlgebra

theorem prime_of_norm_prime [IsGalois ℚ K] : Prime pb.gen :=
  by
  rw [← span_singleton_prime (gen_ne_zero hpr), ← quotient.is_domain_iff_prime]
  haveI : Nontrivial (𝓞 K ⧸ span {pb.gen}) := ⟨(quotient_not_trivial hpr).exists_pair_ne⟩
  suffices NoZeroDivisors (𝓞 K ⧸ span {pb.gen}) by exact @NoZeroDivisors.to_isDomain _ _ _ this
  refine' ⟨_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  by_contra' h
  have h₁ := h.1; have h₂ := h.2
  simp only [Submodule.Quotient.quot_mk_eq_mk, quotient.mk_eq_mk] at h₁ h₂ hxy 
  obtain ⟨n, hn⟩ := exists_int_sModEq pb ⟨x, hx⟩
  obtain ⟨m, hm⟩ := exists_int_sModEq pb ⟨y, hy⟩
  rw [SModEq.def, quotient.mk_eq_mk] at hn hm 
  rw [hn] at h₁ hxy ; rw [hm] at h₂ hxy 
  obtain ⟨z, hz⟩ := mem_span_singleton.1 (quotient.eq_zero_iff_mem.1 hxy)
  replace hz := congr_arg (norm ℚ) hz
  have hnm : (norm ℚ) ((n : R) * (m : R)) = n ^ finrank ℚ K * m ^ finrank ℚ K :=
    by
    refine' Subtype.ext _
    simp only [norm, MonoidHom.restrict_apply, MulMemClass.coe_mul, SubringClass.coe_intCast,
      _root_.map_mul, MonoidHom.codRestrict_apply, SetLike.coe_mk, SubsemiringClass.coe_pow]
    rw [show (n : K) = algebraMap ℚ K (n : ℚ) by simp,
      show (m : K) = algebraMap ℚ K (m : ℚ) by simp, Algebra.norm_algebraMap,
      Algebra.norm_algebraMap]
  replace hz : norm ℚ pb.gen ∣ n ^ finrank ℚ K * m ^ finrank ℚ K
  · refine' ⟨norm ℚ z, _⟩
    rwa [← hnm, ← _root_.map_mul]
  simp only [quotient.mk_eq_mk, map_intCast] at h₁ h₂ 
  cases' hpr.dvd_or_dvd hz with Hn Hm
  ·
    simpa [h₁] using
      quotient.eq_zero_iff_mem.2
        (mem_span_singleton.2
          (dvd_trans (dvd_norm ℚ pb.gen)
            (RingHom.map_dvd (algebraMap (𝓞 ℚ) R) (hpr.dvd_of_dvd_pow Hn))))
  ·
    simpa [h₂] using
      quotient.eq_zero_iff_mem.2
        (mem_span_singleton.2
          (dvd_trans (dvd_norm ℚ pb.gen)
            (RingHom.map_dvd (algebraMap (𝓞 ℚ) R) (hpr.dvd_of_dvd_pow Hm))))

