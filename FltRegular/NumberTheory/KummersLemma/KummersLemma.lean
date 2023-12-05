import FltRegular.NumberTheory.KummersLemma.Field
import FltRegular.NumberTheory.Hilbert94

open scoped NumberField

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))] (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ)
  (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ (p : ℕ) ≠ u)

attribute [-instance] instCoeOut

open Polynomial

variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
variable [IsSplittingField K L (X ^ (p : ℕ) - C (u : K))]
variable (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

theorem false_of_zeta_sub_one_pow_dvd_sub_one_of_pow_ne (u : (𝓞 K)ˣ)
    (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑u : 𝓞 K) - 1)
    (hu : ∀ v : K, v ^ (p : ℕ) ≠ u) : False := by
  letI := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let L := AdjoinRoot (Polynomial.X ^ (p : ℕ) - Polynomial.C (u : K))
  haveI := isSplittingField_AdjoinRoot_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
    (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  haveI := isGalois_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
    (X_pow_sub_C_irreducible_of_prime hpri.out hu) L
  have := Polynomial.IsSplittingField.finiteDimensional L
    (Polynomial.X ^ (p : ℕ) - Polynomial.C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional ℚ L := Module.Finite.trans K L
  have : NumberField L := ⟨⟩
  have hKL : FiniteDimensional.finrank K L = p := (finrank_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ (X_pow_sub_C_irreducible_of_prime hpri.out hu) L)
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := NumberField.InfinitePlace.isUramified_of_odd_finrank (k := K) (K := L)
    (hKL.symm ▸ Nat.Prime.odd_of_ne_two hpri.out (PNat.coe_injective.ne hp))
  have := dvd_card_classGroup_of_isUnramified_isCyclic K L (hKL.symm ▸ hpri.out)
    (hKL.symm ▸ PNat.coe_injective.ne hp)
  rw [hKL, ← Int.ofNat_dvd, (Nat.prime_iff_prime_int.mp hpri.out).irreducible.dvd_iff_not_coprime,
    Nat.isCoprime_iff_coprime] at this
  exact this (by convert hreg)

-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number off
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (↑u - n : 𝓞 K)) :
    ∃ v, u = v ^ (p : ℕ) := by
  haveI : Fact (Nat.Prime p) := hpri
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root (S := {p}) ℚ (B := K) (n := p) rfl
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1
  · obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1 : ℕ) - 1
    · refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out (n := n) ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := _root_.map_dvd (Int.castRingHom (𝓞 K)) h
      simp only [map_natCast, eq_intCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_unit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime hζ).dvd.trans h) u.isUnit))
      simpa only [ge_iff_le, ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := _root_.map_dvd (Int.castRingHom (𝓞 K)) hn'
    simp only [map_natCast, eq_intCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1
  · rw [hx]
    rw [sub_eq_iff_eq_add, add_comm] at hx
    have H : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 := norm_add_one_smul_of_isUnit hpri.out
      (PNat.coe_injective.ne_iff.mpr hp) x (by rw [nsmul_eq_mul, ← hx]; exact Units.isUnit _)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ x
    simpa [ge_iff_le, Int.cast_one, sub_self, nsmul_eq_mul, Nat.cast_mul, PNat.pos,
      Nat.cast_pred, zero_sub, IsUnit.mul_iff, ne_eq, tsub_eq_zero_iff_le, not_le, dvd_neg,
      Units.isUnit, and_true, zero_add] using this
  have : ¬(∀ v : K, _) := false_of_zeta_sub_one_pow_dvd_sub_one_of_pow_ne hp hreg hζ _ this
  simp only [not_forall, not_not] at this
  obtain ⟨v, hv⟩ := this
  have hv' : IsIntegral ℤ v
  · apply IsIntegral.of_pow p.pos; rw [hv]; exact NumberField.RingOfIntegers.isIntegral_coe _
  have : IsUnit (⟨v, hv'⟩ : 𝓞 K)
  · rw [← isUnit_pow_iff p.pos.ne.symm]; convert (u ^ (p - 1 : ℕ) : (𝓞 K)ˣ).isUnit; ext; exact hv
  have hv'' : this.unit ^ (p : ℕ) = u ^ (p - 1 : ℕ)
  · ext; simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, SubmonoidClass.coe_pow] using hv
  use u / this.unit
  rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_one]
