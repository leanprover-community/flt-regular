import FltRegular.NumberTheory.KummersLemma.Field
import FltRegular.NumberTheory.Hilbert94

open Polynomial
open scoped NumberField

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : (p : ℕ).Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hp hreg

theorem exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one {u : (𝓞 K)ˣ}
    (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ (p : ℕ) = u := by
  by_contra! hu
  have hirr := X_pow_sub_C_irreducible_of_prime hpri.out hu
  have := Fact.mk hirr
  let L := AdjoinRoot (X ^ (p : ℕ) - C (u : K))
  have := isSplittingField_AdjoinRoot_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ hirr
  have := isGalois_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ hirr L
  have := IsSplittingField.finiteDimensional L (X ^ (p : ℕ) - C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ hirr L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional ℚ L := Module.Finite.trans K L
  have : NumberField L := ⟨⟩
  have hKL : Module.finrank K L = p :=
    finrank_of_isSplittingField_X_pow_sub_C ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ hirr L
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := dvd_card_classGroup_of_isUnramified_isCyclic K L (hKL.symm ▸ hpri.out)
    (hKL.symm ▸ PNat.coe_injective.ne hp)
  rw [hKL, hpri.out.dvd_iff_not_coprime] at this
  exact this (by convert hreg)

-- Let 𝑝 be a regular prime (i.e. an odd prime which does not divide the class number off
-- the 𝑝-th cyclotomic field) and 𝜉 a primitive 𝑝-th root of unity;
-- if a unit 𝑢∈𝐐(𝜉) is congruent to an integer modulo 𝑝, then 𝑢 is a 𝑝-th power in 𝐐(𝜉).
theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) :
    ∃ v, u = v ^ (p : ℕ) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root ℚ (B := K) (Set.mem_singleton p)
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1 := by
    obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1 : ℕ) - 1 := by
      refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := Int.cast_dvd_cast (α := 𝓞 K) _ _ h
      simp only [Int.cast_natCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_unit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime hζ).dvd.trans h) u.isUnit))
      simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := Int.cast_dvd_cast (α := 𝓞 K) _ _ hn'
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑(u ^ (p - 1 : ℕ)) : 𝓞 K) - 1 := by
    rw [hx]
    rw [sub_eq_iff_eq_add, add_comm] at hx
    have H : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 := norm_add_one_smul_of_isUnit hpri.out
      (PNat.coe_injective.ne_iff.mpr hp) x (by rw [nsmul_eq_mul, ← hx]; exact Units.isUnit _)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ x
    simpa [ge_iff_le, Int.cast_one, sub_self, nsmul_eq_mul, Nat.cast_mul, PNat.pos,
      Nat.cast_pred, zero_sub, IsUnit.mul_iff, ne_eq, tsub_eq_zero_iff_le, not_le, dvd_neg,
      Units.isUnit, and_true, zero_add] using this
  obtain ⟨v, hv⟩ := exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one hp hreg hζ this
  have hv' : IsIntegral ℤ v := by
    apply IsIntegral.of_pow p.pos; rw [hv]; exact NumberField.RingOfIntegers.isIntegral_coe _
  set w : 𝓞 K := ⟨v, hv'⟩
  have : IsUnit w := by
    rw [← isUnit_pow_iff p.pos.ne.symm]; convert (u ^ (p - 1 : ℕ) : (𝓞 K)ˣ).isUnit; ext; exact hv
  have hv'' : this.unit ^ (p : ℕ) = u ^ (p - 1 : ℕ) := by
    ext; simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, SubmonoidClass.coe_pow] using hv
  use u / this.unit
  rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_one]
