import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.Cyclotomic.CyclRat
import FltRegular.NumberTheory.RegularPrimes
import FltRegular.NumberTheory.Cyclotomic.Factoring

open scoped NumberField nonZeroDivisors

variable {p : ℕ+} {K : Type _} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open FractionalIdeal

variable (i : ℤ)

namespace FltRegular.CaseI

set_option maxHeartbeats 1600000 in
theorem exists_int_sum_eq_zero (hpodd : p ≠ 2) [hp : Fact (p : ℕ).Prime] (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) = u * α ^ (p : ℕ)) :
    ∃ k : ℤ,
      (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) - (hζ.unit' ^ (2 * k) : (𝓞 K)ˣ) * (x + y * (hζ.unit' ^ (-i) : (𝓞 K)ˣ)) ∈
        Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) :=
  by
  letI : NumberField K := IsCyclotomicExtension.numberField { p } ℚ _
  obtain ⟨β, k, hβreal : galConj K p β = β, H⟩ := unit_lemma_gal_conj hζ hpodd hp.out u
  have : (x + y * (hζ.unit' ^ (-i) : (𝓞 K)ˣ) : K) = galConj K p (x + y * ↑↑(IsPrimitiveRoot.unit' hζ) ^ i) := by
    simp [galConj_zeta_runity hζ, ← coe_life]
  obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd p α
  refine' ⟨k, _⟩
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨γ, hγ⟩ := ha
  rw [h, sub_eq_iff_eq_add.1 hγ, mul_add, ← mul_assoc, mul_comm (↑u : 𝓞 K), mul_assoc, add_sub_assoc]
  refine' dvd_add (Dvd.intro _ rfl) _
  have h' := congr_arg (fun a : 𝓞 K => (a : K)) h
  have hγ' := congr_arg (fun a : 𝓞 K => (a : K)) hγ
  simp only [AddSubgroupClass.coe_sub, SubsemiringClass.coe_pow, SubringClass.coe_intCast, MulMemClass.coe_mul,
    SubringClass.coe_natCast, AddMemClass.coe_add, coe_zpow'] at h' hγ'
  rw [h', sub_eq_iff_eq_add.1 hγ', H, MulMemClass.coe_mul, AlgEquiv.map_mul, AlgEquiv.map_mul, AlgEquiv.map_add,
    map_intCast, AlgEquiv.map_mul, coe_zpow', coe_zpow'] at this
  simp only [hζ.coe_unit'_coe, SubringClass.coe_natCast, map_natCast] at this
  let γ' := (⟨galConj K p γ, NumberField.RingOfIntegers.map_mem (galConj K p) γ⟩ : 𝓞 K)
  have hint : ↑γ' = galConj K p γ := rfl
  rw [hβreal, map_zpow₀, galConj_zeta_runity hζ, ← hζ.coe_unit'_coe, inv_zpow, ← zpow_neg, ← hint, ←
    SubringClass.coe_intCast (𝓞 K) x, ← SubringClass.coe_intCast (𝓞 K) y, ← coe_zpow', ←
    SubringClass.coe_natCast (𝓞 K) p, ← coe_zpow', ← SubringClass.coe_intCast (𝓞 K) a, ← MulMemClass.coe_mul (𝓞 K), ←
    AddMemClass.coe_add (𝓞 K), ← MulMemClass.coe_mul (𝓞 K), ← MulMemClass.coe_mul (𝓞 K), ← AddMemClass.coe_add (𝓞 K), ←
    MulMemClass.coe_mul (𝓞 K), Subtype.coe_inj] at this
  rw [this, mul_add, mul_add, sub_add_eq_sub_sub, sub_right_comm]
  refine' dvd_sub _ (by simp)
  rw [mul_comm (↑β : 𝓞 K), ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← zpow_add, two_mul, ← sub_eq_add_neg,
    add_sub_assoc, sub_self, add_zero, mul_comm _ (↑β : 𝓞 K), ← H, sub_self]
  exact dvd_zero _

end FltRegular.CaseI
