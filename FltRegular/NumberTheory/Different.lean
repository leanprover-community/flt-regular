import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Localization.FractionRing
import FltRegular.NumberTheory.QuotientTrace
import Mathlib.NumberTheory.KummerDedekind
/-!
# The different ideal

## Main result
- `pow_sub_one_dvd_differentIdeal`:
  If `P ^ e ∣ p.map (algebraMap A B)`, then `P ^ (e - 1) ∣ differentIdeal A B`.
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ differentIdeal A B`
    with `f` being the minimal polynomial of `x`.

-/
universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A K L B) [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsDomain B]
variable [IsFractionRing A K] [IsIntegralClosure B A L] [IsFractionRing B L]
variable [FiniteDimensional K L] [IsSeparable K L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [IsFractionRing B L]

open nonZeroDivisors IsLocalization Matrix Algebra

variable [IsDedekindDomain A] [IsDedekindDomain B] [IsFractionRing B L]

lemma pow_sub_one_dvd_differentIdeal_aux
    [NoZeroSMulDivisors A B] [Module.Finite A B]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (he : 0 < e) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (NoZeroSMulDivisors.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥
  · rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e
  · obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B → _) at ha
    apply_fun (· ^ (e - 1) : Ideal B → _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he.ne.symm)]
    rw [pow_add, hb, mul_assoc, mul_right_inj' (pow_ne_zero _ hPbot), pow_one, mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices : ∀ x ∈ a, Algebra.intTrace A B x ∈ p
  · have hP : ((P ^ (e - 1) : _)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B)
    · apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div, ne_eq,
        FractionalIdeal.coeIdeal_eq_zero, mul_div_assoc]
      rw [div_self (by simpa), mul_one]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot), hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_nonzero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K)
    · rw [← Algebra.algebraMap_intTrace (A := A)]
      exact Submodule.mem_map_of_mem (this z hz)
    rwa [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intros x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
    ← isNilpotent_iff_eq_zero]
  apply Algebra.isNilpotent_trace_of_isNilpotent
  use e
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  apply (Ideal.dvd_iff_le.mp this)
  exact Ideal.pow_mem_pow hx _

lemma pow_sub_one_dvd_differentIdeal
    [IsDedekindDomain A] [NoZeroSMulDivisors A B] [Module.Finite A B]
    [IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _ (Algebra.IsIntegral.of_finite (R := A) (B := B))
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
      (isAlgebraic_of_isFractionRing _ _ (Algebra.IsIntegral.of_finite (R := A) (B := B)))
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    Module.Finite_of_isLocalization A B _ _ A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  rw [← Ne.def, ← Nat.pos_iff_ne_zero] at he
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) B P e he hp hP
