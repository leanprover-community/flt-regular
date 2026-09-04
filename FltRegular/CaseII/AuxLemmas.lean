module

public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}

open scoped nonZeroDivisors
open Polynomial

open FractionalIdeal in
lemma exists_not_dvd_spanSingleton_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : Prime x) (I J : Ideal R)
    (hI : ¬ (Ideal.span <| singleton x) ∣ I) (hJ : ¬ (Ideal.span <| singleton x) ∣ J)
    (h : Submodule.IsPrincipal ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) : ∃ a b : R,
    ¬(x ∣ a) ∧ ¬(x ∣ b) ∧
      spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
  have hI' : (I : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [← coeIdeal_bot, Ne, coeIdeal_inj]
    rintro rfl
    exact hI (dvd_zero _)
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [← coeIdeal_bot, Ne, coeIdeal_inj]
    rintro rfl
    exact hJ (dvd_zero _)
  rw [isPrincipal_iff] at h
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ r
  rw [IsFractionRing.mk'_eq_div] at hr
  have hs : s ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_div, spanSingleton_zero, div_eq_zero_iff, hJ', or_false] at hr
    exact hI' hr
  have ht : algebraMap R K (t : R) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero t.prop)
  have he : Ideal.span {s} * J = I * Ideal.span {(t : R)} := by
    apply coeIdeal_injective (K := K)
    simp only [coeIdeal_mul, coeIdeal_span_singleton]
    apply (div_eq_div_iff (spanSingleton_eq_zero_iff.not.mpr ht) hJ').mp
    simpa only [spanSingleton_div_spanSingleton] using hr.symm
  -- Remove the maximal power of `x` from the numerator.
  obtain ⟨n, a, ha, hs⟩ := WfDvdMonoid.max_power_factor hs hx.irreducible
  have hcoprime : IsCoprime (Ideal.span {x}) I := by
    rwa [Ideal.isCoprime_iff_gcd,
      (Ideal.prime_span_singleton_iff.mpr hx).irreducible.gcd_eq_one_iff]
  have htn : x ^ n ∣ (t : R) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, ← Ideal.span_singleton_pow]
    apply (hcoprime.pow_left (m := n)).dvd_of_dvd_mul_left
    rw [← he]
    exact dvd_mul_of_dvd_left (by
      rw [Ideal.span_singleton_pow, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
      exact ⟨a, hs⟩) J
  obtain ⟨b, hb⟩ := htn
  have hab : spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
    rw [hs, hb, map_mul, map_mul, mul_div_mul_left] at hr
    · exact hr.symm
    · simpa only [map_zero] using (IsFractionRing.injective R K).ne (pow_ne_zero n hx.ne_zero)
  have he' : Ideal.span {a} * J = I * Ideal.span {b} := by
    rw [hs, hb, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_mul_span_singleton, mul_assoc, mul_left_comm I] at he
    exact mul_left_cancel₀ (by
      simpa only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        using pow_ne_zero n hx.ne_zero) he
  refine ⟨a, b, ha, ?_, hab⟩
  intro hxb
  apply ha
  rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton]
  have hd : Ideal.span {x} ∣ Ideal.span {a} * J := by
    rw [he']
    exact dvd_mul_of_dvd_right (by rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton]) I
  exact ((Ideal.prime_span_singleton_iff.mpr hx).dvd_or_dvd hd).resolve_right hJ
