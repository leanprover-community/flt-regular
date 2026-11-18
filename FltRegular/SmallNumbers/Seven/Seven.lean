module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.NormNum.Prime

/-!
# The ring of integers of the seventh cyclotomic field

This file computes the relevant Minkowski bound and proves that the ring of integers of a
seventh-cyclotomic number field is a principal ideal domain. The bound is `4`, and the primes `2`
and `3` have inertia degrees `3` and `6` in `ℚ(ζ₇)`, so no prime above them has norm at most `4`.
-/

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real NumberField.RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- The primality fact for `7`. -/
instance Nat.fact_prime_seven : Fact (Nat.Prime 7) := ⟨prime_seven⟩

/-- The explicit floor computation used in the Minkowski bound for the seventh cyclotomic field. -/
lemma crazy7 : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · grw [pi_lt_d2.le, ← (le_sqrt (by norm_num) (by norm_num)).mpr
      (show (129 : ℝ) ^ 2 ≤ 16807 by norm_num)]
    norm_num
  · grw [← pi_gt_three.le, (sqrt_le_left (by norm_num)).mpr
      (show (16807 : ℝ) ≤ 130 ^ 2 by norm_num)]
    norm_num

variable [IsCyclotomicExtension {7} ℚ K]

/-- The Minkowski bound for a seventh-cyclotomic number field is `4`. -/
theorem M7 : ⌊(M K)⌋₊ = 4 := by
  rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K (irreducible_rat (by norm_num)),
    nrComplexPlaces_eq_totient_div_two 7, totient_prime Nat.prime_seven]
  simpa using crazy7

variable (K) in
/-- The ring of integers of a seventh-cyclotomic number field is a principal ideal domain. -/
theorem Rat.seven_pid : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p hp hprime ↦ ?_
  have : (span {(p : ℤ)}).IsPrime :=
    isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hprime))
  obtain ⟨P⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, P.2, Or.inl ?_⟩
  rw [M7] at hp ⊢
  fin_cases hp
  · norm_num at hprime
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by decide),
      (orderOf_eq_iff (n := 3) (by decide)).mpr ⟨by decide, by decide⟩]
    decide
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by decide),
      (orderOf_eq_iff (n := 6) (by decide)).mpr ⟨by decide, by decide⟩]
    decide
  · norm_num at hprime
