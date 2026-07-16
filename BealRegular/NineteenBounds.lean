import FltRegular.SmallNumbers.Cyclotomic
import FltRegular.SmallNumbers.OrderOf
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import BealRegular.NineteenPrimeClassification

/-!
# Bounds and arithmetic for a certificate at the regular prime 19

This file follows the certificate architecture used by the upstream proofs for
7, 11, and 13 and by `BealRegular.Seventeen`. External algebra software is used
only to discover polynomial identities; Lean checks every identity.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem Nat.prime_nineteen : Nat.Prime 19 := by
  norm_num

instance Nat.fact_prime_nineteen : Fact (Nat.Prime 19) :=
  ⟨Nat.prime_nineteen⟩

lemma crazy19 :
    ⌊(4 / π) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939)⌋₊ = 105933 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 9 *
          (18! / 18 ^ 18 * √5480386857784802185939) := by
        gcongr
        exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 9 *
          (18! / 18 ^ 18 * 74029634996) := by
        gcongr
        exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 105933 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 9 *
          (18! / 18 ^ 18 * √5480386857784802185939) := by
        gcongr
        exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 9 *
          (18! / 18 ^ 18 * 74029634997) := by
        gcongr
        exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ 105933 + 1 := by norm_num

variable [IsCyclotomicExtension {19} ℚ K]

theorem M19 : ⌊(M K)⌋₊ = 105933 := by
  rw [discr_prime 19 K, IsCyclotomicExtension.finrank (n := 19) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 19, totient_prime
      Nat.prime_nineteen]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow, reduceSub]
  rw [show |(↑(-1 * 5480386857784802185939 : ℤ) : ℝ)| =
    5480386857784802185939 by norm_num]
  exact crazy19

theorem cyclotomic_19 : cyclotomic 19 ℤ =
    X^18 + X^17 + X^16 + X^15 + X^14 + X^13 + X^12 + X^11 + X^10 + X^9 + X^8 +
      X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

set_option maxHeartbeats 0 in
-- Composes the independently compiled exhaustive classifiers without a heartbeat cap.
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_of_mod_eq_one {p : ℕ}
    (hp : p.Prime) (hple : p ≤ 105933) (hmod : p % 19 = 1) :
    p ∈ exceptionalSplitPrimesNineteen := by
  let k := p / 19
  have hpform : p = 19 * k + 1 := by
    dsimp [k]
    omega
  have hk : k ≤ 5575 := by omega
  have hprime : (19 * k + 1).Prime := hpform ▸ hp
  rw [hpform]
  exact prime_mem_exceptionalSplitPrimesNineteen_of_k_le hk hprime

set_option linter.unusedTactic false in
set_option maxHeartbeats 0 in
-- Checks all remaining small primes by explicit finite-order computations.
set_option maxRecDepth 20000 in
theorem log_lt_orderOf_nineteen_of_mod_ne_one {p : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hpn : p ≠ 19) (hple : p ≤ 105933)
    (hmod : p % 19 ≠ 1) (hmem : p ∉ exceptionalNonSplitPrimesNineteen) :
    Nat.log p 105933 <
      orderOf (ZMod.unitOfCoprime p (uff Nat.prime_nineteen hpn)) := by
  by_cases hpge : 326 ≤ p
  · let u := ZMod.unitOfCoprime p (uff Nat.prime_nineteen hpn)
    have hu : u ≠ 1 := by
      intro h
      have hv := congrArg Units.val h
      simp only [u, ZMod.coe_unitOfCoprime, Units.val_one] at hv
      apply hmod
      simpa using (ZMod.natCast_eq_natCast_iff' p 1 19).mp hv
    have hord : 2 ≤ orderOf u := by
      exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨(orderOf_pos u).ne', orderOf_eq_one_iff.not.mpr hu⟩)
    rw [Nat.log_lt_iff_lt_pow hp.one_lt (by norm_num)]
    calc
      105933 < p ^ 2 := by nlinarith
      _ ≤ p ^ orderOf u := Nat.pow_le_pow_right (by omega) hord
  · have hpsmall : p ≤ 325 := by omega
    interval_cases p
    all_goals solve
      | norm_num at hp
      | norm_num at hpn
      | norm_num at hmod
      | norm_num [exceptionalNonSplitPrimesNineteen] at hmem
      | exact orderOf_lt_of (by norm_num) (by
          intro i hi hi1
          have hi16 : i ≤ 16 :=
            hi.trans (show Nat.log _ 105933 ≤ 16 by decide)
          have hipow := Nat.pow_le_of_le_log (by norm_num) hi
          interval_cases i
          all_goals solve
            | norm_num
            | norm_num at hipow)
