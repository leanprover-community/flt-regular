import FltRegular.SmallNumbers.Cyclotomic
import FltRegular.SmallNumbers.OrderOf
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Bounds and arithmetic for a certificate at the regular prime 17

This file follows the certificate architecture used by the upstream proofs for
7, 11, and 13.  External algebra software was used only to discover polynomial
identities; Lean checks every identity below.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem Nat.prime_seventeen : Nat.Prime 17 := by
  norm_num

instance Nat.fact_prime_seventeen : Fact (Nat.Prime 17) :=
  ⟨Nat.prime_seventeen⟩

lemma crazy17 :
    ⌊(4 / π) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793)⌋₊ = 13254 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 8 *
          (16! / 16 ^ 16 * √2862423051509815793) := by
        gcongr
        exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 8 *
          (16! / 16 ^ 16 * 1691869691) := by
        gcongr
        exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 13254 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 8 *
          (16! / 16 ^ 16 * √2862423051509815793) := by
        gcongr
        exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 8 *
          (16! / 16 ^ 16 * 1691869692) := by
        gcongr
        exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ 13254 + 1 := by norm_num

variable [IsCyclotomicExtension {17} ℚ K]

theorem M17 : ⌊(M K)⌋₊ = 13254 := by
  rw [discr_prime 17 K, IsCyclotomicExtension.finrank (n := 17) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 17, totient_prime
      Nat.prime_seventeen]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow, reduceSub,
    one_mul, Int.cast_ofNat, abs_ofNat]
  exact crazy17

theorem cyclotomic_17 : cyclotomic 17 ℤ =
    X^16 + X^15 + X^14 + X^13 + X^12 + X^11 + X^10 + X^9 + X^8 +
      X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ]
  ring

/-! Only the primes below fail the inexpensive `p ^ order > M` branch of
`pid6`.  This finite list is independently checked in the next two lemmas. -/

def exceptionalPrimesSeventeen : Finset ℕ :=
  [2, 67, 101, 103, 137, 239, 307, 409, 443, 613, 647, 919, 953, 1021, 1123, 1259,
    1327, 1361, 1429, 1531, 1667, 1871, 1973, 2143, 2347, 2381, 2551, 2687, 2789,
    2857, 3061, 3163, 3299, 3469, 3571, 3673, 3877, 3911, 4013, 4217, 4421, 4523,
    4591, 4931, 4999, 5101, 5237, 5407, 5441, 5849, 6053, 6121, 6257, 6359, 6427,
    6529, 6563, 6733, 6869, 6971, 7039, 7243, 7481, 7549, 7583, 7753, 8059, 8093,
    8161, 8263, 8297, 8467, 8501, 8807, 9011, 9181, 9283, 9419, 9521, 9623, 9929,
    10099, 10133, 10303, 10337, 10711, 10847, 10949, 11119, 11527, 11731, 11833,
    11867, 11969, 12037, 12071, 12241, 12343, 12377, 12479, 12547, 12853,
    13159].toFinset

set_option linter.unusedTactic false in
set_option maxHeartbeats 0 in
-- Exhaustively checks the 780 possible values of `p / 17` below the bound.
theorem prime_mem_exceptionalPrimesSeventeen_of_mod_eq_one {p : ℕ}
    (hp : p.Prime) (hple : p ≤ 13254) (hmod : p % 17 = 1) :
    p ∈ exceptionalPrimesSeventeen := by
  let k := p / 17
  have hpform : p = 17 * k + 1 := by
    dsimp [k]
    omega
  have hk : k ≤ 779 := by omega
  interval_cases k <;> subst_vars
  all_goals solve
    | norm_num at hp
    | norm_num [exceptionalPrimesSeventeen]

set_option linter.unusedTactic false in
set_option maxHeartbeats 0 in
-- Reuses the finite classification above and checks the remaining small primes.
theorem log_lt_orderOf_seventeen_of_not_mem {p : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hpn : p ≠ 17) (hple : p ≤ 13254)
    (hmem : p ∉ exceptionalPrimesSeventeen) :
    Nat.log p 13254 <
      orderOf (ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)) := by
  by_cases hpge : 116 ≤ p
  · by_cases hmod : p % 17 = 1
    · exact (hmem (prime_mem_exceptionalPrimesSeventeen_of_mod_eq_one hp hple hmod)).elim
    · let u := ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)
      have hu : u ≠ 1 := by
        intro h
        have hv := congrArg Units.val h
        simp only [u, ZMod.coe_unitOfCoprime, Units.val_one] at hv
        apply hmod
        simpa using (ZMod.natCast_eq_natCast_iff' p 1 17).mp hv
      have hord : 2 ≤ orderOf u := by
        exact (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
          ⟨(orderOf_pos u).ne', orderOf_eq_one_iff.not.mpr hu⟩)
      rw [Nat.log_lt_iff_lt_pow hp.one_lt (by norm_num)]
      calc
        13254 < p ^ 2 := by nlinarith
        _ ≤ p ^ orderOf u := Nat.pow_le_pow_right (by omega) hord
  · have hpsmall : p ≤ 115 := by omega
    by_cases hpge11 : 11 ≤ p
    · have hmod1 : p % 17 ≠ 1 := by
        intro hmod
        exact hmem (prime_mem_exceptionalPrimesSeventeen_of_mod_eq_one hp hple hmod)
      have hmod16 : p % 17 ≠ 16 := by
        intro hmod
        let k := p / 17
        have hpform : p = 17 * k + 16 := by
          dsimp [k]
          omega
        have hk : k ≤ 5 := by omega
        interval_cases k <;> subst_vars
        all_goals solve
          | norm_num at hp
          | norm_num [exceptionalPrimesSeventeen] at hmem
      have hlog : Nat.log p 13254 ≤ 3 := by
        rw [← Nat.lt_succ_iff, Nat.log_lt_iff_lt_pow hp.one_lt (by norm_num)]
        have hpow : 11 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hpge11 4
        norm_num at hpow ⊢
        omega
      refine hlog.trans_lt (orderOf_lt_of _ ?_)
      intro i hi hi1
      interval_cases i
      all_goals
        rw [Nat.pow_mod]
        have hr : p % 17 < 17 := Nat.mod_lt _ (by norm_num)
        interval_cases hres : p % 17
        all_goals solve
          | norm_num at hmod1
          | norm_num at hmod16
          | norm_num
    · have hpne2 : p ≠ 2 := by
        intro h
        subst p
        norm_num [exceptionalPrimesSeventeen] at hmem
      have hple10 : p ≤ 10 := by omega
      interval_cases p
      all_goals solve
        | norm_num at hp
        | omega
        | exact lt_of_le_of_lt (show Nat.log _ 13254 ≤ 8 by decide)
            (orderOf_lt_of _ (by
              intro i hi hi1
              interval_cases i <;> norm_num))
