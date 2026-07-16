import FltRegular.FltRegular
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

/-!
# Bernoulli-number certificate at 23

This file kernel-checks the elementary, finite part of Kummer's Bernoulli
criterion at the prime `23`: the reduced numerators of
`B_2, B_4, ..., B_20` are all nonzero modulo `23`.

The bridge from that finite calculation to regularity is deliberately an
explicit hypothesis.  Mathlib and `flt-regular` do not currently provide
Kummer's Bernoulli criterion, so this file neither postulates nor silently
assumes it.
-/

@[expose] public section

open Nat

namespace BealRegular.TwentyThreeBernoulli

private theorem prime_twentyThree : Nat.Prime 23 := by
  norm_num

local instance : Fact (Nat.Prime 23) := ⟨prime_twentyThree⟩

/-! ## Exact Bernoulli values -/

/-
The recursive calculations are kept as `bernoulli'` lemmas because that is
the recursion exposed by `Mathlib.NumberTheory.Bernoulli`.  At even indices,
`bernoulli` and `bernoulli'` agree.
-/

@[simp] private theorem bernoulli'_five_value : bernoulli' 5 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_six_value : bernoulli' 6 = (1 : ℚ) / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_seven_value : bernoulli' 7 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_eight_value : bernoulli' 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_nine_value : bernoulli' 9 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_ten_value : bernoulli' 10 = (5 : ℚ) / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_eleven_value : bernoulli' 11 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_twelve_value : bernoulli' 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_thirteen_value : bernoulli' 13 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_fourteen_value : bernoulli' 14 = (7 : ℚ) / 6 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_fifteen_value : bernoulli' 15 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_sixteen_value : bernoulli' 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_seventeen_value : bernoulli' 17 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_eighteen_value : bernoulli' 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

@[simp] private theorem bernoulli'_nineteen_value : bernoulli' 19 = 0 := by
  exact bernoulli'_eq_zero_of_odd (by norm_num) (by norm_num)

@[simp] private theorem bernoulli'_twenty_value : bernoulli' 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

theorem bernoulli_two_value : bernoulli 2 = (1 : ℚ) / 6 := by
  norm_num

theorem bernoulli_four_value : bernoulli 4 = (-1 : ℚ) / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_four

theorem bernoulli_six_value : bernoulli 6 = (1 : ℚ) / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_six_value

theorem bernoulli_eight_value : bernoulli 8 = (-1 : ℚ) / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_eight_value

theorem bernoulli_ten_value : bernoulli 10 = (5 : ℚ) / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_ten_value

theorem bernoulli_twelve_value : bernoulli 12 = (-691 : ℚ) / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_twelve_value

theorem bernoulli_fourteen_value : bernoulli 14 = (7 : ℚ) / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_fourteen_value

theorem bernoulli_sixteen_value : bernoulli 16 = (-3617 : ℚ) / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_sixteen_value

theorem bernoulli_eighteen_value : bernoulli 18 = (43867 : ℚ) / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_eighteen_value

theorem bernoulli_twenty_value : bernoulli 20 = (-174611 : ℚ) / 330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  exact bernoulli'_twenty_value

/-! ## Reduced numerators and their residues modulo 23 -/

theorem bernoulli_two_num : (bernoulli 2).num = (1 : ℤ) := by
  rw [bernoulli_two_value]
  norm_num

theorem bernoulli_four_num : (bernoulli 4).num = (-1 : ℤ) := by
  rw [bernoulli_four_value]
  norm_num

theorem bernoulli_six_num : (bernoulli 6).num = (1 : ℤ) := by
  rw [bernoulli_six_value]
  norm_num

theorem bernoulli_eight_num : (bernoulli 8).num = (-1 : ℤ) := by
  rw [bernoulli_eight_value]
  norm_num

theorem bernoulli_ten_num : (bernoulli 10).num = (5 : ℤ) := by
  rw [bernoulli_ten_value]
  norm_num

theorem bernoulli_twelve_num : (bernoulli 12).num = (-691 : ℤ) := by
  rw [bernoulli_twelve_value]
  norm_num

theorem bernoulli_fourteen_num : (bernoulli 14).num = (7 : ℤ) := by
  rw [bernoulli_fourteen_value]
  norm_num

theorem bernoulli_sixteen_num : (bernoulli 16).num = (-3617 : ℤ) := by
  rw [bernoulli_sixteen_value]
  norm_num

theorem bernoulli_eighteen_num : (bernoulli 18).num = (43867 : ℤ) := by
  rw [bernoulli_eighteen_value]
  norm_num

theorem bernoulli_twenty_num : (bernoulli 20).num = (-174611 : ℤ) := by
  rw [bernoulli_twenty_value]
  norm_num

theorem twentyThree_not_dvd_bernoulli_two_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 2).num) := by
  norm_num [bernoulli_two_num]

theorem twentyThree_not_dvd_bernoulli_four_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 4).num) := by
  norm_num [bernoulli_four_num]

theorem twentyThree_not_dvd_bernoulli_six_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 6).num) := by
  norm_num [bernoulli_six_num]

theorem twentyThree_not_dvd_bernoulli_eight_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 8).num) := by
  norm_num [bernoulli_eight_num]

theorem twentyThree_not_dvd_bernoulli_ten_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 10).num) := by
  norm_num [bernoulli_ten_num]

theorem twentyThree_not_dvd_bernoulli_twelve_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 12).num) := by
  norm_num [bernoulli_twelve_num]

theorem twentyThree_not_dvd_bernoulli_fourteen_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 14).num) := by
  norm_num [bernoulli_fourteen_num]

theorem twentyThree_not_dvd_bernoulli_sixteen_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 16).num) := by
  norm_num [bernoulli_sixteen_num]

theorem twentyThree_not_dvd_bernoulli_eighteen_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 18).num) := by
  norm_num [bernoulli_eighteen_num]

theorem twentyThree_not_dvd_bernoulli_twenty_num :
    ¬ ((23 : ℤ) ∣ (bernoulli 20).num) := by
  norm_num [bernoulli_twenty_num]

/-!
`BernoulliNumeratorCondition p` is exactly the finite numerator condition
appearing in the usual Bernoulli formulation of Kummer's criterion: for
`1 ≤ k` and `2k ≤ p - 3`, the reduced numerator of `B_(2k)` is not
divisible by `p`.
-/
def BernoulliNumeratorCondition (p : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 * k ≤ p - 3 →
    ¬ ((p : ℤ) ∣ (bernoulli (2 * k)).num)

theorem twentyThree_bernoulliNumeratorCondition :
    BernoulliNumeratorCondition 23 := by
  intro k hk htop
  have hk_le : k ≤ 10 := by omega
  interval_cases k <;>
    norm_num [bernoulli_two_num, bernoulli_four_num, bernoulli_six_num,
      bernoulli_eight_num, bernoulli_ten_num, bernoulli_twelve_num,
      bernoulli_fourteen_num, bernoulli_sixteen_num, bernoulli_eighteen_num,
      bernoulli_twenty_num] at hk htop ⊢

/-! ## Assumption-explicit Kummer bridge and FLT endpoint -/

/--
The exact implication needed from Kummer's criterion.  This is a proposition,
not an axiom or instance: clients must supply a proof of it.
-/
def KummerBernoulliImplication (p : ℕ) [Fact p.Prime] : Prop :=
  BernoulliNumeratorCondition p → IsRegularPrime p

/-- The computed finite certificate implies regularity once the missing
Kummer criterion is supplied explicitly. -/
theorem isRegularPrime_twentyThree_of_kummerBernoulli
    (hKummer : KummerBernoulliImplication 23) : IsRegularPrime 23 :=
  hKummer twentyThree_bernoulliNumeratorCondition

/-- The same supplied criterion reaches the existing regular-prime FLT
theorem.  No proof of Kummer's criterion is claimed here. -/
theorem fermatLastTheoremTwentyThree_of_kummerBernoulli
    (hKummer : KummerBernoulliImplication 23) : FermatLastTheoremFor 23 :=
  flt_regular (isRegularPrime_twentyThree_of_kummerBernoulli hKummer) (by norm_num)

end BealRegular.TwentyThreeBernoulli
