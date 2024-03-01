import Mathlib
import FltRegular

open Nat NumberField Polynomial IsPrimitiveRoot IsCyclotomicExtension Real Complex
open scoped nonZeroDivisors

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  classical
  have five_pos : 0 < 5 := by norm_num
  let p := (⟨5, five_pos⟩ : ℕ+)
  have hφ : φ 5 = 4 := rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hodd : 5 ≠ 2 := by omega
  have hp : Fact (Nat.Prime (↑p : ℕ)) := this
  let K := CyclotomicField p ℚ

  refine flt_regular ?_ hodd
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  refine classNumber_eq_one_iff.2 (RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_)
  suffices : discr K = 125
  rw [IsCyclotomicExtension.finrank (n := 5) K (cyclotomic.irreducible_rat five_pos), this]
  · suffices InfinitePlace.NrComplexPlaces K = 2 by
      · rw [this, show ((5 : ℕ+) : ℕ) = 5 by rfl, hφ, show ((4! : ℕ) : ℝ) = 24 by rfl,
          abs_of_pos (by norm_num)]
        norm_num
        suffices (2 * (3 ^ 2 / 16) * (32 / 3)) ^ 2 < (2 * ((π : ℝ) ^ 2 / 16) * (32 / 3)) ^ 2 by
          · refine lt_trans ?_ this
            norm_num
        gcongr
        exact pi_gt_three
    rw [Rat.nrComplexPlaces_eq_totient_div_two (n := 5)]
    rfl
  · convert IsCyclotomicExtension.Rat.absdiscr_prime p K
    assumption
