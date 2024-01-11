import Mathlib
import FltRegular

open Nat NumberField Polynomial IsPrimitiveRoot
open scoped nonZeroDivisors

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  have five_pos : 0 < 5 := by norm_num
  let p := (⟨5, five_pos⟩ : ℕ+)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hodd : 5 ≠ 2 := by omega
  have hp : Fact (Nat.Prime (↑p : ℕ)) := this
  let K := CyclotomicField p ℚ
  let pB := integralPowerBasis' (hp := hp)
    (IsCyclotomicExtension.zeta_spec (⟨5, five_pos⟩ : ℕ+) ℚ K)

  refine flt_regular ?_ hodd
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  apply classNumber_eq_one_of_abs_discr_lt
  rw [IsCyclotomicExtension.finrank (n := 5) K (cyclotomic.irreducible_rat five_pos),
    ← discr_eq_discr _ pB.basis]
  sorry
