import Mathlib
import FltRegular

open Nat NumberField Polynomial IsPrimitiveRoot IsCyclotomicExtension Real Complex
open scoped nonZeroDivisors

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩

  refine flt_regular ?_ (by omega)
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.five_pid (CyclotomicField _ ℚ))
