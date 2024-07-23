import FltRegular.FltRegular
import Mathlib.NumberTheory.Cyclotomic.PID

open Nat NumberField IsCyclotomicExtension

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

  refine flt_regular ?_ (by omega)
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.five_pid (CyclotomicField _ ℚ))
