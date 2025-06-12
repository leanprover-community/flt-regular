import FltRegular.FltRegular
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.Stuff.Thirteen

open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_thirteen : IsRegularPrime 13 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 pid13

theorem fermatLastTheoremThirteen : FermatLastTheoremFor 13 :=
  flt_regular isRegularPrime_thirteen (by omega)
