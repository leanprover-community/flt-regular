import FltRegular.FltRegular
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.Stuff.Seven

open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_seven : IsRegularPrime 7 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 pid7

theorem fermatLastTheoremSeven : FermatLastTheoremFor 7 :=
  flt_regular isRegularPrime_seven (by omega)
