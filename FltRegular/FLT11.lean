import FltRegular.FltRegular
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.Stuff.Eleven

open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_eleven : IsRegularPrime 11 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 pid11

theorem fermatLastTheoremEleven : FermatLastTheoremFor 11 :=
  flt_regular isRegularPrime_eleven (by omega)
