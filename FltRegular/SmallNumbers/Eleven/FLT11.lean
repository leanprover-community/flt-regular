module

public import FltRegular.NumberTheory.RegularPrimes
public import Mathlib.NumberTheory.FLT.Basic
import FltRegular.FltRegular
import FltRegular.SmallNumbers.Eleven.Eleven
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_eleven :
    haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    IsRegularPrime 11 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.eleven_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremEleven : FermatLastTheoremFor 11 := by
  have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  exact flt_regular isRegularPrime_eleven (by omega)
