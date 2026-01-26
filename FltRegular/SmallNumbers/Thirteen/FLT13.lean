module

public import FltRegular.NumberTheory.RegularPrimes
public import Mathlib.NumberTheory.FLT.Basic
public import FltRegular.SmallNumbers.Thirteen.Thirteen
import FltRegular.FltRegular
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_thirteen :
    haveI : Fact (Nat.Prime 13) := ⟨Nat.prime_thirteen⟩
    IsRegularPrime 13 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.thirteen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremThirteen : FermatLastTheoremFor 13 := by
  have : Fact (Nat.Prime 13) := ⟨Nat.prime_thirteen⟩
  exact flt_regular isRegularPrime_thirteen (by omega)
