module

public import FltRegular.NumberTheory.RegularPrimes
public import Mathlib.NumberTheory.FLT.Basic
import FltRegular.FltRegular
import Mathlib.Tactic.NormNum.Prime
public import FltRegular.SmallNumbers.Thirteen.Thirteen

@[expose] public section

open Nat NumberField IsCyclotomicExtension

set_option backward.isDefEq.respectTransparency false in
theorem isRegularPrime_thirteen :
    haveI : Fact (Nat.Prime 13) := ⟨Nat.prime_thirteen⟩
    IsRegularPrime 13 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.thirteen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremThirteen : FermatLastTheoremFor 13 :=
  @flt_regular 13 ⟨Nat.prime_thirteen⟩ isRegularPrime_thirteen (by omega)
