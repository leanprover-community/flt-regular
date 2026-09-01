module

public import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Tactic.NormNum.Prime

import FltRegular.FltRegular
public import FltRegular.NumberTheory.RegularPrimes
import FltRegular.SmallNumbers.Seven.Seven

/-!
# Fermat's Last Theorem for exponent seven

This file proves that `7` is regular and applies the regular-prime theorem to exponent `7`.
-/

@[expose] public section

open Nat NumberField IsCyclotomicExtension

set_option backward.isDefEq.respectTransparency false in
/-- Seven is a regular prime. -/
theorem isRegularPrime_seven :
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    IsRegularPrime 7 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.seven_pid (CyclotomicField _ ℚ))

/-- Fermat's Last Theorem for exponent seven. -/
theorem fermatLastTheoremSeven : FermatLastTheoremFor 7 :=
  @flt_regular 7 ⟨Nat.prime_seven⟩ isRegularPrime_seven (by omega)
