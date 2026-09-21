module

public import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

import FltRegular.FltRegular
public import FltRegular.NumberTheory.RegularPrimes

/-!
# Fermat's Last Theorem for exponent five

This file proves that `5` is regular and applies the regular-prime theorem to exponent `5`.
-/

@[expose] public section

open Nat NumberField IsCyclotomicExtension

/-- Five is a regular prime. -/
theorem isRegularPrime_five : IsRegularPrime 5 :=
  have := Rat.five_pid (CyclotomicField 5 ℚ)
  isRegularPrime_of_isPrincipalIdealRing 5

/-- Fermat's Last Theorem for exponent five. -/
theorem fermatLastTheoremFive : FermatLastTheoremFor 5 :=
  @flt_regular 5 ⟨Nat.prime_five⟩ isRegularPrime_five (by omega)
