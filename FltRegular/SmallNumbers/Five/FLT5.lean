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

set_option backward.isDefEq.respectTransparency false in
/-- Five is a regular prime. -/
theorem isRegularPrime_five :
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    IsRegularPrime 5 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.five_pid (CyclotomicField _ ℚ))

/-- Fermat's Last Theorem for exponent five. -/
theorem fermatLastTheoremFive : FermatLastTheoremFor 5 :=
  @flt_regular 5 ⟨Nat.prime_five⟩ isRegularPrime_five (by omega)
