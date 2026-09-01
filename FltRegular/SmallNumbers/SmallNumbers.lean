module

public import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic.NormNum.Prime

import FltRegular.SmallNumbers.Five.FLT5
import FltRegular.SmallNumbers.Seven.FLT7

/-!
# Fermat's Last Theorem for exponents from three through ten

This file combines the known results for exponents `3`, `4`, `5`, and `7` with divisibility of
exponents to cover the interval from `3` through `10`.
-/

@[expose] public section

/-- Fermat's Last Theorem holds for every exponent in the interval `[3, 10]`. -/
theorem FLT_small {n : ℕ} (hn : n ∈ Finset.Icc 3 10) : FermatLastTheoremFor n := by
  fin_cases hn
  · exact fermatLastTheoremThree
  · exact fermatLastTheoremFour
  · exact fermatLastTheoremFive
  · exact fermatLastTheoremThree.mono (show 3 ∣ 6 by decide)
  · exact fermatLastTheoremSeven
  · exact fermatLastTheoremFour.mono (show 4 ∣ 8 by decide)
  · exact fermatLastTheoremThree.mono (show 3 ∣ 9 by decide)
  · exact fermatLastTheoremFive.mono (show 5 ∣ 10 by decide)
