module

public import Mathlib.NumberTheory.FLT.Basic
import FltRegular.SmallNumbers.Five.FLT5
import FltRegular.SmallNumbers.Seven.FLT7
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

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
