module

public import Mathlib.NumberTheory.FLT.Basic
import FltRegular.SmallNumbers.Eleven.FLT11
import FltRegular.SmallNumbers.Five.FLT5
import FltRegular.SmallNumbers.Seven.FLT7
import FltRegular.SmallNumbers.Thirteen.FLT13
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem FLT_small {n : ℕ} (hn : n ∈ Finset.Icc 3 16) : FermatLastTheoremFor n := by
  fin_cases hn
  · exact fermatLastTheoremThree
  · exact fermatLastTheoremFour
  · exact fermatLastTheoremFive
  · apply FermatLastTheoremFor.mono (show 3 ∣ 6 by decide)
    exact fermatLastTheoremThree
  · exact fermatLastTheoremSeven
  · apply FermatLastTheoremFor.mono (show 4 ∣ _ by decide)
    exact fermatLastTheoremFour
  · apply FermatLastTheoremFor.mono (show 3 ∣ 9 by decide)
    exact fermatLastTheoremThree
  · apply FermatLastTheoremFor.mono (show 5 ∣ 10 by decide)
    exact fermatLastTheoremFive
  · exact fermatLastTheoremEleven
  · apply FermatLastTheoremFor.mono (show 4 ∣ 12 by decide)
    exact fermatLastTheoremFour
  · exact fermatLastTheoremThirteen
  · apply FermatLastTheoremFor.mono (show 7 ∣ 14 by decide)
    exact fermatLastTheoremSeven
  · apply FermatLastTheoremFor.mono (show 5 ∣ 15 by decide)
    exact fermatLastTheoremFive
  · apply FermatLastTheoremFor.mono (show 4 ∣ 16 by decide)
    exact fermatLastTheoremFour
