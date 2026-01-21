module

public import FltRegular.SmallNumbers.Five.FLT5
public import FltRegular.SmallNumbers.Seven.FLT7
public import FltRegular.SmallNumbers.Eleven.FLT11
public import FltRegular.SmallNumbers.Thirteen.FLT13
public import Mathlib.NumberTheory.FLT.Four

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
