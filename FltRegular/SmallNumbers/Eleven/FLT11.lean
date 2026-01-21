module

public import FltRegular.FltRegular
public import FltRegular.SmallNumbers.Eleven.Eleven

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
