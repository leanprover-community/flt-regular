module

public import Mathlib.NumberTheory.FLT.Basic

public import FltRegular.NumberTheory.RegularPrimes
import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement

/-!
# Fermat's Last Theorem for regular primes

This file combines the first and second cases to prove Fermat's Last Theorem at every odd regular
prime exponent.
-/

@[expose] public section

open FltRegular

/-- Fermat's last theorem for regular primes. -/
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p :=
  fermatLastTheoremFor_iff_int.2 <| fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
    fun a b c ha hb hc hgcd ↦ if hcase : ↑p ∣ a * b * c then
      caseII hreg hodd (by simp [ha, hb, hc]) hgcd hcase
    else caseI hreg hcase
