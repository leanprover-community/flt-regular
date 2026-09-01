module

public import Mathlib.NumberTheory.FLT.Basic

public import FltRegular.NumberTheory.RegularPrimes
import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement
import FltRegular.MayAssume.Lemmas

/-!
# Fermat's Last Theorem for regular primes

This file combines the first and second cases to prove Fermat's Last Theorem at every odd regular
prime exponent.
-/

@[expose] public section

open FltRegular

/-- Fermat's last theorem for regular primes. -/
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  rw [fermatLastTheoremFor_iff_int]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd
  by_cases hcase : ↑p ∣ a * b * c
  · exact caseII hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd hcase
  · exact caseI hreg hcase
