module

public import Mathlib.NumberTheory.FLT.Basic
public import FltRegular.NumberTheory.RegularPrimes
import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement
import FltRegular.MayAssume.Lemmas

@[expose] public section

open FltRegular

/-- Fermat's last theorem for regular primes. -/
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  rw [fermatLastTheoremFor_iff_int]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd
  by_cases case : ↑p ∣ a * b * c
  · exact caseII hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd case
  · exact caseI hreg case
