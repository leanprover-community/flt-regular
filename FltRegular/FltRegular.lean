import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement
import Mathlib.NumberTheory.FLT.Basic

open FltRegular

/-- Fermat's last theorem for regular primes. -/
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : ↑p ∣ (a / d) * (b / d) * (c / d)
  · exact caseII hreg hodd hprod' hgcd case e'
  · exact caseI hreg case e'
