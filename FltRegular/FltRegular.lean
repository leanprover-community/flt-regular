import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement
import Mathlib.NumberTheory.FLT.Basic

open FltRegular

/-- Statement of Fermat's last theorem for regular primes. -/
def FltRegular.Statement : Prop :=
  ∀ ⦃p : ℕ⦄ [Fact p.Prime], IsRegularPrime p → p ≠ 2 → FermatLastTheoremWith ℤ p

/-- Fermat's last theorem for regular primes. -/
theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremWith ℤ p := by
  intro a b c ha hb hc
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  by_cases case : ↑p ∣ a * b * c
  exact caseII hreg hodd hprod case
  exact caseI hreg case
