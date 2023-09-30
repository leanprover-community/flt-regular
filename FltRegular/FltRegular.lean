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
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : ↑p ∣ (a / d) * (b / d) * (c / d)
  exact caseII hreg hodd hprod' hgcd case e'
  exact caseI hreg case e'
