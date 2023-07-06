import FltRegular.CaseI.Statement
import FltRegular.CaseII.Statement

open flt_regular

/-- Statement of Fermat's last theorem for regular primes. -/
def FltRegular.Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ [hpri : Fact p.Prime] (hreg : @IsRegularPrime p hpri) (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0), a ^ p + b ^ p ≠ c ^ p

/-- Fermat's last theorem for regular primes.. -/
theorem flt_regular {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) : a ^ p + b ^ p ≠ c ^ p :=
  by
  by_cases case : ↑p ∣ a * b * c
  exact caseII hreg hodd hprod case
  exact caseI hreg case

