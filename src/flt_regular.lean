import caseI.statement
import caseII.statement

open flt_regular

/-- Statement of Fermat's last theorem for regular primes. -/
def flt_regular.statement : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hodd : p ≠ 2) (hprod : a * b * c ≠ 0),
  a ^ p + b ^ p ≠ c ^ p

/-- Fermat's last theorem for regular primes.. -/
theorem flt_regular {a b c : ℤ} {p : ℕ} (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) : a ^ p + b ^ p ≠ c ^ p :=
begin
  by_cases case : ↑p ∣ a * b * c,
  exact caseII hpri hreg hodd hprod case,
  exact caseI hpri hreg hodd case
end
