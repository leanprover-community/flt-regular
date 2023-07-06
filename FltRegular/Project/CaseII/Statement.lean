import FltRegular.MayAssume.Lemmas

namespace FltRegular

/-- Statement of case II. -/
def CaseII.Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ [hp : Fact p.Prime] (hreg : @IsRegularPrime p hp) (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- CaseII. -/
theorem caseII {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  sorry

end FltRegular

