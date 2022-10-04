import may_assume.lemmas

namespace flt_regular

/-- Statement of case II. -/
def caseII.statement : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- CaseII. -/
theorem caseII {a b c : ℤ} {p : ℕ} (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := sorry

end flt_regular
