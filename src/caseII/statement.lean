import may_assume.lemmas

namespace flt_regular

/-- Statement of case II. -/
def caseII.statement : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ [hp : fact p.prime]
  (hreg : @is_regular_prime p hp)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- CaseII. -/
theorem caseII {a b c : ℤ} {p : ℕ} [fact p.prime] (hreg : is_regular_prime p)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseII : ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := sorry

end flt_regular
