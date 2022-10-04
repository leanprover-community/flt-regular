import may_assume.lemmas

open finset

namespace flt_regular

namespace caseI

/-- Statement of case I with additional assumptions. -/
def slightly_easier : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

/-- Statement of case I. -/
def statement : Prop := ∀ ⦃a b c : ℤ⦄ ⦃p : ℕ⦄ (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseI : ¬ ↑p ∣ a * b * c), a ^ p + b ^ p ≠ c ^ p

lemma may_assume : slightly_easier → statement :=
begin
  intro Heasy,
  intros a b c p hpri hreg hodd hprod hI H,
  have hp5 : 5 ≤ p,
  { by_contra' habs,
    have : p ∈ finset.Ioo 2 5 := finset.mem_Icc.2 ⟨nat.lt_of_le_and_ne hpri.two_le hodd.symm,
      by linarith⟩,
    fin_cases this,
    { exact may_assume.p_ne_three hprod H rfl },
    { rw [show 4 = 2 * 2, from rfl] at hpri,
      refine nat.not_prime_mul one_lt_two one_lt_two hpri } },
  rcases may_assume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩,
  let d := ({a, b, c} : finset ℤ).gcd id,
  have hdiv : ¬↑p ∣ (a / d) * (b / d) * (c / d),
  { have hadiv : d ∣ a := gcd_dvd (by simp),
    have hbdiv : d ∣ b := gcd_dvd (by simp),
    have hcdiv : d ∣ c := gcd_dvd (by simp),
    intro hdiv,
    replace hdiv := dvd_mul_of_dvd_right hdiv ((d * d) * d),
    rw [mul_assoc, ← mul_assoc d, ← mul_assoc d, int.mul_div_cancel' hadiv, mul_assoc,
      mul_comm a, mul_assoc (b / d), ← mul_assoc _ (b / d), int.mul_div_cancel' hbdiv,
      mul_comm, mul_assoc, mul_assoc, int.div_mul_cancel hcdiv, mul_comm, mul_assoc,
      mul_comm c, ← mul_assoc] at hdiv,
    exact hI hdiv },
  obtain ⟨X, Y, Z, H1, H2, H3, H4, H5⟩ := a_not_cong_b hpri hp5 hprodxyx Hxyz hunit hdiv,
  exact Heasy hpri hreg hp5 H4 H2 H3 (λ hfin, H5 hfin) H1
end

end caseI

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} {p : ℕ} (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := sorry

/-- CaseI. -/
theorem caseI {a b c : ℤ} {p : ℕ} (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
flt_regular.caseI.may_assume (λ x y z P Hpri Hreg HP5 Hprod Hunit Hxy HI,
    caseI_easier Hpri Hreg HP5 Hprod Hunit Hxy HI) hpri hreg hodd hprod caseI

end flt_regular
