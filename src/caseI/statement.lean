import may_assume.lemmas
import number_theory.cyclotomic.factoring
import number_theory.cyclotomic.Unit_lemmas
import ready_for_mathlib.exists_eq_pow_of_mul_eq_pow

open finset nat is_cyclotomic_extension ideal polynomial int

open_locale big_operators number_field

namespace flt_regular

variables {p : ℕ} (hpri : p.prime)

local notation `P` := (⟨p, hpri.pos⟩ : ℕ+)
local notation `K` := cyclotomic_field P ℚ
local notation `R` := 𝓞 K

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

lemma ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id)) : is_coprime a b  :=
begin
  rw [← gcd_eq_one_iff_coprime],
  by_contra' h,
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h,
  replace hqpri : prime (q : ℤ) := prime_iff_nat_abs_prime.2 (by simp [hqpri]),
  obtain ⟨n, hn⟩ := hq,
  have haq : ↑q ∣ a,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_left a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hbq : ↑q ∣ b,
  { obtain ⟨m, hm⟩ := int.gcd_dvd_right a b,
    exact ⟨n * m, by { rw [hm, hn], simp [mul_assoc] }⟩ },
  have hcq : ↑q ∣ c,
  { suffices : ↑q ∣ c ^ p,
    { exact hqpri.dvd_of_dvd_pow this },
    rw [← H],
    exact dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero) },
  have Hq : ↑q ∣ ({a, b, c} : finset ℤ).gcd id,
  { refine dvd_gcd (λ x hx, _),
    simp only [mem_insert, mem_singleton] at hx,
    rcases hx with H | H | H;
    simpa [H] },
  exact not_is_unit_of_not_is_unit_dvd hqpri.not_unit Hq hgcd
end

theorem exist_ideal {a b c : ℤ} (h5p : 5 ≤ p)
  (H : a ^ p + b ^ p = c ^ p)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (caseI : ¬ ↑p ∣ a * b * c) :
  ∀ i ∈ nth_roots_finset p R, ∃ I, span ({a + i * b} : set R) = I ^ p :=
begin
  have h5P : 5 ≤ P := h5p,
  haveI : fact ((P : ℕ).prime) := ⟨hpri⟩,
  classical,
  have H₁ := congr_arg (algebra_map ℤ R) H,
  simp only [eq_int_cast, int.cast_add, int.cast_pow] at H₁,
  have hζ := is_primitive_root.unit'_coe (zeta_spec P ℚ K),
  rw [pow_add_pow_eq_prod_add_zeta_runity_mul (or.resolve_left (prime.eq_two_or_odd hpri)
    (λ _, by linarith)) hζ] at H₁,
  replace H₁ := congr_arg (λ x, span ({x} : set R)) H₁,
  simp only [span_singleton_prod, ← span_singleton_pow] at H₁,
  intros i hi,
  obtain ⟨I, hI⟩ := exists_eq_pow_of_prod_eq_pow p (span ({c} : set R)) (λ η₁ hη₁ η₂ hη₂ hη, _) H₁ i hi,
  { exact ⟨I, hI⟩ },
  { exact flt_ideals_coprime h5P H (ab_coprime H hpri.ne_zero hgcd) hη₁ hη₂ hη caseI }
end

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} {p : ℕ} (hpri : p.prime)
  (hreg : is_regular_number p hpri.pos) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (hgcd : is_unit (({a, b, c} : finset ℤ).gcd id))
  (hab : ¬a ≡ b [ZMOD p]) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
begin
  sorry
end

/-- CaseI. -/
theorem caseI {a b c : ℤ} {p : ℕ} (hpri : p.prime) (hreg : is_regular_number p hpri.pos)
  (hodd : p ≠ 2) (hprod : a * b * c ≠ 0) (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
flt_regular.caseI.may_assume (λ x y z p₁ Hpri Hreg HP5 Hprod Hunit Hxy HI,
    caseI_easier Hpri Hreg HP5 Hprod Hunit Hxy HI) hpri hreg hodd hprod caseI

end flt_regular
