import flt_three.flt_three
import algebra.gcd_monoid.finset
import field_theory.finite.basic
import ready_for_mathlib.gcd
import number_theory.regular_primes

open int finset

namespace flt_regular

namespace may_assume

lemma p_ne_three {a b c : ℤ} {n : ℕ} (hprod : a * b * c ≠ 0)
  (h : a ^ n + b ^ n = c^ n) : n ≠ 3 :=
begin
  intro hn,
  have ha : a ≠ 0 := λ ha, by simpa [ha] using hprod,
  have hb : b ≠ 0 := λ hb, by simpa [hb] using hprod,
  have hc : c ≠ 0 := λ hc, by simpa [hc] using hprod,
  simpa [hn, flt_three ha hb hc] using h
end

lemma coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
  let d := ({a, b, c} : finset ℤ).gcd id in
  (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
  is_unit (({a / d, b / d, c / d} : finset ℤ).gcd id) ∧
  (a / d) * (b / d) * (c / d) ≠ 0 :=
begin
  have ha : a ≠ 0 := λ ha, by simpa [ha] using hprod,
  have hb : b ≠ 0 := λ hb, by simpa [hb] using hprod,
  have hc : c ≠ 0 := λ hc, by simpa [hc] using hprod,
  let s : finset ℤ := {a, b, c},
  set d : ℤ := s.gcd id with hddef,
  have hadiv : d ∣ a := gcd_dvd (by simp),
  have hazero : a / d ≠ 0 := λ habs, ha (int.eq_zero_of_div_eq_zero hadiv habs),
  have hbdiv : d ∣ b := gcd_dvd (by simp),
  have hbzero : b / d ≠ 0 := λ habs, hb (int.eq_zero_of_div_eq_zero hbdiv habs),
  have hcdiv : d ∣ c := gcd_dvd (by simp),
  have hczero : c / d ≠ 0 := λ habs, hc (int.eq_zero_of_div_eq_zero hcdiv habs),
  have hdzero : d ≠ 0 := λ hdzero, by simpa [ha] using finset.gcd_eq_zero_iff.1 hdzero a (by simp),
  have h0 : (({a / d, b / d, c / d} : finset ℤ).gcd id) ≠ 0 := λ h0,
    ha (int.eq_zero_of_div_eq_zero (show d ∣ a, from gcd_dvd (by simp))
    (by convert finset.gcd_eq_zero_iff.1 h0 (a / d) (by simp))),
  have him : {a / d, b / d, c / d} = ({a, b, c} : finset ℤ).image (λ x, x / d) := by simp,
  have hdp : d ^ n ≠ 0 := λ hdn, hdzero (pow_eq_zero hdn),
  refine ⟨_, _, λ habs, _⟩,
  { obtain ⟨na, hna⟩ := hadiv, obtain ⟨nb, hnb⟩ := hbdiv, obtain ⟨nc, hnc⟩ := hcdiv,
    rw [← hddef],
    simpa [hna, hnb, hnc, mul_pow, hdzero, int.add_mul_div_left (d ^ n * na ^ n) (nb ^ n), hdp]
      using congr_arg (/ d ^ n) H },
  { convert is_unit_div_gcd_id ({a, b, c} : finset ℤ) (show a ∈ _, by simp) ha using 1,
    rw [finset.gcd, him, fold_image (λ x hx y hy hxy, (int.div_left_inj _ _).1 hxy)],
    { refl },
    { simp only [mem_insert, mem_singleton] at hx,
      rcases hx with hxa | hxb | hxc,
      rw [hxa], assumption, rw [hxb], assumption, rw [hxc], assumption },
    { simp only [mem_insert, mem_singleton] at hy,
      rcases hy with hya | hyb | hyc,
      rw [hya], assumption, rw [hyb], assumption, rw [hyc], assumption } },
  { simp only [mul_eq_zero] at habs,
    rcases habs with (Ha | Hb) | Hc,
    { exact ha (int.eq_zero_of_div_eq_zero (by exact gcd_dvd (by simp)) Ha) },
    { exact hb (int.eq_zero_of_div_eq_zero (by exact gcd_dvd (by simp)) Hb) },
    { exact hc (int.eq_zero_of_div_eq_zero (by exact gcd_dvd (by simp)) Hc) } }
end

end may_assume

lemma p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.prime) (hp : p ≠ 3)
  (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p]) (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c :=
begin
  letI : fact p.prime := ⟨hpri⟩,
  replace h := congr_arg (λ (n : ℤ), (n : zmod p)) h,
  simp only [int.coe_nat_pow, int.cast_add, int.cast_pow, zmod.pow_card] at h,
  simp only [← zmod.int_coe_eq_int_coe_iff, int.cast_neg] at hbc hab,
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← int.cast_neg, ← int.cast_sub,
    ← int.cast_sub] at h,
  ring_nf at h,
  simp only [int.cast_neg, int.cast_mul, int.cast_bit1, int.cast_one, int.cast_coe_nat,
    neg_eq_zero, mul_eq_zero] at h,
  rw [← zmod.int_coe_zmod_eq_zero_iff_dvd],
  refine or.resolve_left h (λ h3, _),
  rw [show (3 : zmod p) = ↑(3 : ℕ), by simp, zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.dvd_prime
    (nat.prime_three)] at h3,
  cases h3 with H₁ H₂,
  { exact hpri.ne_one H₁ },
  { exact hp H₂ }
end

lemma a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.prime) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
  (h : a ^ p + b ^ p = c ^ p) (hunit : is_unit (({a, b, c} : finset ℤ).gcd id))
  (caseI : ¬ ↑p ∣ (a * b * c)) :
  ∃ (x y z : ℤ), x ^ p + y ^ p = z ^ p ∧
  is_unit (({x, y, z} : finset ℤ).gcd id) ∧
  ¬x ≡ y [ZMOD p] ∧
  x * y * z ≠ 0 ∧
  ¬ ↑p ∣ x * y * z :=
begin
  by_cases H : a ≡ b [ZMOD p],
  swap,
  { exact ⟨a, b, c, ⟨h, hunit, H, hprod, caseI⟩⟩ },
  refine ⟨a, -c, -b, ⟨_, _, λ habs, _, _, _⟩⟩,
  { have hpodd : p ≠ 2 := by linarith,
    simp only [neg_pow, (or.resolve_left hpri.eq_two_or_odd' hpodd).neg_one_pow, neg_one_mul,
      ← sub_eq_add_neg, sub_eq_iff_eq_add],
    symmetry,
    rw [neg_add_eq_iff_eq_add, add_comm],
    exact h.symm },
  { convert hunit using 1,
    have : ({a, -c, -b} : finset ℤ) = {a, -b, -c},
    { refine finset.ext (λ x, ⟨λ hx, _, λ hx, _⟩);
      { simp only [mem_insert, mem_singleton] at hx,
        rcases hx with (H | H | H);
        simp [H] } },
    rw [this],
    simp only [gcd_insert, id.def, gcd_singleton, normalize_apply, neg_mul],
    congr' 1,
    rw [← coe_gcd, ← coe_gcd, int.gcd_eq_nat_abs, int.gcd_eq_nat_abs],
    simp only [nat_abs_neg, nat.cast_inj],
    rcases ⟨int.is_unit_iff.1 (norm_unit (-c)).is_unit,
      int.is_unit_iff.1 (norm_unit c).is_unit⟩ with ⟨H₁ | H₂, H₃ | H₄⟩,
    { simp [H₁, H₃] },
    { simp [H₁, H₄] },
    { simp [H₂, H₃] },
    { simp [H₂, H₄] } },
  { have hp3 : p ≠ 3 := by linarith,
    rw [← zmod.int_coe_eq_int_coe_iff] at habs H,
    rw [H] at habs,
    rw [zmod.int_coe_eq_int_coe_iff] at habs H,
    obtain ⟨n, hn⟩ := p_dvd_c_of_ab_of_anegc hpri hp3 h H habs,
    refine caseI ⟨a * b * n, _⟩,
    rw [hn],
    ring },
  { convert hprod using 1,
    ring },
  { ring_nf at ⊢ caseI,
    exact caseI }
end

end flt_regular
