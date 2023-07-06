import FltRegular.FltThree.FltThree
import Mathlib.Algebra.GcdMonoid.Finset
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.GcdMonoid.Div
import FltRegular.NumberTheory.RegularPrimes

open Int Finset

namespace FltRegular

namespace MayAssume

theorem p_ne_three {a b c : ℤ} {n : ℕ} (hprod : a * b * c ≠ 0) (h : a ^ n + b ^ n = c ^ n) :
    n ≠ 3 := by
  intro hn
  have ha : a ≠ 0 := fun ha => by simpa [ha] using hprod
  have hb : b ≠ 0 := fun hb => by simpa [hb] using hprod
  have hc : c ≠ 0 := fun hc => by simpa [hc] using hprod
  simpa [hn, flt_three ha hb hc] using h

theorem coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    let d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 :=
  by
  have ha : a ≠ 0 := fun ha => by simpa [ha] using hprod
  have hb : b ≠ 0 := fun hb => by simpa [hb] using hprod
  have hc : c ≠ 0 := fun hc => by simpa [hc] using hprod
  let s : Finset ℤ := {a, b, c}
  set d : ℤ := s.gcd id with hddef
  have hadiv : d ∣ a := gcd_dvd (by simp)
  have hbdiv : d ∣ b := gcd_dvd (by simp)
  have hcdiv : d ∣ c := gcd_dvd (by simp)
  have hdzero : d ≠ 0 := fun hdzero => by
    simpa [ha] using Finset.gcd_eq_zero_iff.1 hdzero a (by simp)
  have hdp : d ^ n ≠ 0 := fun hdn => hdzero (pow_eq_zero hdn)
  refine' ⟨_, _, fun habs => _⟩
  · obtain ⟨na, hna⟩ := hadiv; obtain ⟨nb, hnb⟩ := hbdiv; obtain ⟨nc, hnc⟩ := hcdiv
    rw [← hddef]
    simpa [hna, hnb, hnc, mul_pow, hdzero, Int.add_mul_ediv_left (d ^ n * na ^ n) (nb ^ n),
      hdp] using congr_arg (· / d ^ n) H
  ·
    simpa [gcd_eq_gcd_image] using
      Finset.Int.gcd_div_id_eq_one (show a ∈ ({a, b, c} : Finset ℤ) by simp) ha
  · simp only [mul_eq_zero] at habs 
    rcases habs with ((Ha | Hb) | Hc)
    · exact ha (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp)) Ha)
    · exact hb (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp)) Hb)
    · exact hc (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp)) Hc)

end MayAssume

theorem p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp : p ≠ 3)
    (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p]) (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c :=
  by
  letI : Fact p.prime := ⟨hpri⟩
  replace h := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.coe_nat_pow, Int.cast_add, Int.cast_pow, ZMod.pow_card] at h 
  simp only [← ZMod.int_cast_eq_int_cast_iff, Int.cast_neg] at hbc hab 
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_sub, ← Int.cast_sub] at
    h 
  ring_nf at h 
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_bit1, Int.cast_one, Int.cast_ofNat, neg_eq_zero,
    mul_eq_zero] at h 
  rw [← ZMod.int_cast_zmod_eq_zero_iff_dvd]
  refine' Or.resolve_left h fun h3 => _
  rw [show (3 : ZMod p) = ↑(3 : ℕ) by simp, ZMod.nat_cast_zmod_eq_zero_iff_dvd,
    Nat.dvd_prime Nat.prime_three] at h3 
  cases' h3 with H₁ H₂
  · exact hpri.ne_one H₁
  · exact hp H₂

theorem a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ,
      x ^ p + y ^ p = z ^ p ∧
        ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧ ¬↑p ∣ x * y * z :=
  by
  by_cases H : a ≡ b [ZMOD p]
  swap
  · exact ⟨a, b, c, ⟨h, hgcd, H, hprod, caseI⟩⟩
  refine' ⟨a, -c, -b, ⟨_, _, fun habs => _, _, _⟩⟩
  · have hpodd : p ≠ 2 := by linarith
    simp only [neg_pow, (Or.resolve_left hpri.eq_two_or_odd' hpodd).neg_one_pow, neg_one_mul, ←
      sub_eq_add_neg, sub_eq_iff_eq_add]
    symm
    rw [neg_add_eq_iff_eq_add, add_comm]
    exact h.symm
  · convert hgcd using 1
    have : ({a, -c, -b} : Finset ℤ) = {a, -b, -c} := by
      refine' Finset.ext fun x => ⟨fun hx => _, fun hx => _⟩ <;>
        · simp only [mem_insert, mem_singleton] at hx 
          rcases hx with (H | H | H) <;> simp [H]
    rw [this]
    simp only [gcd_insert, id.def, gcd_singleton, normalize_apply, neg_mul]
    congr 1
    rw [← coe_gcd, ← coe_gcd, Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
    simp only [nat_abs_neg, Nat.cast_inj]
    rcases Int.isUnit_iff.1 (norm_unit (-c)).IsUnit, Int.isUnit_iff.1 (norm_unit c).IsUnit with
      ⟨H₁ | H₂, H₃ | H₄⟩
    · simp [H₁, H₃]
    · simp [H₁, H₄]
    · simp [H₂, H₃]
    · simp [H₂, H₄]
  · have hp3 : p ≠ 3 := by linarith
    rw [← ZMod.int_cast_eq_int_cast_iff] at habs H 
    rw [H] at habs 
    rw [ZMod.int_cast_eq_int_cast_iff] at habs H 
    obtain ⟨n, hn⟩ := p_dvd_c_of_ab_of_anegc hpri hp3 h H habs
    refine' caseI ⟨a * b * n, _⟩
    rw [hn]
    ring
  · convert hprod using 1
    ring
  · ring_nf at caseI ⊢
    exact caseI

end FltRegular

