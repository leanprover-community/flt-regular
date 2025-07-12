import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

open Int Finset

namespace FltRegular

namespace MayAssume

theorem coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    let d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 := by
  have ha : a ≠ 0 := fun ha => by simp [ha] at hprod
  have hb : b ≠ 0 := fun hb => by simp [hb] at hprod
  have hc : c ≠ 0 := fun hc => by simp [hc] at hprod
  let s : Finset ℤ := {a, b, c}
  set d : ℤ := s.gcd id
  have hadiv : d ∣ a := gcd_dvd (by simp [s])
  have hbdiv : d ∣ b := gcd_dvd (by simp [s])
  have hcdiv : d ∣ c := gcd_dvd (by simp [s])
  have hdzero : d ≠ 0 := fun hdzero => by
    simpa [ha] using Finset.gcd_eq_zero_iff.1 hdzero a (by simp [s])
  have hdp : d ^ n ≠ 0 := fun hdn => hdzero (pow_eq_zero hdn)
  refine ⟨?_, ?_, fun habs => ?_⟩
  · obtain ⟨na, hna⟩ := hadiv; obtain ⟨nb, hnb⟩ := hbdiv; obtain ⟨nc, hnc⟩ := hcdiv
    rwa [← mul_left_inj' hdp, add_mul, ← mul_pow, ← mul_pow, ← mul_pow, hna, hnb, hnc,
      Int.mul_ediv_cancel_left _ hdzero, Int.mul_ediv_cancel_left _ hdzero,
      Int.mul_ediv_cancel_left _ hdzero, mul_comm, ← hna, mul_comm, ← hnb, mul_comm, ← hnc]
  · simpa [gcd_eq_gcd_image, d] using
      Finset.gcd_div_id_eq_one (show a ∈ ({a, b, c} : Finset ℤ) by simp) ha
  · simp only [mul_eq_zero] at habs
    rcases habs with ((Ha | Hb) | Hc)
    · exact ha (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp [s])) Ha)
    · exact hb (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp [s])) Hb)
    · exact hc (Int.eq_zero_of_ediv_eq_zero (gcd_dvd (by simp [s])) Hc)

end MayAssume

theorem p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp : p ≠ 3)
    (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p]) (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  letI : Fact p.Prime := ⟨hpri⟩
  replace h := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_neg] at hbc hab
  rw [hab, hbc, ← sub_eq_zero, ← sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_sub,
    ← Int.cast_sub] at h
  ring_nf at h
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, neg_eq_zero, mul_eq_zero] at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine Or.resolve_right h fun h3 => ?_
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_zero_iff,
    Nat.dvd_prime Nat.prime_three] at h3
  rcases h3 with H₁ | H₂
  · exact hpri.ne_one H₁
  · exact hp H₂

theorem a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p) (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧ ¬↑p ∣ x * y * z := by
  by_cases H : a ≡ b [ZMOD p]
  swap
  · exact ⟨a, b, c, ⟨h, hgcd, H, hprod, caseI⟩⟩
  refine ⟨a, -c, -b, ⟨?_, ?_, fun habs => ?_, ?_, ?_⟩⟩
  · have hpodd : p ≠ 2 := by linarith
    rw [neg_pow, (Or.resolve_left hpri.eq_two_or_odd' hpodd).neg_one_pow, neg_pow,
      (Or.resolve_left hpri.eq_two_or_odd' hpodd).neg_one_pow]
    simp only [← sub_eq_add_neg, sub_eq_iff_eq_add, neg_mul, one_mul]
    symm
    rw [neg_add_eq_iff_eq_add, add_comm]
    exact h.symm
  · convert hgcd using 1
    have : ({a, -c, -b} : Finset ℤ) = {a, -b, -c} := by
      refine Finset.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩ <;>
        · simp only [mem_insert, mem_singleton] at hx
          rcases hx with (H | H | H) <;> simp [H]
    rw [this]
    simp only [gcd_insert, id, gcd_singleton, normalize_apply, neg_mul]
    congr 1
    rw [← coe_gcd, ← coe_gcd, Int.gcd_eq_natAbs, Int.gcd_eq_natAbs]
    simp only [natAbs_neg, Nat.cast_inj]
    rcases Int.isUnit_iff.1 (normUnit (-c)).isUnit, Int.isUnit_iff.1 (normUnit c).isUnit with
      ⟨H₁ | H₂, H₃ | H₄⟩
    · simp [H₁, H₃]
    · simp [H₁, H₄]
    · simp [H₂, H₃]
    · simp [H₂, H₄]
  · have hp3 : p ≠ 3 := by linarith
    rw [← ZMod.intCast_eq_intCast_iff] at habs H
    rw [H] at habs
    rw [ZMod.intCast_eq_intCast_iff] at habs H
    obtain ⟨n, hn⟩ := p_dvd_c_of_ab_of_anegc hpri hp3 h H habs
    refine caseI ⟨a * b * n, ?_⟩
    rw [hn]
    ring
  · convert hprod using 1
    ring
  · ring_nf at caseI ⊢
    exact caseI

end FltRegular
