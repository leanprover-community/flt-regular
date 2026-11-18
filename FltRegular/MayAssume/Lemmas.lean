module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Int Finset

namespace FltRegular

namespace MayAssume

theorem coprime {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    letI d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 := by
  have ha : a ≠ 0 := by grind
  set d : ℤ := ({a, b, c} : Finset ℤ).gcd id
  have hadiv : d ∣ a := gcd_dvd (by simp)
  have hbdiv : d ∣ b := gcd_dvd (by simp)
  have hcdiv : d ∣ c := gcd_dvd (by simp)
  have hdzero : d ≠ 0 := fun hd ↦ ha (Finset.gcd_eq_zero_iff.1 hd a (by simp))
  refine ⟨?_, ?_, by grind [Int.ediv_mul_cancel hadiv, Int.ediv_mul_cancel hbdiv,
    Int.ediv_mul_cancel hcdiv]⟩
  · rwa [← mul_left_inj' (pow_ne_zero n hdzero), add_mul, ← mul_pow, ← mul_pow, ← mul_pow,
      Int.ediv_mul_cancel hadiv, Int.ediv_mul_cancel hbdiv, Int.ediv_mul_cancel hcdiv]
  · simpa [gcd_eq_gcd_image, d] using
      Finset.gcd_div_id_eq_one (show a ∈ ({a, b, c} : Finset ℤ) by simp) ha

end MayAssume

theorem p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  have : Fact p.Prime := ⟨hpri⟩
  replace h := congr_arg (Int.cast (R := ZMod p)) h
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_add, Int.cast_pow, ZMod.pow_card,
    Int.cast_neg] at h hab hbc
  have h3c : (3 : ℕ) * (c : ZMod p) = 0 := by grind
  rcases mul_eq_zero.mp h3c with h3 | hc
  · exact absurd ((Nat.dvd_prime Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff 3 p).mp h3))
      (by grind [hpri.ne_one])
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc

theorem a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧
        ¬↑p ∣ x * y * z := by
  if hab : a ≡ b [ZMOD p] then
    refine ⟨a, -c, -b, ?_, ?_, fun habs ↦ caseI
      ((p_dvd_c_of_ab_of_anegc hpri (by lia) h hab (hab.symm.trans habs)).mul_left _),
      by grind, by grind⟩
    · have hodd : Odd p := hpri.odd_of_ne_two (by lia)
      rw [hodd.neg_pow, hodd.neg_pow]
      lia
    · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
        ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm]
  else
    exact ⟨a, b, c, h, hgcd, hab, hprod, caseI⟩

end FltRegular
