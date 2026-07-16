module

public import FltRegular.SmallNumbers.Cyclotomic
public import FltRegular.SmallNumbers.OrderOf
public import Mathlib.Tactic.NormNum.Prime

/-! Minimal arithmetic shared by the independently compiled p = 19 certificates. -/

@[expose] public section

namespace NineteenCertificateArithmetic

open Nat Polynomial cyclotomic Finset

theorem prime_nineteen : Nat.Prime 19 := by
  norm_num

theorem cyclotomic_19 : cyclotomic 19 ℤ =
    X^18 + X^17 + X^16 + X^15 + X^14 + X^13 + X^12 + X^11 + X^10 + X^9 + X^8 +
      X^7 + X^6 + X^5 + X^4 + X^3 + X^2 + X + 1 := by
  letI : Fact (Nat.Prime 19) := ⟨prime_nineteen⟩
  simp [cyclotomic_prime, sum_range_succ]
  ring

theorem orderOf_unitOfCoprime_eq_one_of_eq_mul_add_one {p : ℕ} [Fact p.Prime]
    (hpn : p ≠ 19) (k : ℕ) (hpform : p = 19 * k + 1) :
    orderOf (ZMod.unitOfCoprime p (uff prime_nineteen hpn)) = 1 := by
  rw [orderOf_eq_one_iff]
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, Units.val_one]
  rw [hpform]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]

theorem orderOf_unitOfCoprime_eq_one_of_mod_eq_one {p : ℕ} [Fact p.Prime]
    (hpn : p ≠ 19) (hmod : p % 19 = 1) :
    orderOf (ZMod.unitOfCoprime p (uff prime_nineteen hpn)) = 1 := by
  rw [orderOf_eq_one_iff]
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, Units.val_one]
  exact (ZMod.natCast_eq_natCast_iff' p 1 19).2 (by simpa using hmod)

end NineteenCertificateArithmetic
