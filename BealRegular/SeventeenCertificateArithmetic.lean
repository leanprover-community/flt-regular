import BealRegular.SeventeenBounds

/-! Symbolic arithmetic shared by the independently compiled p = 17 certificates. -/

namespace SeventeenCertificateArithmetic

theorem orderOf_unitOfCoprime_eq_one_of_mod_eq_one {p : ℕ} [Fact p.Prime]
    (hpn : p ≠ 17) (hmod : p % 17 = 1) :
    orderOf (ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)) = 1 := by
  rw [orderOf_eq_one_iff]
  apply Units.ext
  simp only [ZMod.coe_unitOfCoprime, Units.val_one]
  exact (ZMod.natCast_eq_natCast_iff' p 1 17).2 (by simpa using hmod)

end SeventeenCertificateArithmetic
