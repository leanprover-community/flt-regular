import BealRegular.SeventeenCertificateArithmetic
import FltRegular.FltRegular
import FltRegular.NumberTheory.RegularPrimes
import Mathlib.NumberTheory.FLT.Basic

/-! Shared statement for independently compiled regular-prime-17 certificates. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

def SeventeenCertificate (p : ℕ) [Fact p.Prime] (hpn : p ≠ 17) : Prop :=
  ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
    P.Monic ∧
      orderOf (ZMod.unitOfCoprime p (uff Nat.prime_seventeen hpn)) = P.natDegree ∧
      P * Q + p * A = cyclotomic 17 ℤ ∧
      (p = G * Qp + Rp * cyclotomic 17 ℤ ∧
        P = G * QP + RP * cyclotomic 17 ℤ ∧ G = C1 * P + C2 * p)
