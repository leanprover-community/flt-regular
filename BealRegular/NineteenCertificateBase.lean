module

public import BealRegular.NineteenCertificateArithmetic
import FltRegular.FltRegular
public import FltRegular.NumberTheory.RegularPrimes
public import Mathlib.NumberTheory.FLT.Basic

/-! Shared statement for independently compiled regular-prime-19 certificates. -/

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

def NineteenCertificate (p : ℕ) [Fact p.Prime] (hpn : p ≠ 19) : Prop :=
  ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
    P.Monic ∧
      orderOf (ZMod.unitOfCoprime p (uff NineteenCertificateArithmetic.prime_nineteen hpn)) =
        P.natDegree ∧
      P * Q + p * A = cyclotomic 19 ℤ ∧
      (p = G * Qp + Rp * cyclotomic 19 ℤ ∧
        P = G * QP + RP * cyclotomic 19 ℤ ∧ G = C1 * P + C2 * p)
