module

public import BealRegular.CubicIdealCertificate
public import FltRegular.SmallNumbers.Cyclotomic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring

/-!
# A cube-principality certificate above 2 in Q(zeta_23)

This file checks one explicit Kummer--Dedekind prime ideal.  It does not claim
that every ideal class has cube one, and therefore does not prove regularity or
FLT at exponent 23 by itself.
-/

@[expose] public section

open Ideal NumberField Polynomial RingOfIntegers
open BealRegular.CubicIdealCertificate
open scoped nonZeroDivisors

namespace BealRegular.TwentyThreePrimeTwoCube

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ

theorem prime_two : Nat.Prime 2 := by norm_num
theorem prime_twentyThree : Nat.Prime 23 := by norm_num

local instance : Fact (Nat.Prime 2) := ⟨prime_two⟩
local instance : Fact (Nat.Prime 23) := ⟨prime_twentyThree⟩
local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

/-- The 23rd cyclotomic polynomial, written coefficientwise for the kernel
certificate. -/
def Phi : ℤ[X] :=
  X ^ 22 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 +
    X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 +
    X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

/-- A monic degree-11 factor of `Phi` modulo 2. -/
def F : ℤ[X] := X ^ 11 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X + 1

/-- A generator for the cube of the prime ideal `(2, F(zeta_23))`. -/
def G : ℤ[X] :=
  X ^ 21 + X ^ 20 + X ^ 17 + X ^ 16 + X ^ 13 + X ^ 11 - X ^ 6 + X ^ 5 +
    X ^ 4 + X ^ 3 + X ^ 2 + 1

def Q0 : ℤ[X] :=
  X ^ 21 + X ^ 20 + X ^ 19 + X ^ 18 - X ^ 17 + X ^ 12 + X ^ 10 + X ^ 7 +
    X ^ 6 + X ^ 3 + X ^ 2 + 1
def Q1 : ℤ[X] :=
  2 * X ^ 21 + X ^ 20 + 2 * X ^ 19 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 +
    X ^ 14 + 2 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + X ^ 10 + 2 * X ^ 9 +
    2 * X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 +
    2 * X ^ 2 + X + 1
def Q2 : ℤ[X] :=
  X ^ 20 + X ^ 19 + 2 * X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + 2 * X ^ 14 +
    3 * X ^ 13 + 2 * X ^ 12 + X ^ 11 + 2 * X ^ 9 + X ^ 8 + 2 * X ^ 7 -
    X ^ 6 + X ^ 3 - 1
def Q3 : ℤ[X] :=
  2 * X ^ 20 + 2 * X ^ 19 + 3 * X ^ 18 - X ^ 17 - X ^ 15 + 2 * X ^ 14 -
    X ^ 12 - 4 * X ^ 11 - 2 * X ^ 10 - 2 * X ^ 9 - X ^ 8 - 3 * X ^ 7 -
    3 * X ^ 6 - 3 * X ^ 5 - X ^ 4 - X ^ 3
def R0 : ℤ[X] :=
  -X ^ 20 - X ^ 19 + X ^ 16 - X ^ 14 + X ^ 12 - 2 * X ^ 10 + 2 * X ^ 8 -
    X ^ 7 + X ^ 6 - X ^ 5 - 2 * X ^ 2 - 7 * X + 7
def R1 : ℤ[X] :=
  -2 * X ^ 20 - X ^ 19 - X ^ 16 - X ^ 15 - 2 * X ^ 12 - 3 * X ^ 10 +
    3 * X ^ 9 - 2 * X ^ 8 - X ^ 7 - X ^ 6 + 3 * X ^ 5 - 2 * X ^ 4 -
    X ^ 3 - 6 * X ^ 2 + 3
def R2 : ℤ[X] :=
  -X ^ 19 - X ^ 18 - X ^ 17 - X ^ 14 - 2 * X ^ 13 - 2 * X ^ 12 +
    2 * X ^ 10 - X ^ 9 - 2 * X ^ 8 - 2 * X ^ 7 + 3 * X ^ 6 + 3 * X ^ 5 +
    X ^ 4 - 3 * X ^ 3 - X ^ 2 + X + 3
def R3 : ℤ[X] :=
  -2 * X ^ 19 - 2 * X ^ 18 - X ^ 17 + 3 * X ^ 16 + X ^ 15 - 2 * X ^ 14 -
    3 * X ^ 13 + 2 * X ^ 12 + 5 * X ^ 11 + 3 * X ^ 10 - X ^ 9 - 2 * X ^ 8 +
    6 * X ^ 7 + 7 * X ^ 6 + 6 * X ^ 5 - X ^ 4 - X ^ 3 + 2 * X + 1
def C0 : ℤ[X] :=
  -X ^ 21 - X ^ 20 + 2 * X ^ 18 + 3 * X ^ 17 + 3 * X ^ 16 + 2 * X ^ 15 +
    4 * X ^ 14 + 5 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 5 * X ^ 10 +
    4 * X ^ 9 + 5 * X ^ 8 + 3 * X ^ 7 + 3 * X ^ 6 + 2 * X ^ 5 +
    3 * X ^ 4 - 2 * X
def C1 : ℤ[X] := X ^ 5 + X + 1
def C2 : ℤ[X] := X ^ 9 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X
def C3 : ℤ[X] := X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3
def R4 : ℤ[X] :=
  -X ^ 20 - 3 * X ^ 18 - 6 * X ^ 16 - 2 * X ^ 15 - 11 * X ^ 14 -
    2 * X ^ 13 - 15 * X ^ 12 - 21 * X ^ 10 - 4 * X ^ 9 - 20 * X ^ 8 -
    X ^ 7 - 17 * X ^ 6 - X ^ 5 - 28 * X ^ 4 + 3 * X ^ 3 - 13 * X ^ 2 +
    9 * X - 3

/-- The five exact integer-polynomial identities consumed by the generic
cubic-ideal verifier. -/
theorem polynomial_certificate :
    (C (2 : ℤ)) ^ 3 = G * Q0 + Phi * R0 ∧
      (C (2 : ℤ)) ^ 2 * F = G * Q1 + Phi * R1 ∧
      C (2 : ℤ) * F ^ 2 = G * Q2 + Phi * R2 ∧
      F ^ 3 = G * Q3 + Phi * R3 ∧
      G = C0 * (C (2 : ℤ)) ^ 3 + C1 * ((C (2 : ℤ)) ^ 2 * F) +
        C2 * (C (2 : ℤ) * F ^ 2) + C3 * F ^ 3 + Phi * R4 := by
  simp only [Phi, F, G, Q0, Q1, Q2, Q3, R0, R1, R2, R3, C0, C1, C2, C3, R4]
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The displayed coefficient polynomial really is the cyclotomic
polynomial `Phi_23`. -/
theorem Phi_eq_cyclotomic : Phi = cyclotomic 23 ℤ := by
  rw [Phi]
  simp [cyclotomic_prime, Finset.sum_range_succ]
  ring

/-- The integral primitive 23rd root used by Kummer--Dedekind. -/
def theta : 𝓞 K23 := (IsCyclotomicExtension.zeta_spec 23 ℚ K23).toInteger

theorem aeval_Phi_theta : aeval theta Phi = 0 := by
  rw [Phi_eq_cyclotomic, ← IsCyclotomicExtension.Rat.minpoly 23 K23]
  exact minpoly.aeval ℤ theta

/-- The other degree-11 factor modulo 2. -/
def Fbar : ℤ[X] := X ^ 11 + X ^ 10 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1

theorem F_dvd_cyclotomic_mod_two :
    F.map (Int.castRingHom (ZMod 2)) ∣ cyclotomic 23 (ZMod 2) := by
  refine ⟨Fbar.map (Int.castRingHom (ZMod 2)), ?_⟩
  simp [F, Fbar, cyclotomic_prime, Finset.sum_range_succ]
  ring_nf
  have h3 : (3 : (ZMod 2)[X]) = 1 := by
    change C (3 : ZMod 2) = C 1
    rw [show (3 : ZMod 2) = 1 by decide]
  have h7 : (7 : (ZMod 2)[X]) = 1 := by
    change C (7 : ZMod 2) = C 1
    rw [show (7 : ZMod 2) = 1 by decide]
  rw [h3, h7]
  simp only [mul_one]

theorem order_two_mod_twentyThree :
    orderOf (ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 23)) = 11 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Finset.Ioo 0 11 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

theorem map_F_irreducible : Irreducible (F.map (Int.castRingHom (ZMod 2))) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (n := 23)
    (by norm_num) F_dvd_cyclotomic_mod_two ?_
  have hFmonic : F.Monic := by simp only [F]; monicity!
  rw [hFmonic.natDegree_map, order_two_mod_twentyThree]
  simp only [F]
  compute_degree!

theorem map_F_mem_monicFactorsMod :
    F.map (Int.castRingHom (ZMod 2)) ∈ monicFactorsMod theta 2 := by
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic theta.isIntegral))]
  refine ⟨map_F_irreducible, ?_, ?_⟩
  · have hFmonic : F.Monic := by simp only [F]; monicity!
    exact hFmonic.map _
  · simp only [theta]
    rw [IsCyclotomicExtension.Rat.minpoly 23 K23, map_cyclotomic_int]
    exact F_dvd_cyclotomic_mod_two

/-- The Kummer--Dedekind prime above 2 selected by `F`. -/
def primeIdealTwo : primesOver (span {(2 : ℤ)}) (𝓞 K23) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (IsCyclotomicExtension.Rat.ne_dvd_exponent 2)).symm
      ⟨F.map (Int.castRingHom (ZMod 2)), map_F_mem_monicFactorsMod⟩

theorem primeIdealTwo_mem_primesOver :
    (primeIdealTwo : Ideal (𝓞 K23)) ∈ primesOver (span {(2 : ℤ)}) (𝓞 K23) :=
  primeIdealTwo.property

theorem primeIdealTwo_eq_span :
    (primeIdealTwo : Ideal (𝓞 K23)) = span {(2 : 𝓞 K23), aeval theta F} := by
  exact NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (IsCyclotomicExtension.Rat.ne_dvd_exponent 2) map_F_mem_monicFactorsMod

/-- The explicit prime above 2 has principal cube generated by `G(theta)`. -/
theorem primeIdealTwo_cube_eq_span_generator :
    (primeIdealTwo : Ideal (𝓞 K23)) ^ 3 = span {aeval theta G} := by
  rw [primeIdealTwo_eq_span]
  rcases polynomial_certificate with ⟨h0, h1, h2, h3, h4⟩
  exact
    kummerDedekindIdeal_cube_eq_span_singleton_of_polynomial_certificate
    (F := F) (G := G) (Phi := Phi) (Q0 := Q0) (Q1 := Q1) (Q2 := Q2) (Q3 := Q3)
    (R0 := R0) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4)
    (C0 := C0) (C1 := C1) (C2 := C2) (C3 := C3)
    theta 2 aeval_Phi_theta h0 h1 h2 h3 h4

/-- Principal-ideal packaging of the same checked cube equality. -/
theorem primeIdealTwo_cube_isPrincipal :
    Submodule.IsPrincipal ((primeIdealTwo : Ideal (𝓞 K23)) ^ 3) :=
  ⟨aeval theta G, primeIdealTwo_cube_eq_span_generator⟩

end

end BealRegular.TwentyThreePrimeTwoCube
