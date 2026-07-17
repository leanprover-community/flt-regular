module

public import BealRegular.TwentyThreePrimeTwoCube

/-!
# A cube-principality certificate above 3 in Q(zeta_23)

This file checks one explicit Kummer--Dedekind prime ideal above `3`.  Since
the cyclotomic field is Galois, the generic one-prime-above theorem can
transport this cube-principality statement to the other prime above `3`.
This is still only the `q = 3` branch of that theorem and does not prove that
the whole class group has exponent three.
-/

@[expose] public section

open Ideal NumberField Polynomial RingOfIntegers
open BealRegular.CubicIdealCertificate
open scoped nonZeroDivisors

namespace BealRegular.TwentyThreePrimeThreeCube

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "Phi23" => BealRegular.TwentyThreePrimeTwoCube.Phi
local notation "theta" => BealRegular.TwentyThreePrimeTwoCube.theta

theorem prime_three : Nat.Prime 3 := by norm_num

local instance : Fact (Nat.Prime 3) := ⟨prime_three⟩
local instance : Fact (Nat.Prime 23) :=
  ⟨BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree⟩
local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

/-- A monic degree-11 factor of `Phi_23` modulo 3. -/
def F : ℤ[X] :=
  X ^ 11 - X ^ 8 - X ^ 6 + X ^ 4 + X ^ 3 - X ^ 2 - X - 1

/-- A generator for the cube of the prime ideal `(3, F(zeta_23))`. -/
def G : ℤ[X] :=
  -2 * X ^ 21 - 2 * X ^ 20 - 2 * X ^ 17 - 2 * X ^ 16 - 2 * X ^ 13 -
    2 * X ^ 11 + X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 2

def Q0 : ℤ[X] :=
  -2 * X ^ 21 - 2 * X ^ 20 - 2 * X ^ 19 - 2 * X ^ 18 + X ^ 17 -
    2 * X ^ 12 - 2 * X ^ 10 - 2 * X ^ 7 - 2 * X ^ 6 - 2 * X ^ 3 - 2 * X ^ 2 - 2
def Q1 : ℤ[X] :=
  X ^ 21 + 3 * X ^ 20 + X ^ 19 + X ^ 18 - X ^ 17 + 2 * X ^ 12 +
    2 * X ^ 8 + X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 - 1
def Q2 : ℤ[X] :=
  -X ^ 21 - 2 * X ^ 20 + X ^ 19 + X ^ 17 + X ^ 16 + 2 * X ^ 15 -
    X ^ 10 + 2 * X ^ 8 + 2 * X ^ 7 + X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 -
    2 * X ^ 3 + X ^ 2 + 2 * X + 3
def Q3 : ℤ[X] :=
  -X ^ 21 - 2 * X ^ 17 - 3 * X ^ 16 - 3 * X ^ 15 - 3 * X ^ 14 - X ^ 13 +
    X ^ 12 + 3 * X ^ 11 - 3 * X ^ 9 - 6 * X ^ 8 - 3 * X ^ 7 - X ^ 6 +
    3 * X ^ 5 + 2 * X ^ 4 + X ^ 3 - 4 * X ^ 2 - 4 * X - 3
def R0 : ℤ[X] :=
  -4 * X ^ 20 - 4 * X ^ 19 + 2 * X ^ 16 - 2 * X ^ 14 + 2 * X ^ 12 -
    6 * X ^ 10 + 6 * X ^ 8 - 2 * X ^ 7 + 2 * X ^ 6 - 4 * X ^ 5 -
    8 * X ^ 2 - 23 * X + 23
def R1 : ℤ[X] :=
  2 * X ^ 20 + 6 * X ^ 19 - 4 * X ^ 17 - 2 * X ^ 16 + 4 * X ^ 15 +
    2 * X ^ 14 - 4 * X ^ 13 - 2 * X ^ 12 + 6 * X ^ 11 - 8 * X ^ 8 +
    10 * X ^ 7 - 4 * X ^ 6 - 7 * X ^ 5 + 2 * X ^ 4 + 20 * X ^ 3 + 2 * X - 11
def R2 : ℤ[X] :=
  -2 * X ^ 20 - 4 * X ^ 19 + 4 * X ^ 18 + 4 * X ^ 17 - 2 * X ^ 16 -
    2 * X ^ 15 + 6 * X ^ 14 + 2 * X ^ 13 - 6 * X ^ 12 + 6 * X ^ 10 -
    8 * X ^ 9 + 4 * X ^ 8 + 4 * X ^ 7 + 8 * X ^ 6 - 7 * X ^ 5 -
    7 * X ^ 4 - 11 * X ^ 3 + 7 * X ^ 2 + X + 9
def R3 : ℤ[X] :=
  -2 * X ^ 20 + 2 * X ^ 18 - 6 * X ^ 16 - 6 * X ^ 15 - 2 * X ^ 12 +
    5 * X ^ 11 + 3 * X ^ 10 - 15 * X ^ 8 - 3 * X ^ 7 + X ^ 6 +
    13 * X ^ 5 + X ^ 4 + 4 * X ^ 3 - 9 * X ^ 2 - 4 * X - 7
def C0 : ℤ[X] :=
  -2 * X ^ 21 - 4 * X ^ 20 - 3 * X ^ 19 - 2 * X ^ 18 + X ^ 17 +
    3 * X ^ 16 + 2 * X ^ 15 - 2 * X ^ 14 - 4 * X ^ 13 - 3 * X ^ 12 -
    2 * X ^ 11 + 2 * X ^ 10 + 4 * X ^ 9 + 3 * X ^ 8 - X ^ 7 - X ^ 6 -
    2 * X ^ 5 - X ^ 4 - X ^ 3 + X ^ 2 + X + 2
def C1 : ℤ[X] :=
  2 * X ^ 10 + 2 * X ^ 9 + X ^ 8 + 2 * X ^ 7 + X ^ 6 + 2 * X ^ 4 +
    2 * X ^ 3 + X ^ 2 + X + 2
def C2 : ℤ[X] :=
  2 * X ^ 10 + X ^ 9 + X ^ 6 + X ^ 5 + 2 * X ^ 4 + X ^ 3 + 1
def C3 : ℤ[X] :=
  2 * X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    X ^ 2 + X + 2
def R4 : ℤ[X] :=
  -2 * X ^ 20 + X ^ 19 + 6 * X ^ 17 - 3 * X ^ 16 + 6 * X ^ 15 -
    10 * X ^ 14 - 2 * X ^ 13 - 15 * X ^ 12 + 19 * X ^ 11 + X ^ 10 +
    24 * X ^ 9 - 12 * X ^ 8 + 6 * X ^ 7 - 48 * X ^ 6 - 8 * X ^ 4 +
    45 * X ^ 3 + 13 * X ^ 2 + 40 * X - 39

/-- The five exact integer-polynomial identities consumed by the generic
cubic-ideal verifier. -/
theorem polynomial_certificate :
    (C (3 : ℤ)) ^ 3 = G * Q0 + Phi23 * R0 ∧
      (C (3 : ℤ)) ^ 2 * F = G * Q1 + Phi23 * R1 ∧
      C (3 : ℤ) * F ^ 2 = G * Q2 + Phi23 * R2 ∧
      F ^ 3 = G * Q3 + Phi23 * R3 ∧
      G = C0 * (C (3 : ℤ)) ^ 3 + C1 * ((C (3 : ℤ)) ^ 2 * F) +
        C2 * (C (3 : ℤ) * F ^ 2) + C3 * F ^ 3 + Phi23 * R4 := by
  simp only [BealRegular.TwentyThreePrimeTwoCube.Phi, F, G, Q0, Q1, Q2, Q3,
    R0, R1, R2, R3, C0, C1, C2, C3, R4]
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The other degree-11 factor modulo 3. -/
def Fbar : ℤ[X] :=
  X ^ 11 + X ^ 10 + X ^ 9 - X ^ 8 - X ^ 7 + X ^ 5 + X ^ 3 - 1

/-- Integral correction term in the factorization of `Phi_23` modulo 3. -/
def A : ℤ[X] :=
  X ^ 19 + X ^ 18 + X ^ 17 - X ^ 14 + X ^ 12 + 3 * X ^ 11 +
    X ^ 10 - X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3

/-- An exact integral identity whose reduction modulo 3 proves that `F`
divides `Phi_23`. -/
theorem F_mul_Fbar_add_three_mul_A :
    F * Fbar + C (3 : ℤ) * A = Phi23 := by
  simp only [F, Fbar, A, BealRegular.TwentyThreePrimeTwoCube.Phi]
  norm_num
  ring

theorem F_dvd_cyclotomic_mod_three :
    F.map (Int.castRingHom (ZMod 3)) ∣ cyclotomic 23 (ZMod 3) := by
  refine ⟨Fbar.map (Int.castRingHom (ZMod 3)), ?_⟩
  have hmap := congrArg (Polynomial.map (Int.castRingHom (ZMod 3)))
    F_mul_Fbar_add_three_mul_A
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C] at hmap
  have hthree : Int.castRingHom (ZMod 3) (3 : ℤ) = 0 := by decide
  rw [hthree, C_0, zero_mul, add_zero,
    BealRegular.TwentyThreePrimeTwoCube.Phi_eq_cyclotomic,
    map_cyclotomic_int] at hmap
  exact hmap.symm

theorem order_three_mod_twentyThree :
    orderOf (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 23)) = 11 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have hn : n ∈ Finset.Ioo 0 11 := by simp [hnpos, hnlt]
  fin_cases hn <;> decide

theorem map_F_irreducible : Irreducible (F.map (Int.castRingHom (ZMod 3))) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (n := 23)
    (by norm_num) F_dvd_cyclotomic_mod_three ?_
  have hFmonic : F.Monic := by simp only [F]; monicity!
  rw [hFmonic.natDegree_map, order_three_mod_twentyThree]
  simp only [F]
  compute_degree!

theorem map_F_mem_monicFactorsMod :
    F.map (Int.castRingHom (ZMod 3)) ∈ monicFactorsMod theta 3 := by
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic
      BealRegular.TwentyThreePrimeTwoCube.theta.isIntegral))]
  refine ⟨map_F_irreducible, ?_, ?_⟩
  · have hFmonic : F.Monic := by simp only [F]; monicity!
    exact hFmonic.map _
  · simp only [BealRegular.TwentyThreePrimeTwoCube.theta]
    rw [IsCyclotomicExtension.Rat.minpoly 23 K23, map_cyclotomic_int]
    exact F_dvd_cyclotomic_mod_three

/-- The Kummer--Dedekind prime above 3 selected by `F`. -/
def primeIdealThree : primesOver (span {(3 : ℤ)}) (𝓞 K23) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (IsCyclotomicExtension.Rat.ne_dvd_exponent 3)).symm
      ⟨F.map (Int.castRingHom (ZMod 3)), map_F_mem_monicFactorsMod⟩

theorem primeIdealThree_mem_primesOver :
    (primeIdealThree : Ideal (𝓞 K23)) ∈ primesOver (span {(3 : ℤ)}) (𝓞 K23) :=
  primeIdealThree.property

theorem primeIdealThree_eq_span :
    (primeIdealThree : Ideal (𝓞 K23)) = span {(3 : 𝓞 K23), aeval theta F} := by
  exact NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (IsCyclotomicExtension.Rat.ne_dvd_exponent 3) map_F_mem_monicFactorsMod

/-- The selected prime has residue degree 11. -/
theorem primeIdealThree_inertiaDeg :
    (primeIdealThree : Ideal (𝓞 K23)).inertiaDeg ℤ = 11 := by
  unfold primeIdealThree
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply
    (IsCyclotomicExtension.Rat.ne_dvd_exponent 3) map_F_mem_monicFactorsMod]
  have hFmonic : F.Monic := by simp only [F]; monicity!
  rw [hFmonic.natDegree_map]
  simp only [F]
  compute_degree!

/-- The explicit prime above 3 has principal cube generated by `G(theta)`. -/
theorem primeIdealThree_cube_eq_span_generator :
    (primeIdealThree : Ideal (𝓞 K23)) ^ 3 = span {aeval theta G} := by
  rw [primeIdealThree_eq_span]
  rcases polynomial_certificate with ⟨h0, h1, h2, h3, h4⟩
  exact
    kummerDedekindIdeal_cube_eq_span_singleton_of_polynomial_certificate
    (F := F) (G := G) (Phi := Phi23) (Q0 := Q0) (Q1 := Q1) (Q2 := Q2) (Q3 := Q3)
    (R0 := R0) (R1 := R1) (R2 := R2) (R3 := R3) (R4 := R4)
    (C0 := C0) (C1 := C1) (C2 := C2) (C3 := C3)
    theta 3 BealRegular.TwentyThreePrimeTwoCube.aeval_Phi_theta h0 h1 h2 h3 h4

/-- Principal-ideal packaging of the checked cube equality. -/
theorem primeIdealThree_cube_isPrincipal :
    Submodule.IsPrincipal ((primeIdealThree : Ideal (𝓞 K23)) ^ 3) :=
  ⟨aeval theta G, primeIdealThree_cube_eq_span_generator⟩

/-- The exact existential shape consumed by the `q = 3` branch of the
one-prime-above Minkowski theorem. -/
theorem exists_prime_above_three_cube_isPrincipal :
    ∃ P ∈ primesOver (span {(3 : ℤ)}) (𝓞 K23),
      Submodule.IsPrincipal (P ^ 3) :=
  ⟨primeIdealThree, primeIdealThree.property, primeIdealThree_cube_isPrincipal⟩

end

end BealRegular.TwentyThreePrimeThreeCube
