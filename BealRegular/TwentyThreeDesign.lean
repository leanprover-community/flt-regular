import BealRegular.ClassGroupExponentMinkowski
import FltRegular.FltRegular
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum.Prime

/-!
# Design boundary for the regular prime 23

This file contains only group-theoretic consequences of possible class-group
certificates.  It deliberately does **not** assert a computation of the class
group of `ℚ(ζ_23)`.

The useful certificate is weaker than a PID instance: it is enough to show
that every ideal class has cube one.  Cauchy's theorem then rules out a factor
of `23` in the class number.
-/

@[expose] public section

open Ideal NumberField Module NumberField.InfinitePlace Nat Real
open scoped NumberField nonZeroDivisors

namespace BealRegular.TwentyThreeDesign

open BealRegular.ClassGroupExponentMinkowski

private theorem prime_twentyThree : Nat.Prime 23 := by
  norm_num

local instance : Fact (Nat.Prime 23) := ⟨prime_twentyThree⟩

local notation "K23" => CyclotomicField 23 ℚ
local notation "M23" => (4 / π) ^ nrComplexPlaces K23 *
  ((finrank ℚ K23)! / (finrank ℚ K23) ^ (finrank ℚ K23) * √|discr K23|)

local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

local instance : IsGalois ℚ K23 :=
  IsCyclotomicExtension.isGalois {23} ℚ K23

/-- If a finite group has exponent dividing `n`, every prime coprime to `n`
is coprime to the cardinality of the group.  The proof uses Cauchy's theorem,
so it does not require the group to be commutative. -/
theorem prime_coprime_card_of_forall_pow_eq_one
    {G : Type*} [Group G] [Fintype G] {p n : ℕ} [hp : Fact p.Prime]
    (hpn : p.Coprime n) (hpow : ∀ g : G, g ^ n = 1) :
    p.Coprime (Fintype.card G) := by
  rw [hp.out.coprime_iff_not_dvd]
  intro hdiv
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hdiv
  have horder : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one (hpow g)
  rw [hg] at horder
  exact (hp.out.coprime_iff_not_dvd.mp hpn) horder

/-- Kernel-facing endpoint for a future exponent-three certificate for the
class group of `ℚ(ζ_23)`. -/
theorem isRegularPrime_twentyThree_of_cube
    (hCube : ∀ c : ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ)),
      c ^ 3 = 1) : IsRegularPrime 23 := by
  rw [IsRegularPrime, IsRegularNumber]
  exact prime_coprime_card_of_forall_pow_eq_one (by norm_num) hCube

/-- An exponent-divisibility certificate is interchangeable with the
pointwise cube certificate used by `isRegularPrime_twentyThree_of_cube`. -/
theorem isRegularPrime_twentyThree_of_exponent_dvd_three
    (hExponent : Monoid.exponent
      (ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ))) ∣ 3) :
    IsRegularPrime 23 := by
  apply isRegularPrime_twentyThree_of_cube
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExponent

/-- Exact class number three is a stronger certificate, and therefore also
suffices.  This theorem does not claim that the class number is three. -/
theorem isRegularPrime_twentyThree_of_card_eq_three
    (hCard : Fintype.card
      (ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ))) = 3) :
    IsRegularPrime 23 := by
  apply isRegularPrime_twentyThree_of_cube
  intro c
  rw [← hCard]
  exact pow_card_eq_one

/-! ## Kernel-checked Minkowski bridges -/

/-- It is enough to prove cube-principality for every prime ideal under the
Minkowski bound.  Unlike a PID criterion, this remains applicable when the
class group itself is nontrivial. -/
theorem isRegularPrime_twentyThree_of_minkowski_prime_cubes
    (h : ∀ {P : (Ideal (NumberField.RingOfIntegers K23))⁰},
      (P : Ideal (NumberField.RingOfIntegers K23)).IsPrime →
      absNorm (P : Ideal (NumberField.RingOfIntegers K23)) ≤ M23 →
        Submodule.IsPrincipal
          ((P : Ideal (NumberField.RingOfIntegers K23)) ^ 3)) :
    IsRegularPrime 23 := by
  apply isRegularPrime_twentyThree_of_cube
  exact classGroup_pow_eq_one_of_isPrincipal_pow_of_norm_le_of_isPrime
    (K := K23) 3 h

/-- In the Galois cyclotomic field, one cube-principality certificate above
each relevant rational prime suffices; conjugacy transports it to all primes
above the same rational prime. -/
theorem isRegularPrime_twentyThree_of_one_prime_above_cubes
    (h : ∀ p ∈ Finset.Icc 1 ⌊M23⌋₊, p.Prime →
      ∃ P ∈ primesOver (span {(p : ℤ)}) (NumberField.RingOfIntegers K23),
        ⌊M23⌋₊ < p ^ P.inertiaDeg ℤ ∨
          Submodule.IsPrincipal (P ^ 3)) :
    IsRegularPrime 23 := by
  apply isRegularPrime_twentyThree_of_cube
  exact classGroup_pow_eq_one_of_one_prime_above (K := K23) 3 h

/-- Any explicit cube certificate reaching the endpoint above also yields the
regular-prime FLT theorem at exponent `23`. -/
theorem fermatLastTheoremTwentyThree_of_cube
    (hCube : ∀ c : ClassGroup (NumberField.RingOfIntegers K23), c ^ 3 = 1) :
    FermatLastTheoremFor 23 :=
  @flt_regular 23 ⟨prime_twentyThree⟩
    (isRegularPrime_twentyThree_of_cube hCube) (by norm_num)

end BealRegular.TwentyThreeDesign
