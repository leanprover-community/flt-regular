module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import FltRegular.NumberTheory.Cyclotomic.Rat

/-!
# Regular primes

## Main definitions

* `IsRegularNumber`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/

@[expose] public section

noncomputable section

open Nat Polynomial NumberField

open scoped NumberField

variable (n p : ℕ)

/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group. -/
def IsRegularNumber : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField n ℚ)

/-- The definition of regular primes. -/
def IsRegularPrime : Prop :=
  IsRegularNumber p

/-- If the ring of integers of the `p`-th cyclotomic field is a principal ideal ring, then `p` is
a regular prime. -/
theorem isRegularPrime_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 (CyclotomicField p ℚ))] :
    IsRegularPrime p := by
  rw [IsRegularPrime, IsRegularNumber, card_classGroup_eq_one_iff.2 ‹_›]
  exact coprime_one_right _

section TwoRegular

variable (K : Type*) [Field K]

variable (L : Type*) [Field L] [Algebra K L]

/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K := by
  suffices IsSplittingField K K (cyclotomic 2 K) by
    have : IsSplittingField K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact (IsSplittingField.algEquiv L (cyclotomic 2 K)).trans
      (IsSplittingField.algEquiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using Splits.X_sub_C (-1 : K),
    by simp [eq_iff_true_of_subsingleton]⟩

instance IsPrincipalIdealRing_of_IsCyclotomicExtension_two
    (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) :=
  let F : 𝓞 L ≃+* ℤ := (RingOfIntegers.mapRingEquiv
    (cyclotomicFieldTwoEquiv ℚ L).toRingEquiv).trans Rat.ringOfIntegersEquiv
  IsPrincipalIdealRing.of_surjective F.symm.toRingHom F.symm.surjective

theorem isRegularPrime_two : IsRegularPrime 2 := isRegularPrime_of_isPrincipalIdealRing 2

theorem isRegularPrime_three : IsRegularPrime 3 :=
  have := IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  isRegularPrime_of_isPrincipalIdealRing 3

end TwoRegular
