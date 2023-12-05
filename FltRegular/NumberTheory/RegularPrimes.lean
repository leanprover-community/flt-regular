import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import FltRegular.NumberTheory.Cyclotomic.CyclRat
import Mathlib.NumberTheory.Cyclotomic.Rat

/-!
# Regular primes

## Main definitions

* `is_regular_number`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/


noncomputable section

open Nat Polynomial

open NumberField

open scoped Classical NumberField

section SafeInstances

/- The idea of `open_locale cyclotomic` is that it provides some of these instances when needed,
but sadly its implementation is so unsafe that using it here creates a lot of diamonds.
We instead put some safe specialised instances here, and we can maybe look at generalising them
later, when this is needed. Most results from here on genuinely only work for ℚ, so this is
very fine for the moment. -/
instance safe {p : ℕ+} : NumberField (CyclotomicField p ℚ) :=
  IsCyclotomicExtension.numberField {p} ℚ <| CyclotomicField p ℚ

instance safe' {p : ℕ+} : FiniteDimensional ℚ (CyclotomicField p ℚ) :=
  IsCyclotomicExtension.finiteDimensional {p} ℚ <| CyclotomicField p ℚ

instance CyclotomicField.classGroupFinite {p : ℕ+} :
    Fintype (ClassGroup <| 𝓞 (CyclotomicField p ℚ)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ (CyclotomicField p ℚ) AbsoluteValue.absIsAdmissible

end SafeInstances

variable (n p : ℕ) [Fact p.Prime]

instance {p : ℕ} [hp : Fact p.Prime] : Fact (0 < p) :=
  ⟨hp.out.pos⟩

/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group -/
def IsRegularNumber [hn : Fact (0 < n)] : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField ⟨n, hn.out⟩ ℚ)

/-- The definition of regular primes. -/
def IsRegularPrime : Prop :=
  IsRegularNumber p

/-- A prime number is Bernoulli regular if it does not divide the numerator of any of
the first `p - 3` (non-zero) Bernoulli numbers-/
def IsBernoulliRegular : Prop :=
  ∀ i ∈ Finset.range ((p - 3) / 2), ((bernoulli 2 * i).num : ZMod p) ≠ 0

/-- A prime is super regular if its regular and Bernoulli regular.-/
def IsSuperRegular : Prop :=
  IsRegularNumber p ∧ IsBernoulliRegular p

section TwoRegular

variable (A K : Type _) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

variable (L : Type _) [Field L] [Algebra K L]

/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K := by
  suffices IsSplittingField K K (cyclotomic 2 K) by
    letI : IsSplittingField K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact
      (IsSplittingField.algEquiv L (cyclotomic 2 K)).trans
        (IsSplittingField.algEquiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using @splits_X_sub_C _ _ _ _ (RingHom.id K) (-1),
    by simp [eq_iff_true_of_subsingleton]⟩


instance IsPrincipalIdealRing_of_IsCyclotomicExtension_two
  (L : Type _) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) := by
  haveI : IsIntegralClosure ℤ ℤ L :=
    { algebraMap_injective' := (algebraMap ℤ L).injective_int
      isIntegral_iff := fun {x} => by
        let f := cyclotomicFieldTwoEquiv ℚ L
        refine'
          ⟨fun hx => ⟨IsIntegralClosure.mk' ℤ (f x) (map_isIntegral_int f hx), f.injective _⟩, _⟩
        · convert IsIntegralClosure.algebraMap_mk' ℤ (f x) (map_isIntegral_int f hx)
          simp
        · rintro ⟨y, hy⟩
          simpa [← hy] using isIntegral_algebraMap }
  let F : 𝓞 L ≃+* ℤ := NumberField.RingOfIntegers.equiv _
  exact IsPrincipalIdealRing.of_surjective F.symm.toRingHom F.symm.surjective

instance : IsCyclotomicExtension {2} ℚ (CyclotomicField (⟨2, two_pos⟩ : ℕ+) ℚ) :=
CyclotomicField.isCyclotomicExtension 2 ℚ

instance : IsPrincipalIdealRing (𝓞 (CyclotomicField (⟨2, two_pos⟩ : ℕ+) ℚ)) :=
IsPrincipalIdealRing_of_IsCyclotomicExtension_two _

theorem isRegularNumber_two : IsRegularNumber 2 := by
  rw [IsRegularNumber]
  convert coprime_one_right _
  dsimp
  apply (card_classGroup_eq_one_iff (R := 𝓞 (CyclotomicField (⟨2, two_pos⟩ : ℕ+) ℚ))).2
  infer_instance

end TwoRegular

theorem IsPrincipal_of_IsPrincipal_pow_of_Coprime
  (A : Type*) [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
  (p : ℕ) [Fact p.Prime]
  (H : p.Coprime <| Fintype.card <| ClassGroup A) (I : Ideal A)
  (hI : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero]
    exact bot_isPrincipal
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero _)] at hI ⊢
  swap; · exact Izero
  swap; · exact pow_ne_zero p Izero
  rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card⟩
  rwa [orderOf_dvd_iff_pow_eq_one, ← map_pow, SubmonoidClass.mk_pow]
