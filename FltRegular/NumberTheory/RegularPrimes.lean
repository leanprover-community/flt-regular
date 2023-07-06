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
-- todo: now the diamond is fixed, `open_locale cyclotomic` may be fine.
instance safe {p : ℕ+} : _ :=
  IsCyclotomicExtension.numberField {p} ℚ <| CyclotomicField p ℚ

instance safe' {p : ℕ+} : _ :=
  IsCyclotomicExtension.finiteDimensional {p} ℚ <| CyclotomicField p ℚ

instance CyclotomicField.classGroupFinite {p : ℕ+} :
    Fintype (ClassGroup <| 𝓞 (CyclotomicField p ℚ)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ (CyclotomicField p ℚ) AbsoluteValue.absIsAdmissible

end SafeInstances

variable (n p : ℕ) [Fact p.Prime]

instance {p : ℕ} [hp : Fact p.Prime] : Fact (0 < p) :=
  ⟨hp.out.Pos⟩

-- note that this definition can be annoying to work with whilst #14984 isn't merged.
/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group -/
def IsRegularNumber [hn : Fact (0 < n)] : Prop :=
  n.coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField ⟨n, hn.out⟩ ℚ)

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
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K :=
  by
  suffices is_splitting_field K K (cyclotomic 2 K)
    by
    letI : is_splitting_field K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact
      (is_splitting_field.alg_equiv L (cyclotomic 2 K)).trans
        (is_splitting_field.alg_equiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using @splits_X_sub_C _ _ _ _ (RingHom.id K) (-1), by simp⟩

instance (L : Type _) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) :=
  by
  haveI : IsIntegralClosure ℤ ℤ L :=
    { algebraMap_injective := (algebraMap ℤ L).injective_int
      isIntegral_iff := fun x => by
        let f := cyclotomicFieldTwoEquiv ℚ L
        refine'
          ⟨fun hx => ⟨IsIntegralClosure.mk' ℤ (f x) (map_isIntegral_int f hx), f.injective _⟩, _⟩
        · convert IsIntegralClosure.algebraMap_mk' ℤ (f x) (map_isIntegral_int f hx)
          simp
        · rintro ⟨y, hy⟩
          simpa [← hy] using isIntegral_algebraMap }
  let F : 𝓞 L ≃+* ℤ := NumberField.RingOfIntegers.equiv _
  exact IsPrincipalIdealRing.of_surjective F.symm.to_ring_hom F.symm.surjective

theorem isRegularNumber_two : IsRegularNumber 2 :=
  by
  rw [IsRegularNumber]
  convert coprime_one_right _
  dsimp
  rw [card_classGroup_eq_one_iff]
  infer_instance

end TwoRegular

