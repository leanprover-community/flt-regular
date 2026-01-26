module

public import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

section Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

variable {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]

lemma WfDvdMonoid.multiplicity_finite_iff [WfDvdMonoid M] {x y : M} :
    FiniteMultiplicity x y ↔ ¬IsUnit x ∧ y ≠ 0 :=
  ⟨fun h => ⟨h.not_unit, h.ne_zero⟩, and_imp.mpr FiniteMultiplicity.of_not_isUnit⟩

lemma dvd_iff_emultiplicity_le [UniqueFactorizationMonoid M] {a b : M} (ha : a ≠ 0) :
    a ∣ b ↔ ∀ p : M, Prime p → emultiplicity p a ≤ emultiplicity p b := by
  constructor
  · intro hab p _
    exact emultiplicity_le_emultiplicity_of_dvd_right hab
  · intro H
    by_cases hb : b = 0
    · exact hb ▸ dvd_zero a
    induction a using WfDvdMonoid.induction_on_irreducible with
    | zero => exact (ha rfl).elim
    | unit u hu => exact hu.dvd
    | mul a q _ hq IH =>
        simp only [ne_eq, mul_eq_zero, not_or] at ha
        rw [UniqueFactorizationMonoid.irreducible_iff_prime] at hq
        obtain ⟨c, rfl⟩ : a ∣ b := by
          refine IH ha.2 (fun p hp ↦ (le_trans ?_ (H p hp)))
          rw [emultiplicity_mul hp]
          exact le_add_self
        rw [mul_comm]
        simp only [mul_eq_zero, not_or] at hb
        refine mul_dvd_mul_left _ ?_
        rw [← pow_one q]
        apply pow_dvd_of_le_multiplicity
        have := H q hq
        rwa [emultiplicity_mul hq, emultiplicity_mul hq,
          (FiniteMultiplicity.of_not_isUnit hq.not_unit hb.2).emultiplicity_eq_multiplicity,
          (FiniteMultiplicity.of_not_isUnit hq.not_unit ha.2).emultiplicity_eq_multiplicity,
          (FiniteMultiplicity.of_not_isUnit hq.not_unit hq.ne_zero).emultiplicity_self,
          add_comm, add_le_add_iff_right_of_ne_top (ENat.coe_ne_top _), Nat.one_le_cast] at this

lemma pow_dvd_pow_iff_dvd [UniqueFactorizationMonoid M] {a b : M} {x : ℕ} (h' : x ≠ 0) :
    a ^ x ∣ b ^ x ↔ a ∣ b := by
  classical
  by_cases ha : a = 0
  · simp [ha, h']
  by_cases hb : b = 0
  · simp [hb, h']
  refine ⟨?_, fun h ↦ pow_dvd_pow_of_dvd h x⟩
  rw [dvd_iff_emultiplicity_le ha, dvd_iff_emultiplicity_le (pow_ne_zero x ha)]
  intro h p hp
  specialize h p hp
  rw [emultiplicity_pow hp, emultiplicity_pow hp,
    (FiniteMultiplicity.of_not_isUnit hp.not_unit ha).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_not_isUnit hp.not_unit hb).emultiplicity_eq_multiplicity,
    ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le] at h
  rw [(FiniteMultiplicity.of_not_isUnit hp.not_unit ha).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_not_isUnit hp.not_unit hb).emultiplicity_eq_multiplicity,
    Nat.cast_le]
  exact Nat.le_of_mul_le_mul_left h (Nat.pos_of_ne_zero h')

end Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}

open scoped nonZeroDivisors
open Polynomial

theorem isPrincipal_of_isPrincipal_pow_of_Coprime'
    {A K : Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
    [Field K] [Algebra A K] [IsFractionRing A K] (p : ℕ)
    (H : p.Coprime <| Fintype.card <| ClassGroup A) (I : FractionalIdeal A⁰ K)
    (hI : (↑(I ^ p) : Submodule A K).IsPrincipal) : (I : Submodule A K).IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero, FractionalIdeal.coe_zero]
    exact bot_isPrincipal
  rw [← Ne, ← isUnit_iff_ne_zero] at Izero
  change Submodule.IsPrincipal ((Izero.unit' : FractionalIdeal A⁰ K) : Submodule A K)
  rw [← ClassGroup.mk_eq_one_iff, ← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ClassGroup.mk_eq_one_iff]
  simp only [Units.val_pow_eq_pow_val, IsUnit.val_unit', hI]

open FractionalIdeal in
lemma exists_not_dvd_spanSingleton_eq {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : Prime x) (I J : Ideal R)
    (hI : ¬ (Ideal.span <| singleton x) ∣ I) (hJ : ¬ (Ideal.span <| singleton x) ∣ J)
    (h : Submodule.IsPrincipal ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) :
    ∃ a b : R,
      ¬(x ∣ a) ∧ ¬(x ∣ b) ∧ spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
  by_contra H1
  have hI' : (I : FractionalIdeal R⁰ K) ≠ 0 :=
    by rw [← coeIdeal_bot, Ne, coeIdeal_inj]; rintro rfl; exact hI (dvd_zero _)
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 :=
    by rw [← coeIdeal_bot, Ne, coeIdeal_inj]; rintro rfl; exact hJ (dvd_zero _)
  have : ∀ n : ℕ, (1 ≤ n) → ¬∃ a b : R, ¬(x ^ n ∣ a) ∧ ¬(x ^ n ∣ b) ∧
    spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        simp_rw [pow_one]
        exact H1
    | succ n' hn' IH =>
        rintro ⟨a, b, ha, hb, e⟩
        have e₀ := e
        rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton,
          ← one_div_spanSingleton, ← mul_div_assoc, mul_one, div_eq_iff,
          ← mul_div_right_comm, eq_div_iff hJ', ← coeIdeal_span_singleton,
            ← coeIdeal_span_singleton, ← coeIdeal_mul, ← coeIdeal_mul, coeIdeal_inj] at e
        on_goal 2 =>
          rw [Ne, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
            (IsFractionRing.injective R K).eq_iff]
          rintro rfl
          apply hb (dvd_zero _)
        by_cases h : x ^ n' ∣ a
        · have ha' : x ∣ a := (dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hn')).trans h
          have hb' : x ∣ b := by
            have : gcd (Ideal.span <| singleton x) I = 1 := by
              rwa [Irreducible.gcd_eq_one_iff]
              · rwa [irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
                · exact hx.ne_zero
                · rw [Ne, Ideal.span_singleton_eq_bot]
                  exact hx.ne_zero
            rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at ha' ⊢
            replace h := ha'.trans (dvd_mul_right _ J)
            rwa [e, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at h
          obtain ⟨a', rfl⟩ := ha'
          obtain ⟨b', rfl⟩ := hb'
          rw [pow_succ', mul_dvd_mul_iff_left hx.ne_zero] at ha hb
          rw [_root_.map_mul, _root_.map_mul, mul_div_mul_left] at e₀
          · exact IH ⟨a', b', ha, hb, e₀⟩
          · rw [Ne, ← (algebraMap R K).map_zero, (IsFractionRing.injective R K).eq_iff]
            exact hx.ne_zero
        · refine IH ⟨a, b, h, ?_, e₀⟩
          intro hb
          apply h
          rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at hb ⊢
          replace hb := hb.trans (dvd_mul_left _ I)
          have : gcd (Ideal.span <| singleton <| x ^ n') J = 1 := by
            rwa [← Ideal.isCoprime_iff_gcd, ← Ideal.span_singleton_pow,
              IsCoprime.pow_left_iff, Ideal.isCoprime_iff_gcd, Irreducible.gcd_eq_one_iff]
            · rwa [irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
              · exact hx.ne_zero
              · rw [Ne, Ideal.span_singleton_eq_bot]
                exact hx.ne_zero
            · rwa [Nat.pos_iff_ne_zero, ← Nat.one_le_iff_ne_zero]
          rwa [← e, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at hb
  rw [isPrincipal_iff] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ a
  by_cases h : s = 0
  · rw [div_eq_iff hJ', h, IsLocalization.mk'_zero, spanSingleton_zero, zero_mul] at ha
    exact hI' ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hx.not_unit h
  obtain ⟨m, hm⟩ := FiniteMultiplicity.of_not_isUnit hx.not_unit (nonZeroDivisors.ne_zero t.prop)
  rw [IsFractionRing.mk'_eq_div] at ha
  refine this (n + m + 1) (Nat.le_add_left 1 (n + m)) ⟨s, t, (fun hs ↦ ?_), (fun ht ↦ ?_), ha.symm⟩
  · exact hn (dvd_trans (pow_dvd_pow _ (by linarith)) hs)
  · exact hm (dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ _)) ht)
