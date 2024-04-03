import Mathlib.NumberTheory.Cyclotomic.Rat
import FltRegular.NumberTheory.Cyclotomic.Factoring
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.ClassGroup
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import FltRegular.ReadyForMathlib.PowerBasis

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped BigOperators nonZeroDivisors NumberField
open Polynomial

instance : CharZero (𝓞 K) := SubsemiringClass.instCharZero (𝓞 K)

instance foofoo [NumberField K] : IsDomain (Ideal (𝓞 K)) := by convert Ideal.isDomain (A := 𝓞 K)

instance [NumberField K] : CancelMonoidWithZero (Ideal (𝓞 K)) :=
  @IsDomain.toCancelMonoidWithZero _ _ foofoo

lemma WfDvdMonoid.multiplicity_finite {M : Type*} [CancelCommMonoidWithZero M] [WfDvdMonoid M]
    {x y : M} (hx : ¬ IsUnit x) (hy : y ≠ 0) :
    multiplicity.Finite x y := by
  by_contra h
  rw [multiplicity.Finite, not_exists_not] at h
  choose f hf using h
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    (WfDvdMonoid.wellFounded_dvdNotUnit (α := M)).has_min (Set.range f) (Set.range_nonempty f)
  apply hn _ ⟨n + 1, rfl⟩
  constructor
  · intro e
    apply hy
    rw [hf (n + 1), e, mul_zero]
  · refine ⟨x, hx, ?_⟩
    rw [mul_comm, ← (mul_right_injective₀ (a := x ^ (n + 1)) _).eq_iff]
    · simp only [← mul_assoc, ← pow_succ, ← hf]
    · intro e
      apply hy
      rw [hf n, e, zero_mul]

lemma WfDvdMonoid.multiplicity_finite_iff {M : Type*} [CancelCommMonoidWithZero M] [WfDvdMonoid M]
    {x y : M} :
  multiplicity.Finite x y ↔ ¬IsUnit x ∧ y ≠ 0 := by
  constructor
  · rw [← not_imp_not, Ne.def, ← not_or, not_not]
    rintro (hx|hy)
    · exact fun ⟨n, hn⟩ ↦ hn (hx.pow _).dvd
    · simp [hy]
  · intro ⟨hx, hy⟩
    exact WfDvdMonoid.multiplicity_finite hx hy

lemma WfDvdMonoid.multiplicity_eq_top_iff {M : Type*} [CancelCommMonoidWithZero M] [WfDvdMonoid M]
    [DecidableRel (fun a b : M ↦ a ∣ b)] {x y : M} :
    multiplicity x y = ⊤ ↔ IsUnit x ∨ y = 0 := by
  rw [multiplicity.eq_top_iff_not_finite, WfDvdMonoid.multiplicity_finite_iff, or_iff_not_and_not]

lemma dvd_iff_multiplicity_le {M : Type*}
    [CancelCommMonoidWithZero M] [DecidableRel (fun a b : M ↦ a ∣ b)] [UniqueFactorizationMonoid M]
    {a b : M} (ha : a ≠ 0) : a ∣ b ↔ ∀ p : M, Prime p → multiplicity p a ≤ multiplicity p b := by
  constructor
  · intro hab p _
    exact multiplicity.multiplicity_le_multiplicity_of_dvd_right hab
  · intro H
    by_cases hb : b = 0
    · exact hb ▸ dvd_zero a
    induction' a using WfDvdMonoid.induction_on_irreducible with u hu a q _ hq IH
    · exact (ha rfl).elim
    · exact hu.dvd
    · simp only [ne_eq, mul_eq_zero, not_or] at ha
      rw [UniqueFactorizationMonoid.irreducible_iff_prime] at hq
      obtain ⟨c, rfl⟩ : a ∣ b := by
        refine' IH ha.2 (fun p hp ↦ (le_trans ?_ (H p hp)))
        rw [multiplicity.mul hp]
        exact le_add_self
      rw [mul_comm]
      simp only [ne_eq, mul_eq_zero, not_or] at hb
      have := H q hq
      rw [multiplicity.mul hq, multiplicity.mul hq, add_comm,
        ← PartENat.natCast_get (multiplicity.finite_iff_dom.mp
          (WfDvdMonoid.multiplicity_finite hq.not_unit ha.2)),
        ← PartENat.natCast_get (multiplicity.finite_iff_dom.mp
          (WfDvdMonoid.multiplicity_finite hq.not_unit hb.2)),
        ← PartENat.natCast_get (multiplicity.finite_iff_dom.mp
          (WfDvdMonoid.multiplicity_finite hq.not_unit ha.1)),
        ← Nat.cast_add, ← Nat.cast_add, PartENat.coe_le_coe,
        multiplicity.get_multiplicity_self, add_le_add_iff_left,
        ← PartENat.coe_le_coe, PartENat.natCast_get, ← multiplicity.pow_dvd_iff_le_multiplicity,
        pow_one] at this
      exact mul_dvd_mul_left _ this

lemma ENat.mul_mono_left {k n m : ℕ∞} (hk : k ≠ 0) (hk' : k ≠ ⊤) : k * n ≤ k * m ↔ n ≤ m := by
  obtain (n|n) := n
  · rw [WithTop.none_eq_top, top_le_iff, WithTop.mul_top hk, top_le_iff, WithTop.mul_eq_top_iff,
      iff_true_intro hk, iff_false_intro hk']
    simp
  obtain (m|m) := m
  · simp only [WithTop.none_eq_top, le_top, iff_true]
    rw [WithTop.mul_top hk]
    simp
  obtain (k|k) := k
  · simp at hk'; contradiction
  simp_rw [WithTop.some_eq_coe, ENat.some_eq_coe]
  rw [← ENat.coe_mul, ← ENat.coe_mul, Nat.cast_le, Nat.cast_le]
  refine (strictMono_mul_left_of_pos (Nat.pos_of_ne_zero ?_)).le_iff_le
  rintro rfl
  exact hk rfl

lemma ENat.nsmul_mono {n m : ℕ∞} {k : ℕ} (hk : k ≠ 0) : k • n ≤ k • m ↔ n ≤ m := by
  simp_rw [nsmul_eq_mul]
  apply ENat.mul_mono_left
  · exact Nat.cast_ne_zero.mpr hk
  · exact coe_ne_top k

lemma pow_dvd_pow_iff_dvd {M : Type*} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M]
    {a b : M} {x : ℕ} (h' : x ≠ 0) : a ^ x ∣ b ^ x ↔ a ∣ b := by
  classical
  by_cases ha : a = 0
  · rw [ha, zero_pow h', zero_dvd_iff, zero_dvd_iff, pow_eq_zero_iff h']
  have ha' : a ^ x ≠ 0 := (pow_ne_zero_iff h').mpr ha
  rw [dvd_iff_multiplicity_le ha, dvd_iff_multiplicity_le ha']
  refine forall₂_congr (fun p hp ↦ ?_)
  simp_rw [multiplicity.pow hp, ← PartENat.withTopEquiv_le]
  show PartENat.withTopAddEquiv _ ≤ PartENat.withTopAddEquiv _ ↔ _
  simp_rw [map_nsmul]
  rw [ENat.nsmul_mono h']
  rfl

theorem isPrincipal_of_isPrincipal_pow_of_Coprime'
    {A K: Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
    [Field K] [Algebra A K] [IsFractionRing A K] (p : ℕ)
    (H : p.Coprime <| Fintype.card <| ClassGroup A) (I : FractionalIdeal A⁰ K)
    (hI : (↑(I ^ p) : Submodule A K).IsPrincipal) : (I : Submodule A K).IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero, FractionalIdeal.coe_zero]
    exact bot_isPrincipal
  rw [← Ne.def, ← isUnit_iff_ne_zero] at Izero
  show Submodule.IsPrincipal (Izero.unit' : FractionalIdeal A⁰ K)
  rw [← ClassGroup.mk_eq_one_iff, ← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ClassGroup.mk_eq_one_iff]
  simp only [Units.val_pow_eq_pow_val, IsUnit.val_unit', hI]

variable (hp : p ≠ 2)

open FractionalIdeal in
lemma exists_not_dvd_spanSingleton_eq {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x : R} (hx : Prime x) (I J : Ideal R)
    (hI : ¬ (Ideal.span <| singleton x) ∣ I) (hJ : ¬ (Ideal.span <| singleton x) ∣ J)
    (h : Submodule.IsPrincipal ((I / J : FractionalIdeal R⁰ K) : Submodule R K)) :
    ∃ a b : R, ¬(x ∣ a) ∧ ¬(x ∣ b) ∧ spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
  by_contra H1
  have hI' : (I : FractionalIdeal R⁰ K) ≠ 0 :=
    by rw [← coeIdeal_bot, Ne.def, coeIdeal_inj]; rintro rfl; exact hI (dvd_zero _)
  have hJ' : (J : FractionalIdeal R⁰ K) ≠ 0 :=
    by rw [← coeIdeal_bot, Ne.def, coeIdeal_inj]; rintro rfl; exact hJ (dvd_zero _)
  have : ∀ n : ℕ, (1 ≤ n) → ¬∃ a b : R, ¬(x ^ n ∣ a) ∧ ¬(x ^ n ∣ b) ∧
    spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) = I / J := by
    intro n hn
    induction' n, hn using Nat.le_induction with n' hn' IH
    · simp_rw [pow_one]
      exact H1
    · rintro ⟨a, b, ha, hb, e⟩
      have e₀ := e
      rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton,
        ← one_div_spanSingleton, ← mul_div_assoc, mul_one, div_eq_iff,
        ← mul_div_right_comm, eq_div_iff hJ', ← coeIdeal_span_singleton, ← coeIdeal_span_singleton,
        ← coeIdeal_mul, ← coeIdeal_mul, coeIdeal_inj] at e
      on_goal 2 =>
        rw [Ne.def, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
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
              · rw [Ne.def, Ideal.span_singleton_eq_bot]
                exact hx.ne_zero
          rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at ha' ⊢
          replace h := ha'.trans (dvd_mul_right _ J)
          rwa [e, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at h
        obtain ⟨a', rfl⟩ := ha'
        obtain ⟨b', rfl⟩ := hb'
        rw [pow_succ', mul_dvd_mul_iff_left hx.ne_zero] at ha hb
        rw [_root_.map_mul, _root_.map_mul, mul_div_mul_left] at e₀
        · exact IH ⟨a', b', ha, hb, e₀⟩
        · rw [Ne.def, ← (algebraMap R K).map_zero, (IsFractionRing.injective R K).eq_iff]
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
            · rw [Ne.def, Ideal.span_singleton_eq_bot]
              exact hx.ne_zero
          · rwa [Nat.pos_iff_ne_zero, ← Nat.one_le_iff_ne_zero]
        rwa [← e, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at hb
  rw [isPrincipal_iff] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨s, t, rfl⟩ := IsLocalization.mk'_surjective R⁰ a
  by_cases h : s = 0
  · rw [div_eq_iff hJ', h, IsLocalization.mk'_zero, spanSingleton_zero, zero_mul] at ha
    exact hI' ha
  obtain ⟨n, hn⟩ := WfDvdMonoid.multiplicity_finite hx.not_unit h
  obtain ⟨m, hm⟩ := WfDvdMonoid.multiplicity_finite hx.not_unit (nonZeroDivisors.ne_zero t.prop)
  rw [IsFractionRing.mk'_eq_div] at ha
  refine this (n + m + 1) (Nat.le_add_left 1 (n + m)) ⟨s, t, ?_, ?_, ha.symm⟩
  · intro hs
    refine hn (dvd_trans (pow_dvd_pow _ ?_) hs)
    linarith
  · intro ht
    refine hm (dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ _)) ht)
