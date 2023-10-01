import Mathlib.NumberTheory.Cyclotomic.Rat
import FltRegular.NumberTheory.Cyclotomic.Factoring
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.ClassGroup

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped BigOperators nonZeroDivisors NumberField
open Polynomial

variable {x y : 𝓞 K}

lemma Ideal.Quotient.eq_zero_iff_dvd {A : Type*} [CommRing A] (x y : A) :
  Ideal.Quotient.mk (Ideal.span ({x} : Set A)) y = 0 ↔ x ∣ y := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

lemma IsPrimitiveRoot.eq_one_mod_one_sub' {A : Type*} [CommRing A] [IsDomain A]
  {n : ℕ+} {ζ : A} (hζ : IsPrimitiveRoot ζ n) {η : A} (hη : η ∈ nthRootsFinset n A) :
  Ideal.Quotient.mk (Ideal.span ({ζ - 1} : Set A)) η = 1 := by
  obtain ⟨i, ⟨_, rfl⟩⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset n.2).1 hη) n.2
  rw [map_pow, ← Ideal.Quotient.algebraMap_eq, eq_one_mod_one_sub, one_pow]

lemma IsUnit_neg_one {A : Type*} [CommRing A] : IsUnit (-1 : A) := by simp

lemma IsPrimitiveRoot.associated_sub_one {A : Type*} [CommRing A] [IsDomain A]
  {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ p) {η₁ : A} (hη₁ : η₁ ∈ nthRootsFinset p A)
  {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p A) (e : η₁ ≠ η₂) :
  Associated (ζ - 1) (η₁ - η₂) := by
  obtain ⟨i, ⟨hi, rfl⟩⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos).1 hη₁) hp.pos
  obtain ⟨j, ⟨hj, rfl⟩⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos).1 hη₂) hp.pos
  have : i ≠ j := by
    rintro rfl
    exact e rfl
  obtain ⟨u, h⟩ := IsCyclotomicExtension.CyclotomicUnit.IsPrimitiveRoot.zeta_pow_sub_eq_unit_zeta_sub_one A
    hp.two_le hp hi hj this hζ
  rw [h, associated_isUnit_mul_right_iff u.isUnit, ← associated_isUnit_mul_right_iff IsUnit_neg_one,
    neg_one_mul, neg_sub]
  rfl

variable (hp : p ≠ 2) (h : (hζ.unit' : 𝓞 K) - 1 ∣ x ^ (p : ℕ) + y ^ (p : ℕ))
  {η : 𝓞 K} (hη : η ∈ nthRootsFinset p (𝓞 K))

lemma IsPrimitiveRoot.sub_one_ne_zero {A : Type*} [CommRing A] {n : ℕ} (hn : 1 < n) {ζ : A}
  (hζ : IsPrimitiveRoot ζ n) : ζ - 1 ≠ 0 := by
  rw [Ne.def, sub_eq_zero]
  exact hζ.ne_one hn

instance CharZero.subsemiring {A : Type*} [Semiring A] {S : Type*} [SetLike S A]
  [SubsemiringClass S A] [CharZero A] (x : S) :
  CharZero x := by
  constructor
  intro i j e
  apply CharZero.cast_injective (R := A)
  show ((i : x) : A) = (j : x)
  rw [e]

instance : CharZero (𝓞 K) := CharZero.subsemiring (𝓞 K)

lemma Ideal.Norm.eq_zero_iff {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
  [Infinite A] [Module.Free ℤ A] [Module.Finite ℤ A]
  {I : Ideal A} : Ideal.absNorm I = 0 ↔ I = ⊥ := by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intros x hx
    rw [mem_bot, ← Algebra.norm_eq_zero_iff (R := ℤ), ← Int.natAbs_eq_zero, ← Ideal.absNorm_span_singleton,
      ← zero_dvd_iff, ← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_iff_mem]
  · rintro rfl
    exact absNorm_bot

lemma Algebra.coe_norm_Int {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
  Algebra.norm ℤ x = Algebra.norm ℚ (x : K) :=
(Algebra.norm_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

lemma Ideal.coprime_iff_sup {R : Type*} [CommRing R] {I J : Ideal R} :
  IsCoprime I J ↔ I ⊔ J = ⊤ := by
  rw [IsCoprime]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J ≤ I ⊔ J from
      sup_le (mul_le_left.trans le_sup_left) (mul_le_left.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
    refine' ⟨1, 1, _⟩
    simpa only [one_eq_top, top_mul, Submodule.add_eq_sup, ge_iff_le]

lemma Ideal.coprime_iff_gcd {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  {I J : Ideal R} :
  IsCoprime I J ↔ gcd I J = 1 := by
  rw [Ideal.coprime_iff_sup, one_eq_top]
  rfl

lemma Irreducible.dvd_iff {M : Type*} [Monoid M]
  {x y : M} (hx : Irreducible x) : y ∣ x ↔ IsUnit y ∨ Associated x y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain (h|h) := hx.2 _ _ hz
    · exact Or.inl h
    · rw [hz]
      exact Or.inr (associated_mul_unit_left _ _ h)
  · rintro (hy|h)
    · exact hy.dvd
    · exact h.symm.dvd

lemma associated_gcd_iff
  {M : Type*} [CancelCommMonoidWithZero M] [GCDMonoid M] {x y : M} :
  Associated x (gcd x y) ↔ x ∣ y :=
⟨λ hx ↦ hx.dvd.trans (gcd_dvd_right x y),
  λ hxy ↦ associated_of_dvd_dvd (dvd_gcd (dvd_refl x) hxy) (gcd_dvd_left x y)⟩

lemma Irreducible.is_unit_iff_not_associated_of_dvd
  {M : Type*} [CancelCommMonoidWithZero M] [GCDMonoid M]
  {x y : M} (hx : Irreducible x) (hy : y ∣ x) : IsUnit y ↔ ¬ Associated x y :=
⟨λ hy hxy ↦ hx.1 (hxy.symm.isUnit hy), (hx.dvd_iff.mp hy).resolve_right⟩

lemma Irreducible.isUnit_gcd_iff {M : Type*} [CancelCommMonoidWithZero M] [GCDMonoid M]
  {x y : M} (hx : Irreducible x) :
  IsUnit (gcd x y) ↔ ¬(x ∣ y) := by
  rw [hx.is_unit_iff_not_associated_of_dvd (gcd_dvd_left x y), not_iff_not, associated_gcd_iff]

lemma Irreducible.gcd_eq_one_iff {M : Type*} [CancelCommMonoidWithZero M] [NormalizedGCDMonoid M]
  {x y : M} (hx : Irreducible x) :
  gcd x y = 1 ↔ ¬(x ∣ y) := by
  rw [← hx.isUnit_gcd_iff, ← normalize_eq_one, NormalizedGCDMonoid.normalize_gcd]

instance foofoo [NumberField K] : IsDomain (Ideal (𝓞 K)) :=
by convert Ideal.isDomain (A := 𝓞 K)

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
    · simp only [← mul_assoc, ← pow_succ', ← hf]
    · intro e
      apply hy
      rw [hf n, e, zero_mul]

lemma WfDvdMonoid.multiplicity_finite_iff {M : Type*} [CancelCommMonoidWithZero M] [WfDvdMonoid M]
  {x y : M} :
  multiplicity.Finite x y ↔ ¬IsUnit x ∧ y ≠ 0 := by
  constructor
  · rw [← not_imp_not, Ne.def, ← not_or, not_not]
    rintro (hx|hy)
    · exact λ ⟨n, hn⟩ ↦ hn (hx.pow _).dvd
    · simp [hy]
  · intro ⟨hx, hy⟩
    exact WfDvdMonoid.multiplicity_finite hx hy

lemma WfDvdMonoid.multiplicity_eq_top_iff {M : Type*} [CancelCommMonoidWithZero M] [WfDvdMonoid M]
  [DecidableRel (λ a b : M ↦ a ∣ b)] {x y : M} :
  multiplicity x y = ⊤ ↔ IsUnit x ∨ y = 0 := by
  rw [multiplicity.eq_top_iff_not_finite, WfDvdMonoid.multiplicity_finite_iff, or_iff_not_and_not]

lemma dvd_iff_multiplicity_le {M : Type*}
  [CancelCommMonoidWithZero M] [DecidableRel (λ a b : M ↦ a ∣ b)] [UniqueFactorizationMonoid M]
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
          refine' IH ha.2 (λ p hp ↦ (le_trans ?_ (H p hp)))
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
  · simp at hk'
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
  · rw [ha, zero_pow (Nat.pos_iff_ne_zero.mpr h'), zero_dvd_iff, zero_dvd_iff,
      pow_eq_zero_iff (Nat.pos_iff_ne_zero.mpr h')]
  have ha' : a ^ x ≠ 0 := (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mpr h')).not.mpr ha
  rw [dvd_iff_multiplicity_le ha, dvd_iff_multiplicity_le ha']
  refine forall₂_congr (λ p hp ↦ ?_)
  simp_rw [multiplicity.pow hp, ← PartENat.withTopEquiv_le]
  show PartENat.withTopAddEquiv _ ≤ PartENat.withTopAddEquiv _ ↔ _
  simp_rw [map_nsmul]
  rw [ENat.nsmul_mono h']
  rfl

theorem isPrincipal_of_isPrincipal_pow_of_Coprime'
  {A K: Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
  [Field K] [Algebra A K] [IsFractionRing A K] (p : ℕ)
  (H : p.Coprime <| Fintype.card <| ClassGroup A) (I : FractionalIdeal A⁰ K)
  (hI : (I ^ p : Submodule A K).IsPrincipal) : (I : Submodule A K).IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero, FractionalIdeal.coe_zero]
    exact bot_isPrincipal
  rw [← Ne.def, ← isUnit_iff_ne_zero] at Izero
  show Submodule.IsPrincipal (Izero.unit' : FractionalIdeal A⁰ K)
  rw [← ClassGroup.mk_eq_one_iff, ← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card_univ⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ClassGroup.mk_eq_one_iff]
  simp only [Units.val_pow_eq_pow_val, IsUnit.val_unit', FractionalIdeal.coe_pow]
  exact hI

lemma mul_mem_nthRootsFinset {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (hn : 0 < n)
  {η₁ : R} (hη₁ : η₁ ∈ nthRootsFinset n R) {η₂ : R} (hη₂ : η₂ ∈ nthRootsFinset n R) :
  η₁ * η₂ ∈ nthRootsFinset n R := by
  rw [mem_nthRootsFinset hn] at hη₁ hη₂ ⊢
  rw [mul_pow, hη₁, hη₂, one_mul]

lemma Prime.not_dvd_mul {M : Type*} [CommMonoidWithZero M] {p : M} (hp : Prime p) {a b : M}
  (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
λ h ↦ or_iff_not_and_not.mp (hp.dvd_or_dvd h) ⟨ha, hb⟩

lemma ne_zero_of_mem_nthRootsFinset {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (hn : 0 < n)
  {η : R} (hη : η ∈ nthRootsFinset n R) : η ≠ 0 := by
    nontriviality R
    rintro rfl
    rw [mem_nthRootsFinset hn, zero_pow hn] at hη
    exact zero_ne_one hη

lemma IsPrimitiveRoot.prime_span_sub_one : Prime (Ideal.span <| singleton <| (hζ.unit' - 1 : 𝓞 K)) := by
  haveI : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Ideal.prime_iff_isPrime,
    Ideal.span_singleton_prime (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)]
  exact IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp
  · rw [Ne.def, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma norm_Int_zeta_sub_one : Algebra.norm ℤ (↑(IsPrimitiveRoot.unit' hζ) - 1 : 𝓞 K) = p := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  simp [Algebra.coe_norm_Int, hζ.sub_one_norm_prime (cyclotomic.irreducible_rat p.2) hp]

lemma Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι → M) (g : ι → M)
  (h : ∀ i, i ∈ s → Associated (f i) (g i)) : Associated (∏ i in s, f i) (∏ i in s, g i) := by
    induction' s using Finset.induction with j s hjs IH
    · simp only [Finset.prod_empty]
      rfl
    · classical
      convert_to Associated (∏ i in insert j s, f i) (∏ i in insert j s, g i)
      rw [Finset.prod_insert hjs, Finset.prod_insert hjs]
      exact Associated.mul_mul (h j (Finset.mem_insert_self j s))
        (IH (λ i hi ↦ h i (Finset.mem_insert_of_mem hi)))

lemma one_mem_nthRootsFinset {n : ℕ} (hn : 0 < n) (R : Type*) [CommRing R] [IsDomain R] :
  1 ∈ nthRootsFinset n R := by rw [mem_nthRootsFinset hn, one_pow]

lemma associated_zeta_sub_one_pow_prime : Associated ((hζ.unit' - 1 : 𝓞 K) ^ (p - 1 : ℕ)) p := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p),
    cyclotomic_eq_prod_X_sub_primitiveRoots hζ.unit'_coe, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hpri.out, ← hζ.unit'_coe.card_primitiveRoots, ← Finset.prod_const]
  apply Associated.prod
  intro η hη
  exact hζ.unit'_coe.associated_sub_one hpri.out
    (one_mem_nthRootsFinset hpri.out.pos _)
    ((isPrimitiveRoot_of_mem_primitiveRoots hη).mem_nthRootsFinset hpri.out.pos)
      ((isPrimitiveRoot_of_mem_primitiveRoots hη).ne_one hpri.out.one_lt).symm

lemma Ideal.isCoprime_span_singleton_iff {R : Type*} [CommRing R] (x y : R) :
  IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y := by
  simp_rw [coprime_iff_sup, eq_top_iff_one, mem_span_singleton_sup, mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

lemma is_coprime_of_not_zeta_sub_one_dvd (hx : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ x) : IsCoprime ↑p x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rwa [← Ideal.isCoprime_span_singleton_iff, ← Ideal.span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime hζ), ← Ideal.span_singleton_pow, IsCoprime.pow_left_iff,
    Ideal.coprime_iff_gcd, (hζ.prime_span_sub_one hp).irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton]
  · simpa only [ge_iff_le, tsub_pos_iff_lt] using hpri.out.one_lt

lemma exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) : ∃ b : ℤ, (hζ.unit' - 1: 𝓞 K) ∣ a - b := by
  letI : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.unit' - 1: 𝓞 K))) := inferInstance
  letI : Fact (Nat.Prime p) := hpri
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero, ← SModEq.Ideal_def]
  convert exists_int_sModEq hζ.subOneIntegralPowerBasis' a
  rw [hζ.subOneIntegralPowerBasis'_gen]
  rfl

lemma exists_dvd_pow_sub_Int_pow (a : 𝓞 K) : ∃ b : ℤ, ↑p ∣ a ^ (p : ℕ) - (b : 𝓞 K) ^ (p : ℕ) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root ℚ (B := K) (Set.mem_singleton p)
  obtain ⟨b, k, e⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out a (-b)
  obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
  rw [(Nat.Prime.odd_of_ne_two hpri.out (PNat.coe_injective.ne hp)).neg_pow, ← sub_eq_add_neg, e,
    mul_pow, ← sub_eq_add_neg] at hr
  nth_rw 1 [← Nat.sub_add_cancel (n := p) (m := 1) hpri.out.one_lt.le] at hr
  rw [pow_succ', ← hu, mul_assoc, mul_assoc] at hr
  use b, ↑u * ((hζ.unit' - 1 : 𝓞 K) * k ^ (p : ℕ)) - r
  rw [mul_sub, hr, add_sub_cancel]

lemma Ideal.span_singleton_absNorm {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Infinite R] [Module.Free ℤ R] [Module.Finite ℤ R] (I : Ideal R) (hI : (Ideal.absNorm I).Prime) :
  Ideal.span (singleton (Ideal.absNorm I : ℤ)) = I.comap (algebraMap ℤ R) := by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : ℤ))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap ℤ R)).ne_top
  · rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
    exact absNorm_mem I
  · rw [Ne.def, span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hI.ne_zero

lemma norm_dvd_iff {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Infinite R] [Module.Free ℤ R] [Module.Finite ℤ R] (x : R) (hx : Prime (Algebra.norm ℤ x)) {y : ℤ} :
  Algebra.norm ℤ x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x), ← eq_intCast (algebraMap ℤ R), ← Ideal.mem_comap,
    ← Ideal.span_singleton_absNorm, Ideal.mem_span_singleton, Ideal.absNorm_span_singleton,
    Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

theorem dvd_gcd_mul_iff_dvd_mul {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]
  {m n k : α} : k ∣ gcd k m * n ↔ k ∣ m * n :=
⟨λ h ↦ h.trans (mul_dvd_mul (gcd_dvd_right k m) (dvd_refl _)), dvd_gcd_mul_of_dvd_mul⟩

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
      by_cases x ^ n' ∣ a
      · have ha' : x ∣ a := (dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hn')).trans h
        have hb' : x ∣ b := by
          have : gcd (Ideal.span <| singleton x) I = 1 := by
            rwa [Irreducible.gcd_eq_one_iff]
            · rwa [GCDMonoid.irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
              · exact hx.ne_zero
              · rw [Ne.def, Ideal.span_singleton_eq_bot]
                exact hx.ne_zero
          rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton] at ha' ⊢
          replace h := ha'.trans (dvd_mul_right _ J)
          rwa [e, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at h
        obtain ⟨a', rfl⟩ := ha'
        obtain ⟨b', rfl⟩ := hb'
        rw [pow_succ, mul_dvd_mul_iff_left hx.ne_zero] at ha hb
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
          rwa [← Ideal.coprime_iff_gcd, ← Ideal.span_singleton_pow,
            IsCoprime.pow_left_iff, Ideal.coprime_iff_gcd, Irreducible.gcd_eq_one_iff]
          · rwa [GCDMonoid.irreducible_iff_prime, Ideal.prime_iff_isPrime, Ideal.span_singleton_prime]
            · exact hx.ne_zero
            · rw [Ne.def, Ideal.span_singleton_eq_bot]
              exact hx.ne_zero
          · rwa [Nat.pos_iff_ne_zero, ← Nat.one_le_iff_ne_zero]
        rwa [← e, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, this, one_mul] at hb
  rw [isPrincipal_iff] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨s, t, rfl⟩ := IsLocalization.mk'_surjective R⁰ a
  by_cases s = 0
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

lemma Prime.dvd_pow_iff_dvd {α : Type*} [CommMonoidWithZero α] {p : α} (hp : Prime p) {a : α} {n : ℕ}
  (hn : n ≠ 0) : p ∣ a ^ n ↔ p ∣ a :=
⟨hp.dvd_of_dvd_pow, λ h ↦ dvd_pow h hn⟩

lemma zeta_sub_one_dvd_Int_iff {n : ℤ} : (hζ.unit' : 𝓞 K) - 1 ∣ n ↔ ↑p ∣ n := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [← norm_Int_zeta_sub_one hζ hp, norm_dvd_iff]
  rw [norm_Int_zeta_sub_one hζ hp, ← Nat.prime_iff_prime_int]
  exact hpri.out
