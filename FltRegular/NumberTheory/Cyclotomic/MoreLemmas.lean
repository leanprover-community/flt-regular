import Mathlib.NumberTheory.Cyclotomic.Rat
import FltRegular.NumberTheory.Cyclotomic.Factoring
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.Cyclotomic.CyclRat
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.NormTrace
import FltRegular.ReadyForMathlib.PowerBasis
import FltRegular.NumberTheory.AuxLemmas
import Mathlib.Algebra.CharZero.Infinite

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped BigOperators nonZeroDivisors NumberField
open Polynomial

variable (hp : p ≠ 2)

lemma IsPrimitiveRoot.prime_span_sub_one : Prime (Ideal.span <| singleton <| (hζ.unit' - 1 : 𝓞 K)) := by
  haveI : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Ideal.prime_iff_isPrime,
    Ideal.span_singleton_prime (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)]
  exact hζ.zeta_sub_one_prime'
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma norm_Int_zeta_sub_one : Algebra.norm ℤ (↑(IsPrimitiveRoot.unit' hζ) - 1 : 𝓞 K) = p := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  simp [Algebra.coe_norm_int, hζ.sub_one_norm_prime (cyclotomic.irreducible_rat p.2) hp]

@[simp]
lemma PNat.coe_two : (2 : ℕ+) = (2 : ℕ) := rfl

lemma surjective_of_isCyclotomicExtension_two (R S) [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [IsCyclotomicExtension {2} R S] :
    Function.Surjective (algebraMap R S) := by
  intro x
  have := IsCyclotomicExtension.adjoin_roots (S := {2}) (A := R) (B := S) x
  simp only [Set.mem_singleton_iff, exists_eq_left, sq_eq_one_iff, PNat.coe_two] at this
  have H : Algebra.adjoin R {b : S | b = 1 ∨ b = -1} ≤ ⊥ := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (rfl|rfl)
    · exact one_mem _
    · exact neg_mem (one_mem _)
  exact H this

theorem IsPrimitiveRoot.sub_one_norm_two' {K L} [Field K] [Field L] [Algebra K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 2)
    [IsCyclotomicExtension {2} K L] : Algebra.norm K (ζ - 1) = -2 := by
  rw [hζ.eq_neg_one_of_two_right]
  suffices Algebra.norm K (algebraMap K L (-2)) = -2 by
    simpa only [sub_eq_add_neg, ← one_add_one_eq_two,
      neg_add_rev, map_add, map_neg, map_one] using this
  rw [Algebra.norm_algebraMap, finrank_eq_one_iff'.mpr, pow_one]
  refine ⟨1, one_ne_zero, fun w ↦ ?_⟩
  simpa only [Algebra.algebraMap_eq_smul_one] using surjective_of_isCyclotomicExtension_two K L w

lemma norm_Int_zeta_sub_one' (hp : p = 2) :
    Algebra.norm ℤ (↑(IsPrimitiveRoot.unit' hζ) - 1 : 𝓞 K) = -p := by
  clear ‹p ≠ 2›
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  subst hp
  simp [Algebra.coe_norm_int, hζ.sub_one_norm_two']

lemma associated_zeta_sub_one_pow_prime : Associated ((hζ.unit' - 1 : 𝓞 K) ^ (p - 1 : ℕ)) p := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p),
    cyclotomic_eq_prod_X_sub_primitiveRoots hζ.unit'_coe, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime this.out, ← hζ.unit'_coe.card_primitiveRoots, ← Finset.prod_const]
  apply Associated.prod
  intro η hη
  exact hζ.unit'_coe.associated_sub_one hpri.out
    (one_mem_nthRootsFinset this.out.pos)
    ((isPrimitiveRoot_of_mem_primitiveRoots hη).mem_nthRootsFinset hpri.out.pos)
      ((isPrimitiveRoot_of_mem_primitiveRoots hη).ne_one hpri.out.one_lt).symm

lemma isCoprime_of_not_zeta_sub_one_dvd (hx : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ x) : IsCoprime ↑p x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rwa [← Ideal.isCoprime_span_singleton_iff,
    ← Ideal.span_singleton_eq_span_singleton.mpr (associated_zeta_sub_one_pow_prime hζ),
    ← Ideal.span_singleton_pow, IsCoprime.pow_left_iff, Ideal.isCoprime_iff_gcd,
    hζ.prime_span_sub_one.irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton]
  · simpa only [ge_iff_le, tsub_pos_iff_lt] using hpri.out.one_lt

set_option synthInstance.maxHeartbeats 80000 in
lemma exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) : ∃ b : ℤ, (hζ.unit' - 1: 𝓞 K) ∣ a - b := by
  letI : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.unit' - 1: 𝓞 K))) := inferInstance
  letI : Fact (Nat.Prime p) := hpri
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero, ← SModEq.Ideal_def]
  convert exists_int_sModEq hζ.subOneIntegralPowerBasis' a
  rw [hζ.subOneIntegralPowerBasis'_gen]
  rw [Subtype.ext_iff, AddSubgroupClass.coe_sub, IsPrimitiveRoot.val_unit'_coe, OneMemClass.coe_one]
  rfl

lemma exists_dvd_pow_sub_Int_pow (a : 𝓞 K) : ∃ b : ℤ, ↑p ∣ a ^ (p : ℕ) - (b : 𝓞 K) ^ (p : ℕ) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_prim_root ℚ (B := K) (Set.mem_singleton p)
  obtain ⟨b, k, e⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out a (-b)
  obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
  rw [(Nat.Prime.odd_of_ne_two hpri.out (PNat.coe_injective.ne hp)).neg_pow, ← sub_eq_add_neg, e,
    mul_pow, ← sub_eq_add_neg] at hr
  nth_rw 1 [← Nat.sub_add_cancel (n := p) (m := 1) hpri.out.one_lt.le] at hr
  rw [pow_succ, ← hu, mul_assoc, mul_assoc] at hr
  use b, ↑u * ((hζ.unit' - 1 : 𝓞 K) * k ^ (p : ℕ)) - r
  rw [mul_sub, hr, add_sub_cancel_right]

lemma norm_dvd_iff {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Infinite R] [Module.Free ℤ R] [Module.Finite ℤ R] (x : R) (hx : Prime (Algebra.norm ℤ x)) {y : ℤ} :
    Algebra.norm ℤ x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x), ← eq_intCast (algebraMap ℤ R), ← Ideal.mem_comap,
    ← Ideal.span_singleton_absNorm, Ideal.mem_span_singleton, Ideal.absNorm_span_singleton,
    Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

section

variable {α} [CommMonoidWithZero α]

theorem prime_units_mul (a : αˣ) (b : α) : Prime (↑a * b) ↔ Prime b := by simp [Prime]

theorem prime_isUnit_mul {a b : α} (h : IsUnit a) : Prime (a * b) ↔ Prime b :=
  let ⟨a, ha⟩ := h
  ha ▸ prime_units_mul a b

theorem prime_mul_units (a : αˣ) (b : α) : Prime (b * ↑a) ↔ Prime b := by simp [Prime]

theorem prime_mul_isUnit {a b : α} (h : IsUnit a) : Prime (b * a) ↔ Prime b :=
  let ⟨a, ha⟩ := h
  ha ▸ prime_mul_units a b

theorem prime_neg_iff {α} [CommRing α] {a : α} : Prime (-a) ↔ Prime a := by
  rw [← prime_isUnit_mul isUnit_one.neg, neg_mul, one_mul, neg_neg]

end

lemma zeta_sub_one_dvd_Int_iff {n : ℤ} : (hζ.unit' : 𝓞 K) - 1 ∣ n ↔ ↑p ∣ n := by
  clear hp
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  by_cases hp : p = 2
  · rw [← neg_dvd (a := (p : ℤ))]
    rw [← norm_Int_zeta_sub_one' hζ hp, norm_dvd_iff]
    rw [norm_Int_zeta_sub_one' hζ hp, prime_neg_iff, ← Nat.prime_iff_prime_int]
    exact hpri.out
  rw [← norm_Int_zeta_sub_one hζ hp, norm_dvd_iff]
  rw [norm_Int_zeta_sub_one hζ hp, ← Nat.prime_iff_prime_int]
  exact hpri.out

lemma IsPrimitiveRoot.sub_one_dvd_sub {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ p) {η₁ : A} (hη₁ : η₁ ∈ nthRootsFinset p A)
    {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p A) :
    ζ - 1 ∣ η₁ - η₂ := by
  by_cases h : η₁ = η₂
  · rw [h, sub_self]; exact dvd_zero _
  · exact (hζ.associated_sub_one hp hη₁ hη₂ h).dvd

set_option synthInstance.maxHeartbeats 80000 in
lemma quotient_zero_sub_one_comp_aut (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (Ideal.span {(hζ.unit' : 𝓞 K) - 1})).comp σ = Ideal.Quotient.mk _ := by
  have : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  letI : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.unit' - 1: 𝓞 K))) := inferInstance
  apply RingHom.toIntAlgHom_injective
  apply hζ.integralPowerBasis'.algHom_ext
  rw [show hζ.integralPowerBasis'.gen = hζ.unit' from Subtype.ext (by simp)]
  simp only [RingHom.toIntAlgHom, RingHom.toMonoidHom_eq_coe, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  apply hζ.unit'_coe.sub_one_dvd_sub hpri.out
  · rw [mem_nthRootsFinset p.pos, ← map_pow, hζ.unit'_coe.pow_eq_one, map_one]
  · rw [mem_nthRootsFinset p.pos, hζ.unit'_coe.pow_eq_one]

set_option synthInstance.maxHeartbeats 80000 in
lemma zeta_sub_one_dvd_trace_sub_smul (x : 𝓞 K) :
    (hζ.unit' - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1 : ℕ) • x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  letI := IsCyclotomicExtension.isGalois p ℚ K
  have : (Algebra.trace ℤ _ x : 𝓞 K) = ∑ σ : K ≃ₐ[ℚ] K, (intGal σ).toRingHom x := by
    apply (show Function.Injective (algebraMap (𝓞 K) K) from Subtype.val_injective)
    rw [← eq_intCast (algebraMap ℤ (𝓞 K)), ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ ℚ K, eq_intCast, Algebra.coe_trace_int,
      trace_eq_sum_automorphisms, map_sum]
    rfl
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, this,
    map_sum]
  simp_rw [← RingHom.comp_apply, quotient_zero_sub_one_comp_aut]
  rw [Finset.sum_const, map_nsmul, sub_eq_zero, Finset.card_univ, IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat p.pos), Nat.totient_prime hpri.out]

lemma zeta_sub_one_pow_dvd_norm_sub_pow (x : 𝓞 K) :
    (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣
      (Algebra.norm ℤ (1 + (p : ℕ) • x) : 𝓞 K) - 1 + (p : ℕ) • x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
  obtain ⟨s, hs⟩ := zeta_sub_one_dvd_trace_sub_smul hζ x
  obtain ⟨t, ht⟩ := (associated_zeta_sub_one_pow_prime hζ).dvd
  rw [sub_eq_iff_eq_add] at hs
  simp only [zsmul_eq_mul, Int.cast_natCast] at hr
  simp only [nsmul_eq_mul, hr, Int.cast_add, Int.cast_one, Int.cast_mul, hs, ge_iff_le, PNat.pos,
    Nat.cast_pred, Int.cast_pow, Nat.cast_mul, ne_eq, PNat.ne_zero, Int.cast_natCast,
    not_false_eq_true, isUnit_pow_iff]
  suffices (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (hζ.unit' - 1) * p * s + (p : 𝓞 K) ^ 2 * (r + x) by
    convert this using 1; ring
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rw [ht, ← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
    exact dvd_mul_right _ _
  · rw [ht, mul_pow, ← pow_mul, mul_assoc]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    zify [(Nat.Prime.one_lt hpri.out).le]
    linarith only [Nat.Prime.two_le hpri.out]

lemma norm_add_one_smul_of_isUnit {K} [Field K] [NumberField K] {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (x : 𝓞 K)
    (hx : IsUnit (1 + (p : ℕ) • x)) : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 := by
  have H : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 ∨ Algebra.norm ℤ (1 + (p : ℕ) • x) = -1 := by
    apply Int.natAbs_eq_iff.mp
    apply (Int.cast_injective (α := ℚ)).comp Nat.cast_injective
    simp only [Int.cast_abs, Function.comp_apply, Nat.cast_one, Int.cast_one, ← Int.abs_eq_natAbs,
      Algebra.coe_norm_int, ← NumberField.isUnit_iff_norm.mp hx, RingOfIntegers.coe_norm]
  have : Algebra.norm ℤ (1 + (p : ℕ) • x) ≠ -1 := by
    intro e; apply hp
    obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
    have : (p : ℤ) * (- Algebra.trace ℤ _ x - r * p) = 2 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ← nsmul_eq_mul, e, eq_comm, ← sub_eq_zero] at hr
      rw [eq_comm, ← sub_eq_zero, ← hr]
      ring
    exact (Nat.prime_two.eq_one_or_self_of_dvd _
      (Int.natCast_dvd_natCast.mp ⟨_, this.symm⟩)).resolve_left hpri.ne_one
  exact H.resolve_right this
