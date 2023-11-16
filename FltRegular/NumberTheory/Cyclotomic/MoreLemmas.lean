import Mathlib.NumberTheory.Cyclotomic.Rat
import FltRegular.NumberTheory.Cyclotomic.Factoring
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.Cyclotomic.CyclRat
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.ClassGroup

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
  exact IsCyclotomicExtension.Rat.zeta_sub_one_prime' hζ hp
  · rw [Ne.def, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt

lemma norm_Int_zeta_sub_one : Algebra.norm ℤ (↑(IsPrimitiveRoot.unit' hζ) - 1 : 𝓞 K) = p := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  haveI : Fact (Nat.Prime p) := hpri
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  simp [Algebra.coe_norm_int, hζ.sub_one_norm_prime (cyclotomic.irreducible_rat p.2) hp]

lemma one_mem_nthRootsFinset {R : Type*} {n : ℕ} [CommRing R] [IsDomain R] (hn : 0 < n) :
    1 ∈ nthRootsFinset n R := by rw [mem_nthRootsFinset hn, one_pow]

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
    (hζ.prime_span_sub_one hp).irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton,
    Ideal.mem_span_singleton]
  · simpa only [ge_iff_le, tsub_pos_iff_lt] using hpri.out.one_lt

lemma exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) : ∃ b : ℤ, (hζ.unit' - 1: 𝓞 K) ∣ a - b := by
  letI : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.unit' - 1: 𝓞 K))) := inferInstance
  letI : Fact (Nat.Prime p) := hpri
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, sub_eq_zero, ← SModEq.Ideal_def]
  convert exists_int_sModEq hζ.subOneIntegralPowerBasis' a
  rw [hζ.subOneIntegralPowerBasis'_gen]
  rw [Subtype.ext_iff, AddSubgroupClass.coe_sub, IsPrimitiveRoot.val_unit'_coe, OneMemClass.coe_one]

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

lemma norm_dvd_iff {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Infinite R] [Module.Free ℤ R] [Module.Finite ℤ R] (x : R) (hx : Prime (Algebra.norm ℤ x)) {y : ℤ} :
    Algebra.norm ℤ x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x), ← eq_intCast (algebraMap ℤ R), ← Ideal.mem_comap,
    ← Ideal.span_singleton_absNorm, Ideal.mem_span_singleton, Ideal.absNorm_span_singleton,
    Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

lemma zeta_sub_one_dvd_Int_iff {n : ℤ} : (hζ.unit' : 𝓞 K) - 1 ∣ n ↔ ↑p ∣ n := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [← norm_Int_zeta_sub_one hζ hp, norm_dvd_iff]
  rw [norm_Int_zeta_sub_one hζ hp, ← Nat.prime_iff_prime_int]
  exact hpri.out

lemma RingHom.toIntAlgHom_injective {R₁ R₂} [Ring R₁] [Ring R₂] [Algebra ℤ R₁] [Algebra ℤ R₂] :
    Function.Injective (RingHom.toIntAlgHom : (R₁ →+* R₂) → _) :=
  fun _ _ e ↦ FunLike.ext _ _ (fun x ↦ FunLike.congr_fun e x)

lemma IsPrimitiveRoot.sub_one_dvd_sub {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ p) {η₁ : A} (hη₁ : η₁ ∈ nthRootsFinset p A)
    {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p A) :
    ζ - 1 ∣ η₁ - η₂ := by
  by_cases η₁ = η₂
  · rw [h, sub_self]; exact dvd_zero _
  · exact (hζ.associated_sub_one hp hη₁ hη₂ h).dvd

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


open Polynomial in
lemma Matrix.eval_det_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (A) (M : Matrix n n R) :
    (det (A + (X : R[X]) • M.map C)).eval 0 = (det A).eval 0 := by
  simp only [eval_det, map_zero, map_add, eval_add, Algebra.smul_def, _root_.map_mul]
  simp only [algebraMap_eq_smul, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X, mul_zero,
    add_zero]

lemma Matrix.trace_submatrix_succ {n : ℕ} {R} [CommRing R] (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M := by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

open Polynomial in
lemma Matrix.derivative_det_one_add_X_smul_aux {n} {R} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero, map_sum, eval_finset_sum]
    simp only [add_apply, smul_apply, map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0, eval_zero, mul_zero]
        intro j
        rw [submatrix_apply, Fin.succAbove_below, one_apply_ne]
        · exact (bne_iff_ne (Fin.succ j) (Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

open Polynomial in
lemma Matrix.derivative_det_one_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (M : Matrix n n R) : (derivative <| det (1 + (X : R[X]) • M.map C)).eval 0 = trace M := by
  let e := Matrix.reindexLinearEquiv R R (Fintype.equivFin n) (Fintype.equivFin n)
  rw [← Matrix.det_reindexLinearEquiv_self R[X] (Fintype.equivFin n)]
  convert derivative_det_one_add_X_smul_aux (e M)
  · ext; simp
  · delta trace
    rw [← (Fintype.equivFin n).symm.sum_comp]
    rfl

open Polynomial in
lemma Matrix.det_one_add_X_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R]
    (M : Matrix n n R) : det (1 + (X : R[X]) • M.map C) =
      (1 : R[X]) + trace M • X + (det (1 + (X : R[X]) • M.map C)).divX.divX * X ^ 2 := by
  rw [Algebra.smul_def (trace M), ← C_eq_algebraMap, pow_two, ← mul_assoc, add_assoc,
    ← add_mul, ← derivative_det_one_add_X_smul, ← coeff_zero_eq_eval_zero, coeff_derivative,
    Nat.cast_zero, @zero_add R, mul_one, ← coeff_divX, add_comm (C _), divX_mul_X_add,
    add_comm (1 : R[X]), ← C.map_one]
  convert (divX_mul_X_add _).symm
  rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]

open Polynomial in
lemma Matrix.det_one_add_smul {n} [Fintype n] [DecidableEq n] {R} [CommRing R] (r : R)
    (M : Matrix n n R) : det (1 + r • M) =
      1 + trace M * r + (det (1 + (X : R[X]) • M.map C)).divX.divX.eval r * r ^ 2 := by
  have := congr_arg (eval r) (Matrix.det_one_add_X_smul M)
  simp only [eval_det, coe_scalar, map_add, _root_.map_one, eval_add, eval_one, eval_smul, eval_X,
    smul_eq_mul, eval_mul, eval_pow] at this
  convert this
  rw [Algebra.smul_def X, _root_.map_mul]
  have : matPolyEquiv (M.map C) = C M
  · ext; simp only [matPolyEquiv_coeff_apply, map_apply, coeff_C]; rw [ite_apply, ite_apply]; rfl
  simp only [algebraMap_eq_smul, matPolyEquiv_smul_one, map_X, X_mul, eval_mul_X, this,
    Algebra.mul_smul_comm, mul_one, eval_C]

lemma Algebra.norm_one_add_smul {A B} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B] (a : A) (x : B) :
    ∃ r : A, Algebra.norm A (1 + a • x) = 1 + Algebra.trace A B x * a + r * a ^ 2 := by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  haveI : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_smul a]
  exact ⟨_, rfl⟩

theorem Algebra.coe_trace_int {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    Algebra.trace ℤ _ x = Algebra.trace ℚ K x :=
  (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

lemma zeta_sub_one_dvd_trace_sub_smul (x : 𝓞 K) :
    (hζ.unit' - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1 : ℕ) • x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  letI := IsCyclotomicExtension.isGalois p ℚ K
  have : (Algebra.trace ℤ _ x : 𝓞 K) = ∑ σ : K ≃ₐ[ℚ] K, (intGal σ).toRingHom x
  · apply (show Function.Injective (algebraMap (𝓞 K) K) from Subtype.val_injective)
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
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hr
  simp only [nsmul_eq_mul, hr, Int.cast_add, Int.cast_one, Int.cast_mul, hs, ge_iff_le, PNat.pos,
    Nat.cast_pred, Int.cast_ofNat, Int.cast_pow, Nat.cast_mul, ne_eq, PNat.ne_zero,
    not_false_eq_true, isUnit_pow_iff]
  suffices : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (hζ.unit' - 1) * p * s + (p : 𝓞 K) ^ 2 * (r + x)
  · convert this using 1; ring
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rw [ht, ← mul_assoc, ← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
    exact dvd_mul_right _ _
  · rw [ht, mul_pow, ← pow_mul, mul_assoc]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    zify [(Nat.Prime.one_lt hpri.out).le]
    linarith only [Nat.Prime.two_le hpri.out]

lemma norm_add_one_smul_of_isUnit {K} [Field K] [NumberField K] {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (x : 𝓞 K)
    (hx : IsUnit (1 + (p : ℕ) • x)) : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 := by
  have H : Algebra.norm ℤ (1 + (p : ℕ) • x) = 1 ∨ Algebra.norm ℤ (1 + (p : ℕ) • x) = -1
  · apply Int.natAbs_eq_iff.mp
    apply (Int.cast_injective (α := ℚ)).comp Nat.cast_injective
    simp only [Int.cast_abs, Function.comp_apply, Nat.cast_one, Int.cast_one, ← Int.abs_eq_natAbs,
      Algebra.coe_norm_int, ← NumberField.isUnit_iff_norm.mp hx, RingOfIntegers.norm_apply_coe]
  have : Algebra.norm ℤ (1 + (p : ℕ) • x) ≠ -1
  · intro e; apply hp
    obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
    have : (p : ℤ) * (- Algebra.trace ℤ _ x - r * p) = 2
    · rw [zsmul_eq_mul, Int.cast_ofNat, ← nsmul_eq_mul, e, eq_comm, ← sub_eq_zero] at hr
      rw [eq_comm, ← sub_eq_zero, ← hr]
      ring
    exact (Nat.prime_two.eq_one_or_self_of_dvd _
      (Int.coe_nat_dvd.mp ⟨_, this.symm⟩)).resolve_left hpri.ne_one
  exact H.resolve_right this
