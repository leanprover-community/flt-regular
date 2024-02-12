import Mathlib
import FltRegular

open NumberField InfinitePlace Polynomial IsPrimitiveRoot Real Complex FiniteDimensional in
theorem classNumber_eq_one_of_abs_discr_lt
    {K} [Field K] [NumberField K]
    (h : |discr K| < (2 * (π / 4) ^ NrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K).factorial)) ^ 2) :
    classNumber K = 1 := by
  have := RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt h
  exact classNumber_eq_one_iff.mpr this

open Nat NumberField Polynomial IsPrimitiveRoot IsCyclotomicExtension Real Complex
open scoped nonZeroDivisors

example (n m : ℕ) (h : n = m) : Fin n ≃ Fin m := by
  exact finCongr h

theorem absdiscr_odd_prime {p : ℕ+} {K : Type u} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [hp : Fact (p : ℕ).Prime] (hodd : p ≠ 2) :
    discr K = (-1) ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  have hζ := (IsCyclotomicExtension.zeta_spec p ℚ K)
  let pB₁ := integralPowerBasis' (IsCyclotomicExtension.zeta_spec p ℚ K)
  apply (algebraMap ℤ ℚ).injective_int
  rw [← discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  convert IsCyclotomicExtension.discr_odd_prime hζ (cyclotomic.irreducible_rat p.2) hodd using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis ℚ hζ).dim := by
      simp only [power_basis_int'_dim, ← finrank K (cyclotomic.irreducible_rat p.2), ←
        PowerBasis.finrank]
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis,integralPowerBasis'_gen]
    convert ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
  classical
  have five_pos : 0 < 5 := by norm_num
  let p := (⟨5, five_pos⟩ : ℕ+)
  have hφ : φ 5 = 4 := rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hodd : 5 ≠ 2 := by omega
  have hp : Fact (Nat.Prime (↑p : ℕ)) := this
  let K := CyclotomicField p ℚ

  refine flt_regular ?_ hodd
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  apply classNumber_eq_one_of_abs_discr_lt
  rw [IsCyclotomicExtension.finrank (n := 5) K (cyclotomic.irreducible_rat five_pos),
    absdiscr_odd_prime (hp := hp) (Subtype.ne_of_val_ne hodd)]
  suffices InfinitePlace.NrComplexPlaces K = 2 by
    · rw [this, show ((5 : ℕ+) : ℕ) = 5 by rfl, hφ, show ((4! : ℕ) : ℝ) = 24 by rfl,
        abs_of_pos (by norm_num)]
      norm_num
      suffices (2 * (3 ^ 2 / 16) * (32 / 3)) ^ 2 < (2 * ((π : ℝ) ^ 2 / 16) * (32 / 3)) ^ 2 by
        · refine lt_trans ?_ this
          norm_num
      gcongr
      exact pi_gt_three
  have key := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsCyclotomicExtension.finrank (n := 5) K (cyclotomic.irreducible_rat five_pos),
    show ((5 : ℕ+) : ℕ) = 5 by rfl, hφ] at key
  suffices InfinitePlace.NrRealPlaces K = 0 by
    · rw [this, zero_add, show 4 = 2 * 2 by rfl] at key
      simpa only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] using key
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨w, hwreal⟩
  let f := w.embedding
  rw [InfinitePlace.isReal_iff] at hwreal
  let ζ := IsCyclotomicExtension.zeta 5 ℚ K
  have hζ := (IsCyclotomicExtension.zeta_spec 5 ℚ K)
  have hζ' : IsPrimitiveRoot (f ζ) 5 := hζ.map_of_injective (RingHom.injective f)
  have him : (f ζ).im = 0 := by
    · rw [← conj_eq_iff_im, ← ComplexEmbedding.conjugate_coe_eq]
      congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    · rw [← abs_re_eq_abs] at him
      have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by norm_num)
      rw [Complex.norm_eq_abs, ← him] at this
      by_cases hpos : 0 ≤ (f ζ).re
      · rw [_root_.abs_of_nonneg hpos] at this
        left
        exact this
      · rw [_root_.abs_of_neg (not_le.1 hpos)] at this
        right
        rw [← this]
        simp
  cases hre with
  | inl hone =>
    apply hζ'.ne_one (by norm_num)
    apply Complex.ext
    · simp [hone]
    · simp [him]
  | inr hnegone =>
  replace hζ' := hζ'.pow_eq_one
  rw [← re_add_im (f ζ), him, hnegone] at hζ'
  simp only [ofReal_neg, ofReal_one, ofReal_zero, zero_mul, add_zero] at hζ'
  norm_num at hζ'
