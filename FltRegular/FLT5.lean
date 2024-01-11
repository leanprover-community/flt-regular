import Mathlib
import FltRegular

open Nat NumberField Polynomial IsPrimitiveRoot IsCyclotomicExtension
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
      simp [← finrank K (cyclotomic.irreducible_rat p.2), ← PowerBasis.finrank]
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp only [powerBasis_dim, finCongr_symm, Function.comp_apply,
      Basis.localizationLocalization_apply, PowerBasis.coe_basis, integralPowerBasis'_gen, map_pow]
    convert ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · sorry --boring


set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by
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
    · rw [this, show ((5 : ℕ+) : ℕ) = 5 by rfl, hφ, show ((4! : ℕ) : ℝ) = 24 by rfl]
      norm_num
      sorry
  sorry
