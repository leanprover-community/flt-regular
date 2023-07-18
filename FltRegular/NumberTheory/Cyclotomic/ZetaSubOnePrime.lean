import FltRegular.Norm.NormPrime
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Rat

variable {K : Type _} [Field K] {ζ : K}

open scoped NumberField

open Polynomial Algebra

local notation "R" => 𝓞 K

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} [hp : Fact (p : ℕ).Prime] [CharZero K]

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220

theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (p ^ _).pos)
    (Subalgebra.one_mem _)⟩ : R) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  letI := IsCyclotomicExtension.isGalois (p ^ (k + 1)) ℚ K
  rw [← hζ.subOneIntegralPowerBasis_gen]
  refine' prime_of_norm_prime _
  rw [hζ.subOneIntegralPowerBasis_gen]
  simp only [RingOfIntegers.norm, MonoidHom.restrict_apply, MonoidHom.codRestrict_apply,
    hζ.sub_one_norm_prime_ne_two (cyclotomic.irreducible_rat (p ^ (k + 1)).pos) hodd]
  rw [MulEquiv.prime_iff Rat.ringOfIntegersEquiv.toMulEquiv]
  simp only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv]
  convert Nat.prime_iff_prime_int.1 hp.1
  refine' EquivLike.injective Rat.ringOfIntegersEquiv.symm (Subtype.ext _)
  simp only [RingEquiv.symm_apply_apply]
  norm_cast
  simp [← RingEquiv.coe_toRingHom]

theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p)
    (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral p.pos) (Subalgebra.one_mem _)⟩ : R) := by
  convert @zeta_sub_one_prime K _ _ p 0 _ _ (by convert h; rw [zero_add, pow_one]) _ hodd
  simpa

end IsCyclotomicExtension.Rat
