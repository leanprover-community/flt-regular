import FltRegular.Norm.NormPrime
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Rat

variable {K : Type _} [Field K] {ζ : K}

open scoped NumberField

open Polynomial Algebra

local notation "R" => 𝓞 K

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} [hp : Fact (p : ℕ).Prime] [CharZero K]

theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.IsIntegral (p ^ _).Pos) (Subalgebra.one_mem _)⟩ : R) :=
  by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  letI := IsCyclotomicExtension.isGalois (p ^ (k + 1)) ℚ K
  rw [← hζ.sub_one_integral_power_basis_gen]
  refine' prime_of_norm_prime _
  rw [hζ.sub_one_integral_power_basis_gen]
  simp only [RingOfIntegers.norm, MonoidHom.restrict_apply, SetLike.coe_mk,
    MonoidHom.codRestrict_apply,
    hζ.sub_one_norm_prime_ne_two (cyclotomic.irreducible_rat (p ^ (k + 1)).Pos) hodd]
  rw [MulEquiv.prime_iff rat.ring_of_integers_equiv.to_mul_equiv]
  simp only [coe_coe, RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv]
  convert Nat.prime_iff_prime_int.1 hp.1
  refine' EquivLike.injective rat.ring_of_integers_equiv.symm (Subtype.ext _)
  simp only [SetLike.coe_mk, RingEquiv.symm_apply_apply]
  norm_cast
  simp [← RingEquiv.coe_toRingHom]

theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p)
    (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.IsIntegral p.Pos) (Subalgebra.one_mem _)⟩ : R) :=
  by
  convert @zeta_sub_one_prime K _ _ p 0 _ _ (by convert h; rw [zero_add, pow_one]) _ hodd
  simpa

end IsCyclotomicExtension.Rat

