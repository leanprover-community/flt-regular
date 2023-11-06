import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.RingTheory.Ideal.Norm

variable {K : Type _} [Field K] {ζ : K}

open scoped NumberField

instance : Module (𝓞 K) (𝓞 K) := Semiring.toModule

open scoped NumberField

open Polynomial Algebra

namespace IsCyclotomicExtension.Rat

variable {p : ℕ+} {k : ℕ} [hp : Fact (p : ℕ).Prime] [CharZero K]

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220

theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (p ^ _).pos)
    (Subalgebra.one_mem _)⟩ : 𝓞 K) := by
  letI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · rw [← Subalgebra.coe_eq_zero, sub_eq_zero] at h
    exact hζ.pow_ne_one_of_pos_of_lt zero_lt_one (one_lt_pow hp.out.one_lt (by simp)) (by simp [h])
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), Subalgebra.algebraMap_eq]
  simp only [PNat.pow_coe, id.map_eq_id, RingHomCompTriple.comp_eq, RingHom.coe_coe,
    Subalgebra.coe_val, algebraMap_int_eq, map_natCast]
  refine hζ.sub_one_norm_prime_ne_two (Polynomial.cyclotomic.irreducible_rat ?_) hodd
  simp

theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p)
    (hodd : p ≠ 2) :
    Prime (⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral p.pos) (Subalgebra.one_mem _)⟩ : 𝓞 K) := by
  convert @zeta_sub_one_prime K _ _ p 0 _ _ (by convert h; rw [zero_add, pow_one]) _ hodd
  simpa

end IsCyclotomicExtension.Rat
