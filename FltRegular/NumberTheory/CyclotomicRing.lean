import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

noncomputable section

open Polynomial NumberField

variable (p : ℕ) [hpri : Fact p.Prime]

def CyclotomicIntegers : Type := AdjoinRoot (cyclotomic p ℤ)

instance : CommRing (CyclotomicIntegers p) := by delta CyclotomicIntegers; infer_instance

open Polynomial in
lemma IsPrimitiveRoot.cyclotomic_eq_minpoly
    (x : 𝓞 (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ)) (hx : IsPrimitiveRoot x.1 p) :
      minpoly ℤ x = cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ),
    ← cyclotomic_eq_minpoly_rat (n := p), map_cyclotomic]
  · exact hx
  · exact hpri.out.pos
  · exact IsIntegralClosure.isIntegral _ (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ) _

def AdjoinRoot.aeval_root {R} [CommRing R] (P : R[X]) : aeval (root P) P = 0 := by simp

@[simps!]
def AdjoinRoot.equivOfMinpolyEq {R S} [CommRing R] [CommRing S] [Algebra R S]
    (P : R[X]) (pb : PowerBasis R S) (hpb : minpoly R pb.gen = P) :
    AdjoinRoot P ≃ₐ[R] S := AdjoinRoot.equiv' P pb (hpb ▸ aeval_root _) (hpb ▸ minpoly.aeval _ _)

theorem map_dvd_iff {M N} [Monoid M] [Monoid N] {F : Type*} [MulEquivClass F M N] (f : F) {a b} :
    f a ∣ f b ↔ a ∣ b := by
  refine ⟨?_, map_dvd f⟩
  convert _root_.map_dvd (f : M ≃* N).symm <;> exact ((f : M ≃* N).symm_apply_apply _).symm

namespace CyclotomicIntegers

@[simps! (config := .lemmasOnly)]
def equiv :
    CyclotomicIntegers p ≃+* 𝓞 (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ) := by
  letI p' : ℕ+ := ⟨p, hpri.out.pos⟩
  letI : Fact (Nat.Prime p') := hpri
  letI H := IsCyclotomicExtension.zeta_spec p' ℚ (CyclotomicField p' ℚ)
  exact (AdjoinRoot.equivOfMinpolyEq (cyclotomic p ℤ) H.integralPowerBasis'
    (H.integralPowerBasis'_gen ▸ IsPrimitiveRoot.cyclotomic_eq_minpoly p H.toInteger H)).toRingEquiv

instance : IsDomain (CyclotomicIntegers p) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (cyclotomic.irreducible hpri.out.pos))

def zeta : CyclotomicIntegers p := AdjoinRoot.root _

lemma equiv_zeta : equiv p (zeta p) = (IsCyclotomicExtension.zeta_spec
    ⟨p, hpri.out.pos⟩ ℚ (CyclotomicField ⟨p, hpri.out.pos⟩ ℚ)).toInteger := by
  letI p' : ℕ+ := ⟨p, hpri.out.pos⟩
  letI : Fact (Nat.Prime p') := hpri
  rw [equiv_apply, zeta]
  simp only [AdjoinRoot.liftHom_root, IsPrimitiveRoot.integralPowerBasis'_gen]

lemma prime_one_sub_zeta :
    Prime (1 - zeta p) := by
  rw [← prime_units_mul (a := -1), Units.val_neg, Units.val_one, neg_mul, one_mul, neg_sub]
  apply (equiv p).toMulEquiv.prime_iff.mpr
  simp only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv,
    (equiv p).map_sub, (equiv p).map_one, equiv_zeta]
  letI p' : ℕ+ := ⟨p, hpri.out.pos⟩
  letI : Fact (Nat.Prime p') := hpri
  letI H := IsCyclotomicExtension.zeta_spec p' ℚ (CyclotomicField p' ℚ)
  exact H.zeta_sub_one_prime'

lemma one_sub_zeta_mem_nonZeroDivisors :
    1 - zeta p ∈ nonZeroDivisors (CyclotomicIntegers p) := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact (prime_one_sub_zeta p).1

lemma not_isUnit_one_sub_zeta :
    ¬ IsUnit (1 - zeta p) := (prime_one_sub_zeta p).irreducible.1

lemma one_sub_zeta_dvd_int_iff (n : ℤ) : 1 - zeta p ∣ n ↔ ↑p ∣ n := by
  letI p' : ℕ+ := ⟨p, hpri.out.pos⟩
  letI : Fact (PNat.Prime p') := hpri
  letI H := IsCyclotomicExtension.zeta_spec p' ℚ (CyclotomicField p' ℚ)
  rw [← map_dvd_iff (equiv p), map_sub, map_one, equiv_zeta, map_intCast,
    ← neg_dvd, neg_sub]
  exact zeta_sub_one_dvd_Int_iff H

lemma one_sub_zeta_dvd : 1 - zeta p ∣ p := by
  show 1 - zeta p ∣ (p : ℤ)
  rw [one_sub_zeta_dvd_int_iff]

lemma isCoprime_one_sub_zeta (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : IsCoprime (1 - zeta p) n := by
  apply (((Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd.mpr hn).map
    (algebraMap ℤ <| CyclotomicIntegers p)).of_isCoprime_of_dvd_left
  exact one_sub_zeta_dvd p

lemma exists_dvd_int (n : CyclotomicIntegers p) (hn : n ≠ 0) : ∃ m : ℤ, m ≠ 0 ∧ n ∣ m := by
  refine ⟨Algebra.norm ℤ ((equiv p) n), by simpa, ?_⟩
  rw [← map_dvd_iff (equiv p), map_intCast]
  convert RingOfIntegers.dvd_norm ℚ (equiv p n) using 1
  ext1
  exact FunLike.congr_arg (algebraMap ℚ _) (Algebra.coe_norm_int (equiv p n))

lemma adjoin_zeta : Algebra.adjoin ℤ {zeta p} = ⊤ := AdjoinRoot.adjoinRoot_eq_top

open BigOperators

lemma sum_zeta_pow : ∑ i in Finset.range p, zeta p ^ (i : ℕ) = 0 := by
  rw [← AdjoinRoot.aeval_root (Polynomial.cyclotomic p ℤ), ← zeta]
  simp [Polynomial.cyclotomic_prime ℤ p]

lemma zeta_pow_sub_one :
    zeta p ^ (p - 1 : ℕ) = - ∑ i : Fin (p - 1), zeta p ^ (i : ℕ) := by
  rw [eq_neg_iff_add_eq_zero]
  convert CyclotomicIntegers.sum_zeta_pow p
  conv_rhs => enter [1]; rw [← tsub_add_cancel_of_le hpri.out.one_lt.le]
  rw [Finset.sum_range_succ, add_comm, Fin.sum_univ_eq_sum_range]

end CyclotomicIntegers
end
