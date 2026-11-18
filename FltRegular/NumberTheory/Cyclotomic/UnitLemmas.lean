module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

/-!
# Units in cyclotomic fields

This file records how complex conjugation acts on cyclotomic units and proves that the quotient
of a unit by its conjugate is a square of a root of unity.
-/

@[expose] public section

variable {p : ℕ} [NeZero p] {K : Type*} [Field K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open scoped nonZeroDivisors NumberField

open IsCyclotomicExtension NumberField Polynomial IsCMField

noncomputable section

local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

set_option quotPrecheck false
local notation "I" => (Ideal.span ({(η - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))

theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mem_span_singleton_self _)

variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]

include hζ in
/-- Complex conjugation sends a primitive `p`-th root of unity to its inverse. -/
theorem complexConj_zeta (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    complexConj K ζ = ζ⁻¹ :=
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  complexConj_torsion (K := K) ⟨η, (CommGroup.mem_torsion _).2 <|
    isOfFinOrder_iff_pow_eq_one.2 ⟨p, NeZero.pos p, Units.ext (Subtype.ext hζ.pow_eq_one)⟩⟩

lemma unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ I) (unitsMulComplexConjInv K u).1 = 1 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hmap := Units.coe_map_inv (N := 𝓞 K ⧸ I) (algebraMap (𝓞 K) (𝓞 K ⧸ I))
    (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul, ← MonoidHom.coe_ofClass, ← hmap,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_ofClass]
  exact (RingHom.congr_fun (quotient_zero_sub_one_comp_aut hζ
    (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) (u : 𝓞 K)).symm

theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -η ^ n := fun H ↦ by
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = 1 := by
    rw [map_pow, eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    exact unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  apply (IsCyclotomicExtension.Rat.two_notMem_span_zeta_sub_one' _ hζ hp : (2 : 𝓞 K) ∉ I)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two,
    ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ

theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (η ^ m) ^ 2 := by
  let _ := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  have hroot : IsOfFinOrder (u * (unitsComplexConj K u)⁻¹ : K) :=
    ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).isOfFinOrder
      ((CommGroup.mem_torsion _).mp (unitsMulComplexConjInv K u).property)
  have hη : (η : K) = ζ := by rw [IsUnit.unit_spec]; rfl
  obtain ⟨n, -, hz | hz⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo hroot
  · rw [show u * (unitsComplexConj K u)⁻¹ = η ^ n from NumberField.Units.coe_injective K
      (by simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow, hη] using hz)]
    simpa only [pow_mul, mul_comm] using
      (hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n
  · exact (unit_inv_conj_not_neg_zeta_runity hζ u n hp <| NumberField.Units.coe_injective K
      (by simpa only [NumberField.Units.coe_mul, NumberField.Units.coe_pow,
        Units.val_neg, map_neg, hη] using hz)).elim
