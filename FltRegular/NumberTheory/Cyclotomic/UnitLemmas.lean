module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

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
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A), ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

set_option backward.isDefEq.respectTransparency false in
theorem aux {t} {l : 𝓞 K} {f : Fin t → ℤ} {μ : K} (hμ : IsPrimitiveRoot μ p)
    (h : ∑ x : Fin t, f x • (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ (x : ℕ) = l) :
    algebraMap (𝓞 K) (𝓞 K ⧸ I) l = ∑ x : Fin t, (f x : 𝓞 K ⧸ I) := by
  apply_fun algebraMap (𝓞 K) (𝓞 K ⧸ I) at h
  simp only [map_sum, map_zsmul] at h
  convert h.symm using 1
  congr
  funext x
  have : (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ p = 1 := by
    ext
    push_cast
    exact hμ.pow_eq_one
  obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one this
  have : algebraMap (𝓞 K) (𝓞 K ⧸ I) (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) = 1 := by
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ I) (η : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  simp only [map_pow (algebraMap (𝓞 K) (𝓞 K ⧸ I)), this, one_pow, zsmul_one]

variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem roots_of_unity_in_cyclo (hpo : Odd p) (x : K)
    (h : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1) :
    ∃ (m k : ℕ), x = (-1) ^ k * (η.1 : K) ^ m := by
  obtain ⟨n, hn, hxn⟩ := h
  have hη : (η.1 : K) = ζ := by rw [IsUnit.unit_spec]; rfl
  simp only [hη]
  obtain ⟨r, -, hr | hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxn⟩)
  · exact ⟨r, 2, by simp [hr]⟩
  · exact ⟨r, 1, by simp [hr]⟩


lemma unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ I) (unitsMulComplexConjInv K u).1 = 1 := by
  haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have := Units.coe_map_inv (N := 𝓞 K ⧸ I) (algebraMap (𝓞 K) (𝓞 K ⧸ I)) (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul, ← MonoidHom.coe_coe, ← this,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_coe]
  haveI := Fact.mk hp
  have hu := hζ.integralPowerBasis.basis.sum_repr u
  let a := hζ.integralPowerBasis.basis.repr
  let φn := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow, IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have hu' := congr_arg (ringOfIntegersComplexConj K) hu
  replace hu' : ∑ x : Fin φn, (a u) x • (ringOfIntegersComplexConj K)
      (hζ.toInteger ^ (x : ℕ)) = unitsComplexConj K u := by
    refine Eq.trans ?_ hu'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have : ∀ x : Fin φn, ringOfIntegersComplexConj K (hζ.toInteger ^ (x : ℕ)) =
      hζ.inv.toInteger ^ (x : ℕ) := by
    intro x
    ext
    simp only [map_pow, coe_ringOfIntegersComplexConj]
    suffices η ∈ Units.torsion K by
      have H := RingOfIntegers.ext_iff.1 <|
        Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨η, ‹_›⟩
      have : ↑↑η = ζ := rfl
      simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingOfIntegers.mapRingEquiv_apply,
        this, AlgEquiv.coe_ringEquiv, InvMemClass.coe_inv, map_units_inv] at H
      change (complexConj K) ζ ^ (x : ℕ) = ζ⁻¹ ^ (x : ℕ)
      rw [H]
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, by lia, ?_⟩)
    ext
    exact hζ.pow_eq_one
  conv_lhs at hu' =>
    congr
    congr
    ext a
    rw [this a]
  exact (aux hζ hζ hu).trans (aux hζ hζ.inv hu').symm

theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -η ^ n := by
  by_contra H
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = 1 := by
    have hpow : ((η : 𝓞 K) ^ n) ^ p = 1 := by
      change (hζ.toInteger ^ n) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ I) (η : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ I) ((η : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  haveI := Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp : (2 : 𝓞 K) ∉ I)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two, ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ

theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (η ^ m) ^ 2 := by
  haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  haveI : NormedAlgebra ℚ ℂ := normedAlgebraRat
  have :=
    @NumberField.Embeddings.pow_eq_one_of_norm_eq_one K _ _ ℂ _ _ _
      (u * (unitsComplexConj K u)⁻¹ : K) ?_ ?_
  · have H := roots_of_unity_in_cyclo hζ hpo (u * (unitsComplexConj K u)⁻¹ : K) this
    obtain ⟨n, k, hz⟩ := H
    simp_rw [← pow_mul]
    have hk := Nat.even_or_odd k
    rcases hk with hk | hk
    · simp only [hk.neg_one_pow, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val] at hz
      norm_cast at hz
      rw [hz]
      refine (exists_congr fun a => ?_).mp
        ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
      · rw [mul_comm]
    · by_contra
      simp only [hk.neg_one_pow, neg_mul, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_neg] at hz
      norm_cast at hz
      simpa [hz] using unit_inv_conj_not_neg_zeta_runity hζ u n hp
  · apply RingHom.IsIntegralElem.mul
    · exact NumberField.RingOfIntegers.isIntegral_coe _
    · exact NumberField.RingOfIntegers.isIntegral_coe _
  · simp
