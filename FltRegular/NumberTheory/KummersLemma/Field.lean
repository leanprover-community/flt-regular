import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.FieldTheory.KummerExtension
import FltRegular.NumberTheory.Unramified
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas

open scoped NumberField BigOperators

variable {K : Type*} {p : ℕ+} [hpri : Fact p.Prime] [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (hp : p ≠ 2)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 K)ˣ)
  (hcong : (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ (p : ℕ) ≠ u)

open Polynomial

lemma zeta_sub_one_pow_dvd_poly :
    C ((hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ)) ∣
      (C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ (p : ℕ) + C (u : 𝓞 K) := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub (u : 𝓞 K), ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out (PNat.coe_injective.ne hp) _ _ dvd_rfl ?_
  conv_lhs => rw [← tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_succ]
  exact mul_dvd_mul_right (associated_zeta_sub_one_pow_prime hζ).dvd _

namespace KummersLemma

noncomputable def poly : (𝓞 K)[X] := (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose

lemma poly_spec :
    C ((hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ)) * poly hp hζ u hcong =
      (C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ (p : ℕ) + C (u : 𝓞 K) :=
  (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose_spec.symm

lemma natDegree_poly_aux :
    natDegree ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ (p : ℕ) + C (u : 𝓞 K)) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

lemma monic_poly_aux :
    leadingCoeff ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ (p : ℕ) + C (u : 𝓞 K)) =
      (hζ.unit' - 1 : 𝓞 K) ^ (p : ℕ) := by
  haveI : Fact (Nat.Prime p) := hpri
  trans leadingCoeff ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ (p : ℕ))
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux hζ, coeff_C, if_neg p.pos.ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C, ite_true,
      coeff_one, ite_false, sub_zero]
    exact C_ne_zero.mpr (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

lemma monic_poly : Monic (poly hp hζ u hcong) := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg leadingCoeff (poly_spec hp hζ u hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C, ne_eq, PNat.pos,
    pow_eq_zero_iff, monic_poly_aux hζ] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

lemma natDegree_poly : natDegree (poly hp hζ u hcong) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg natDegree (poly_spec hp hζ u hcong)
  rwa [natDegree_C_mul, natDegree_poly_aux hζ] at this
  exact pow_ne_zero _ (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

lemma map_poly : (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ (p : ℕ) + C (u / (ζ - 1) ^ (p : ℕ) : K) := by
  ext i
  have := congr_arg (fun P : (𝓞 K)[X] ↦ (↑(coeff P i) : K)) (poly_spec hp hζ u hcong)
  change _ = algebraMap (𝓞 K) K _ at this
  rw [← coeff_map] at this
  replace this : (ζ - 1) ^ (p : ℕ) * ↑((poly hp hζ u hcong).coeff i) =
    (((C ((algebraMap ((𝓞 K)) K) ↑hζ.unit') - 1) * X - 1) ^ (p : ℕ)).coeff i +
    (C ((algebraMap ((𝓞 K)) K) ↑u)).coeff i := by
      simp only [map_pow, map_sub, map_one, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_sub, Polynomial.map_mul, map_C,
        Polynomial.map_one, map_X, coeff_add] at this
      convert this
      simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, ← Polynomial.coeff_map]
      simp only [coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C,
        Polynomial.map_one]
      rw [← Polynomial.coeff_map, mul_comm, ← Polynomial.coeff_mul_C, mul_comm]
      simp [show hζ.unit'.1 = ζ from rfl]
  apply mul_right_injective₀ (pow_ne_zero p (hζ.sub_one_ne_zero hpri.out.one_lt))
  simp only [Subalgebra.algebraMap_eq, Algebra.id.map_eq_id, RingHomCompTriple.comp_eq, coeff_map,
    RingHom.coe_coe, Subalgebra.coe_val, one_div, map_sub, map_one, coeff_add, coeff_sub,
    PNat.pos, pow_eq_zero_iff, this, mul_add, IsPrimitiveRoot.val_unit'_coe]
  simp_rw [← smul_eq_mul K, ← coeff_smul, show hζ.unit'.1 = ζ from rfl]
  rw [smul_C, smul_eq_mul, ← smul_pow, ← mul_div_assoc, mul_div_cancel_left₀, smul_sub, smul_C,
    smul_eq_mul, mul_inv_cancel, map_one, Algebra.smul_def, ← C_eq_algebraMap, map_sub, map_one]
  · exact hζ.sub_one_ne_zero hpri.out.one_lt
  · exact pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt)

lemma irreducible_map_poly :
    Irreducible ((poly hp hζ u hcong).map (algebraMap (𝓞 K) K)) := by
  rw [map_poly, ← irreducible_taylor_iff (r := 1 / (ζ - 1))]
  simp only [taylor, one_div, map_add, LinearMap.coe_mk, AddHom.coe_mk, pow_comp, sub_comp,
    X_comp, C_comp, add_sub_cancel_right]
  rw [← sub_neg_eq_add, ← (C : K →+* _).map_neg]
  apply X_pow_sub_C_irreducible_of_prime hpri.out
  intro b hb
  apply hu (- b * (ζ - 1))
  rw [mul_pow, (hpri.out.odd_of_ne_two (PNat.coe_injective.ne hp)).neg_pow, hb, neg_neg,
    div_mul_cancel₀ _ (pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt))]

theorem aeval_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (poly hp hζ u hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_spec hp hζ u hcong)
  -- also add to mathlib
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.unit') = algebraMap K L ζ := rfl
  have hcoe1 : (algebraMap (𝓞 K) L) ↑u = algebraMap K L ↑↑u := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, Subalgebra.algebraMap_eq, smul_pow,
    hcoe, RingHom.coe_comp, RingHom.coe_coe, Subalgebra.coe_val, Function.comp_apply, e, hcoe1,
    IsPrimitiveRoot.val_unit'_coe, map_add, aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ',
    sub_sub_cancel_left, (hpri.out.odd_of_ne_two (PNat.coe_injective.ne hp)).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, add_left_neg,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')

def polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
      ⟨poly hp hζ u hcong, monic_poly hp hζ u hcong, aeval_poly hp hζ u hcong α e m⟩⟩

theorem roots_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) :
    roots ((poly hp hζ u hcong).map (algebraMap (𝓞 K) L)) =
      (Finset.range (p : ℕ)).val.map
        (fun i ↦ ((1 : L) - ζ ^ i • α) / (algebraMap K L (ζ - 1))) := by
  by_cases hα : α = 0
  · rw [hα, zero_pow p.ne_zero] at e
    exact (((algebraMap (𝓞 K) L).isUnit_map u.isUnit).ne_zero e.symm).elim
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_poly hp hζ u hcong α e]
      exact ((monic_poly hp hζ u hcong).map (algebraMap (𝓞 K) L)).ne_zero
    · intros i hi j hj e
      apply (hζ.map_of_injective (algebraMap K L).injective).injOn_pow_mul hα hi hj
      apply_fun (1 - · * (algebraMap K L ζ - 1)) at e
      dsimp only at e
      simpa only [Nat.cast_one, map_sub, map_one, Algebra.smul_def, map_pow,
        div_mul_cancel₀ _ hζ', sub_sub_cancel] using e
  · simp only [Finset.range_val, Multiset.card_map, Multiset.card_range]
    refine (Polynomial.card_roots' _).trans ?_
    rw [(monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ]

theorem splits_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) :
    (poly hp hζ u hcong).Splits (algebraMap (𝓞 K) L) := by
  rw [← splits_id_iff_splits, splits_iff_card_roots, roots_poly hp hζ u hcong α e,
    (monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ,
    Finset.range_val, Multiset.card_map, Multiset.card_range]

theorem map_poly_eq_prod {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) :
    (poly hp hζ u hcong).map (algebraMap (𝓞 K) (𝓞 L)) =
      ∏ i in Finset.range (p : ℕ), (X - C (polyRoot hp hζ u hcong α e i)) := by
  apply map_injective (algebraMap (𝓞 L) L) Subtype.coe_injective
  have : (algebraMap (𝓞 L) L).comp (algebraMap (𝓞 K) (𝓞 L)) = algebraMap (𝓞 K) L := by
    ext; rfl
  rw [← coe_mapRingHom, map_prod, coe_mapRingHom, map_map, this]
  rw [eq_prod_roots_of_monic_of_splits_id ((monic_poly hp hζ u hcong).map _)
    ((splits_id_iff_splits _).mpr (splits_poly hp hζ u hcong α e)), roots_poly hp hζ u hcong α e,
    Multiset.map_map]
  simp only [Polynomial.map_sub, map_X, map_C]
  rfl

lemma isIntegralClosure_of_isScalarTower (R A K L B) [CommRing R] [CommRing A] [CommRing K]
    [CommRing L] [CommRing B] [Algebra R K] [Algebra A K] [Algebra R L] [Algebra B L]
    [Algebra A L] [Algebra R A] [IsScalarTower R A K] [IsScalarTower R A L]
    [IsIntegralClosure A R K] [IsIntegralClosure B R L] :
    IsIntegralClosure B A L where
  algebraMap_injective' := IsIntegralClosure.algebraMap_injective B R L
  isIntegral_iff := fun {x} ↦ by
    refine Iff.trans ?_ (IsIntegralClosure.isIntegral_iff (R := R) (A := B) (B := L))
    have := (IsIntegralClosure.isIntegral_algebra R (A := A) K)
    exact ⟨isIntegral_trans x, IsIntegral.tower_top⟩

instance {K L} [Field K] [Field L] [Algebra K L] :
    IsIntegralClosure (𝓞 L) (𝓞 K) L := isIntegralClosure_of_isScalarTower ℤ _ K _ _

attribute [local instance 2000] Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction MulAction.toSMul NumberField.inst_ringOfIntegersAlgebra

instance {K L} [Field K] [Field L] [Algebra K L] :
    IsScalarTower (𝓞 K) (𝓞 L) L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

lemma minpoly_polyRoot'' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (i) :
    minpoly K (polyRoot hp hζ u hcong α e i : L) =
      (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) := by
  have : IsIntegral K (polyRoot hp hζ u hcong α e i : L) :=
    IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop
  apply eq_of_monic_of_associated (minpoly.monic this) ((monic_poly hp hζ u hcong).map _)
  refine Irreducible.associated_of_dvd (minpoly.irreducible this)
    (irreducible_map_poly hp hζ u hcong hu) (minpoly.dvd _ _ ?_)
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]
  exact aeval_poly hp hζ u hcong α e i

lemma minpoly_polyRoot' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (i) :
    minpoly (𝓞 K) (polyRoot hp hζ u hcong α e i : L) = (poly hp hζ u hcong) := by
  apply map_injective (algebraMap (𝓞 K) K) Subtype.coe_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K]
  exact minpoly_polyRoot'' hp hζ u hcong hu α e i
  exact IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop

lemma separable_poly_aux {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) : Separable ((poly hp hζ u hcong).map
    (algebraMap (𝓞 K) (𝓞 L))) := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_poly_eq_prod (e := e)]
  refine separable_prod' ?_ (fun _ _ => separable_X_sub_C)
  intros i hi j hj hij
  apply isCoprime_X_sub_C_of_isUnit_sub
  obtain ⟨v, hv⟩ :
      Associated (hζ.unit' - 1 : 𝓞 K) ((hζ.unit' : 𝓞 K) ^ j - (hζ.unit' : 𝓞 K) ^ i) := by
    refine hζ.unit'_coe.associated_sub_one hpri.out ?_ ?_ ?_
    · rw [mem_nthRootsFinset p.pos, ← pow_mul, mul_comm, pow_mul, hζ.unit'_coe.pow_eq_one, one_pow]
    · rw [mem_nthRootsFinset p.pos, ← pow_mul, mul_comm, pow_mul, hζ.unit'_coe.pow_eq_one, one_pow]
    · exact mt (hζ.unit'_coe.injOn_pow hj hi) hij.symm
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.unit') = ζ := rfl
  simp only [map_mul, map_sub, IsPrimitiveRoot.val_unit'_coe, map_one, map_pow, hcoe] at hv
  have hα : IsIntegral (𝓞 K) α := by
    apply IsIntegral.of_pow p.pos; rw [e]; exact isIntegral_algebraMap
  have : IsUnit (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) := by
    rw [← isUnit_pow_iff p.pos.ne.symm]
    convert (algebraMap (𝓞 K) (𝓞 L)).isUnit_map u.isUnit
    ext; simp only [SubmonoidClass.coe_pow, e]; rfl
  convert ((algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit).mul this using 1
  ext
  simp only [polyRoot, map_sub, map_one, sub_div, one_div, map_sub,
    sub_sub_sub_cancel_left, map_mul, NumberField.RingOfIntegers.map_mk]
  rw [← sub_div, ← sub_smul, ← hv, Algebra.smul_def, map_mul, map_sub, map_one, mul_assoc,
    mul_div_cancel_left₀ _ hζ']
  rfl

open scoped KummerExtension in
attribute [local instance] Ideal.Quotient.field in
lemma separable_poly (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Separable ((poly hp hζ u hcong).map (Ideal.Quotient.mk I)) := by
  let L := K[(p : ℕ)√(u : K)]
  letI := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let J := I.map (algebraMap (𝓞 K) (𝓞 L))
  letI : AddCommGroup (𝓞 L) := AddCommGroupWithOne.toAddCommGroup
  letI : Module (𝓞 K) (𝓞 L) := Algebra.toModule
  letI := Ideal.Quotient.commRing J
  let i : 𝓞 K ⧸ I →+* 𝓞 L ⧸ J := Ideal.quotientMap _
    (algebraMap (𝓞 K) (𝓞 L)) Ideal.le_comap_map
  haveI : Nontrivial (𝓞 L ⧸ J) := by
    apply Ideal.Quotient.nontrivial
    rw [ne_eq, Ideal.map_eq_top_iff]; exact Ideal.IsMaximal.ne_top ‹_›
    · intros x y e; ext; exact (algebraMap K L).injective (congr_arg Subtype.val e)
    · intros x; exact IsIntegral.tower_top (IsIntegralClosure.isIntegral ℤ L x)
  rw [← Polynomial.separable_map' i, map_map, Ideal.quotientMap_comp_mk, ← map_map]
  apply Separable.map
  apply separable_poly_aux hp hζ u hcong
  exact root_X_pow_sub_C_pow _ _

lemma polyRoot_spec {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (i) :
    α = (ζ ^ i)⁻¹ • (1 - (ζ - 1) • (polyRoot hp hζ u hcong α e i : L)) := by
  apply smul_right_injective (M := L) (c := ζ ^ i) (pow_ne_zero _ <| hζ.ne_zero p.pos.ne.symm)
  simp only [polyRoot, map_sub, map_one, NumberField.RingOfIntegers.map_mk,
    Algebra.smul_def (ζ - 1), ← mul_div_assoc,
    mul_div_cancel_left₀ _
      ((hζ.map_of_injective (algebraMap K L).injective).sub_one_ne_zero hpri.out.one_lt),
    sub_sub_cancel, smul_smul, inv_mul_cancel (pow_ne_zero _ <| hζ.ne_zero p.pos.ne.symm), one_smul]

lemma mem_adjoin_polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ (p : ℕ) = algebraMap K L u) (i) :
    α ∈ Algebra.adjoin K {(polyRoot hp hζ u hcong α e i : L)} := by
  conv_lhs => rw [polyRoot_spec hp hζ u hcong α e i]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _)
    (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton K _) _)) _

attribute [local instance] Ideal.Quotient.field in
lemma isUnramified (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ (p : ℕ) - C (u : K))] :
    IsUnramified (𝓞 K) (𝓞 L) := by
  let α := polyRoot hp hζ u hcong _ (rootOfSplitsXPowSubC_pow p.pos _ L) 0
  haveI := Polynomial.IsSplittingField.finiteDimensional L (X ^ (p : ℕ) - C (u : K))
  have hα : Algebra.adjoin K {(α : L)} = ⊤ := by
    rw [eq_top_iff, ← Algebra.adjoin_root_eq_top_of_isSplittingField
      ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ (X_pow_sub_C_irreducible_of_prime hpri.out hu)
      (rootOfSplitsXPowSubC_pow p.pos (u : K) L), Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact mem_adjoin_polyRoot hp hζ u hcong _ _ 0
  constructor
  intros I hI hIbot
  refine isUnramifiedAt_of_Separable_minpoly (R := 𝓞 K) K (S := 𝓞 L) L I hIbot α ?_ hα ?_
  · exact IsIntegral.tower_top α.prop
  · rw [minpoly_polyRoot' hp hζ u hcong hu]
    haveI := hI.isMaximal hIbot
    exact separable_poly hp hζ u hcong hu I

end KummersLemma
