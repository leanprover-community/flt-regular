
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.AuxLemmas
import FltRegular.NumberTheory.GaloisPrime
import Mathlib.Tactic.Widget.Conv

open scoped NumberField nonZeroDivisors
open FiniteDimensional Finset BigOperators Submodule

variable {K L : Type*} [Field K] [Field L] [NumberField K] [Algebra K L]
variable [IsGalois K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {η : L} (hη : Algebra.norm K η = 1)

--This is proved in #8599
theorem hilbert90 (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : ∀ (g h : (L ≃ₐ[K] L)), f (g * h) = g (f h) * f g) :
    ∃ β : Lˣ, ∀ g : (L ≃ₐ[K] L), f g * Units.map g β = β := by sorry

lemma ηunit : IsUnit η := by
  refine Ne.isUnit (fun h ↦ ?_)
  simp [h] at hη

noncomputable
def ηu : Lˣ := (ηunit hη).unit

noncomputable
def φ := (finEquivZpowers _ (isOfFinOrder_of_finite σ)).symm

variable {σ}

lemma hφ : ∀ (n : ℕ), φ σ ⟨σ ^ n, hσ _⟩ = n % (orderOf σ) := fun n ↦ by
  simpa [Fin.ext_iff] using
      @finEquivZpowers_symm_apply _ _ _ (isOfFinOrder_of_finite σ) n ⟨n, by simp⟩

noncomputable
def cocycle : (L ≃ₐ[K] L) → Lˣ := fun τ ↦ ∏ i in range (φ σ ⟨τ, hσ τ⟩), Units.map (σ ^ i) (ηu hη)

lemma foo {a b : ℕ} (h : a % orderOf σ = b % orderOf σ) :
    ∏ i in range a, (σ ^ i) (ηu hη) = ∏ i in range b, (σ ^ i) (ηu hη) := by
  sorry

lemma is_cocycle : ∀ (α β : (L ≃ₐ[K] L)), (cocycle hσ hη) (α * β) =
    α ((cocycle hσ hη) β) * (cocycle hσ hη) α := by
  intro α β
  have hσmon : ∀ x, x ∈ Submonoid.powers σ := by
    simpa [← mem_powers_iff_mem_zpowers] using hσ
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 (hσmon α)
  obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 (hσmon β)
  rw [← ha, ← hb, ← pow_add]
  have Hab := hφ (L := L) hσ (a + b)
  have Ha := hφ (L := L) hσ a
  have Hb := hφ (L := L) hσ b
  simp only [SetLike.coe_sort_coe, Nat.cast_add, Fin.ext_iff, Fin.mod_val, Fin.coe_ofNat_eq_mod,
    Nat.mod_self, Nat.mod_zero] at Hab Ha Hb
  simp only [cocycle, SetLike.coe_sort_coe, Units.coe_prod, Units.coe_map, MonoidHom.coe_coe,
    map_prod]
  rw [Hab, Ha, Hb, mul_comm]
  conv =>
    enter [2, 2, 2, x]
    rw [← AlgEquiv.mul_apply, ← pow_add]
  have H : ∀ n, σ ^ (a + n) = σ ^ (a % orderOf σ + n) := fun n ↦ by
    rw [pow_inj_mod]
    simp
  conv =>
    enter [2, 2, 2, x, 1]
    rw [H]
  rw [← prod_range_add (fun (n : ℕ) ↦ (σ ^ n) (ηu hη)) (a % orderOf σ) (b % orderOf σ)]
  apply foo
  simp

lemma Hilbert90 : ∃ ε : L, η = ε / σ ε := by
  by_cases hone : orderOf σ = 1
  · suffices finrank K L = 1 by
      obtain ⟨a, ha⟩ := mem_span_singleton.1 <| (eq_top_iff'.1 <|
        (finrank_eq_one_iff_of_nonzero _ one_ne_zero).1 this) η
      rw [← Algebra.algebraMap_eq_smul_one] at ha
      rw [← ha, Algebra.norm_algebraMap, this, pow_one] at hη
      exact ⟨1, by simp [← ha, hη]⟩
    rw [← IsGalois.card_aut_eq_finrank, Fintype.card_eq_one_iff]
    refine ⟨σ, fun τ ↦ ?_⟩
    simp only [orderOf_eq_one_iff.1 hone, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hσ
    rw [orderOf_eq_one_iff.1 hone, hσ τ]
  haveI nezero : NeZero (orderOf σ) :=
    ⟨fun hzero ↦ orderOf_eq_zero_iff.1 hzero (isOfFinOrder_of_finite σ)⟩
  have hfσ : (cocycle hσ hη) σ = (ηu hη) := by
    conv =>
      enter [1, 3]
      rw [← pow_one σ]
    have : 1 % orderOf σ = 1 := by
      suffices (orderOf σ).pred.pred + 2 = orderOf σ by
        rw [← this]
        exact Nat.one_mod _
      rw [← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, Nat.succ_pred, Nat.succ_pred nezero.1]
      intro h
      rw [show 0 = Nat.pred 1 by rfl] at h
      apply hone
      exact Nat.pred_inj (Nat.pos_of_ne_zero nezero.1) zero_lt_one h
    simp [this]
    have horder :=  hφ hσ 1
    simp only [SetLike.coe_sort_coe, pow_one] at horder
    simp only [cocycle, SetLike.coe_sort_coe, horder, this, range_one, prod_singleton, pow_zero]
    rfl
  obtain ⟨ε, hε⟩ := hilbert90 _ (is_cocycle hσ hη)
  use ε
  specialize hε σ
  rw [hfσ] at hε
  nth_rewrite 1 [← hε]
  simp
  rfl

variable {A B} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]
variable [IsIntegralClosure B A L] [IsDomain B]

lemma Hilbert90_integral (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    (η : B) (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K B L σ ε = ε := by
  haveI : NoZeroSMulDivisors A L := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization' A K L B
      (Algebra.isAlgebraic_iff_isIntegral.mpr <| Algebra.IsIntegral.of_finite (R := K) (B := L))
  obtain ⟨ε, hε⟩ := Hilbert90 hσ hη
  obtain ⟨x, y, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B A⁰) ε
  obtain ⟨t, ht, ht'⟩ := y.prop
  have : t • IsLocalization.mk' L x y = algebraMap _ _ x
  · rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, ne_eq, not_true, div_zero] at hε
    rw [hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · rw [eq_div_iff_mul_eq] at hε
    replace hε := congr_arg (t • ·) hε
    simp only at hε
    rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t, ← AlgHom.coe_coe,
      ← AlgHom.map_smul_of_tower, this] at hε
    apply IsIntegralClosure.algebraMap_injective B A L
    rw [map_mul, ← hε]
    congr 1
    exact algebraMap_galRestrictHom_apply A K B L σ x
    · intro e
      rw [(map_eq_zero _).mp e, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη
