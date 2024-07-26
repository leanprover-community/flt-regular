
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Widget.Conv
import Mathlib.RepresentationTheory.GroupCohomology.Hilbert90

open scoped nonZeroDivisors
open FiniteDimensional Finset BigOperators Submodule groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {η : L} (hη : Algebra.norm K η = 1)

noncomputable
def ηu : Lˣ := (Ne.isUnit (fun h ↦ by simp [h] at hη) : IsUnit η).unit

noncomputable
def φ := (finEquivZPowers _ (isOfFinOrder_of_finite σ)).symm

variable {σ}

lemma hφ : ∀ (n : ℕ), φ σ ⟨σ ^ n, hσ _⟩ = n % (orderOf σ) := fun n ↦ by
  simpa [Fin.ext_iff] using finEquivZPowers_symm_apply _ (isOfFinOrder_of_finite σ) n

noncomputable
def cocycle : (L ≃ₐ[K] L) → Lˣ := fun τ ↦ ∏ i in range (φ σ ⟨τ, hσ τ⟩), Units.map (σ ^ i) (ηu hη)

lemma foo {a: ℕ} (h : a % orderOf σ = 0) :
    ∏ i in range a, (σ ^ i) (ηu hη) = 1 := by
  obtain ⟨n, hn⟩ := (Nat.dvd_iff_mod_eq_zero _ _).2 h
  rw [hn]
  revert a
  induction n with
  | zero => simp
  | succ n ih =>
    intro a _ _
    rw [Nat.mul_succ, prod_range_add, ih (Nat.mul_mod_right (orderOf σ) n) rfl, one_mul]
    simp only [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
    have := Algebra.norm_eq_prod_automorphisms K η
    simp only [hη, map_one] at this
    convert this.symm
    refine prod_bij (fun (n : ℕ) (_ : n ∈ range (orderOf σ)) ↦ σ ^ n) (by simp)
      (fun a ha b hb hab ↦ ?_) (fun τ _ ↦ ?_) (fun _ _ ↦ by rfl)
    · rwa [pow_inj_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 ha),
        Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at hab
    · refine ⟨(finEquivZPowers _ (isOfFinOrder_of_finite σ)).symm ⟨τ, hσ τ⟩, by simp, ?_⟩
      have := Equiv.symm_apply_apply (finEquivZPowers _ (isOfFinOrder_of_finite σ)).symm ⟨τ, hσ τ⟩
      simp only [SetLike.coe_sort_coe, Equiv.symm_symm, ← Subtype.coe_inj] at this ⊢
      rw [← this]
      simp only [SetLike.coe_sort_coe, Subtype.coe_eta, Equiv.symm_apply_apply]
      rfl

lemma bar {a b : ℕ} (h : a % orderOf σ = b % orderOf σ) :
    ∏ i in range a, (σ ^ i) (ηu hη) = ∏ i in range b, (σ ^ i) (ηu hη) := by
  wlog hab : b ≤ a generalizing a b
  · exact (this h.symm (not_le.1 hab).le).symm
  obtain ⟨c, hc⟩ := (Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.sub_mod_eq_zero_of_mod_eq h)
  rw [Nat.sub_eq_iff_eq_add hab] at hc
  rw [hc, prod_range_add]
  rw [foo hσ hη (Nat.mul_mod_right (orderOf σ) c), one_mul]
  simp [pow_add, pow_mul, pow_orderOf_eq_one]

lemma cocycle_spec (hone : orderOf σ ≠ 1) : (cocycle hσ hη) σ = (ηu hη) := by
  haveI nezero : NeZero (orderOf σ) :=
    ⟨fun hzero ↦ orderOf_eq_zero_iff.1 hzero (isOfFinOrder_of_finite σ)⟩
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

lemma is_cocycle_aux : ∀ (α β : (L ≃ₐ[K] L)), (cocycle hσ hη) (α * β) =
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
    Nat.mod_self, Nat.mod_zero, cocycle, Units.coe_prod, Units.coe_map, MonoidHom.coe_coe,
    map_prod] at Hab Ha Hb ⊢
  rw [Hab, Ha, Hb, mul_comm]
  have H : ∀ n, σ ^ (a + n) = σ ^ (a % orderOf σ + n) := fun n ↦ by simp [pow_inj_mod]
  conv =>
    enter [2, 2, 2, x]
    rw [← AlgEquiv.mul_apply, ← pow_add, H]
  rw [← prod_range_add (fun (n : ℕ) ↦ (σ ^ n) (ηu hη)) (a % orderOf σ) (b % orderOf σ)]
  simpa using bar hσ hη (by simp)

lemma is_cocycle : IsMulOneCocycle (cocycle hσ hη) := by
  intro α β
  simp [← Units.eq_iff, is_cocycle_aux hσ hη α β]

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
  obtain ⟨ε, hε⟩ := isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units _ (is_cocycle hσ hη)
  use ε⁻¹
  simp only [map_inv₀, div_inv_eq_mul]
  specialize hε σ
  nth_rewrite 2 [← inv_inv ε] at hε
  rw [div_inv_eq_mul, cocycle_spec hσ hη hone, mul_inv_eq_iff_eq_mul, mul_comm,
    ← Units.eq_iff] at hε
  simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, Units.val_mul] at hε
  symm
  rw [inv_mul_eq_iff_eq_mul₀ ε.ne_zero, hε]
  rfl


variable {A B} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]
variable [IsIntegralClosure B A L] [IsDomain B]

lemma Hilbert90_integral (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    (η : B) (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K L B σ ε = ε := by
  haveI : NoZeroSMulDivisors A L := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  obtain ⟨ε, hε⟩ := Hilbert90 hσ hη
  obtain ⟨x, y, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B A⁰) ε
  obtain ⟨t, ht, ht'⟩ := y.prop
  have : t • IsLocalization.mk' L x y = algebraMap _ _ x := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, ne_eq, not_true, div_zero] at hε
    rw [hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · rw [eq_div_iff_mul_eq] at hε
    replace hε := congr_arg (t • ·) hε
    simp only at hε
    rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t] at hε
    change (algebraMap B L) η * t • σ.toAlgHom _ = _ at hε
    rw [← AlgHom.map_smul_of_tower, this] at hε
    apply IsIntegralClosure.algebraMap_injective B A L
    rw [map_mul, ← hε]
    congr 1
    exact algebraMap_galRestrictHom_apply A K L B σ x
    · intro e
      rw [(map_eq_zero _).mp e, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη
