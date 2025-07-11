import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Units.Basic

open FiniteDimensional

open scoped NumberField


variable (K : Type*) (p : ℕ) [NeZero p] [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation "RR" => 𝓞 K

open scoped NumberField Cyclotomic

open IsCyclotomicExtension Polynomial

noncomputable section

/-- complex conjugation as a Galois automorphism -/
def galConj : K ≃ₐ[ℚ] K :=
  (autEquivPow K (cyclotomic.irreducible_rat (NeZero.pos p))).symm (-1)

variable {K p}

theorem ZMod.val_neg_one' : ∀ {n : ℕ}, 0 < n → (-1 : ZMod n).val = n - 1
  | _ + 1, _ => ZMod.val_neg_one _

theorem galConj_zeta : galConj K p (zeta p ℚ K) = (zeta p ℚ K)⁻¹ := by
  let hζ := zeta_spec p ℚ K
  simp only [galConj, Units.coe_neg_one, autEquivPow_symm_apply, PowerBasis.equivOfMinpoly_apply]
  convert (hζ.powerBasis ℚ).lift_gen (S' := K) _ _
  rw [IsPrimitiveRoot.powerBasis_gen, ZMod.val_neg_one' (NeZero.pos p),
    pow_sub₀ _ (hζ.ne_zero (NeZero.ne p)) (NeZero.pos p), pow_one, hζ.pow_eq_one, one_mul]

include hζ in
@[simp]
theorem galConj_zeta_runity : galConj K p ζ = ζ⁻¹ := by
  obtain ⟨t, _, rfl⟩ := (zeta_spec p ℚ K).eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [map_pow, galConj_zeta, inv_pow]

include hζ in
theorem galConj_zeta_runity_pow (n : ℕ) : galConj K p (ζ ^ n) = ζ⁻¹ ^ n := by
  rw [map_pow, galConj_zeta_runity hζ]

open scoped ComplexConjugate

include hζ in
@[simp]
theorem embedding_conj (x : K) (φ : K →+* ℂ) : conj (φ x) = φ (galConj K p x) := by
  change RingHom.comp conj φ x = (φ.comp (galConj K p)) x
  revert x
  suffices φ (galConj K p ζ) = conj (φ ζ) by
    rw [← funext_iff, DFunLike.coe_fn_eq, ← ((starRingEnd ℂ).comp φ).toRatAlgHom_toRingHom,
      ← (φ.comp ↑(galConj K p)).toRatAlgHom_toRingHom (R := K)]
    congr 1
    apply (hζ.powerBasis ℚ).algHom_ext
    exact this.symm
  rw [← Complex.inv_eq_conj, galConj_zeta_runity hζ, map_inv₀]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne p)

variable (p)

theorem gal_map_mem_subtype (σ : K →ₐ[ℚ] K) (x : RR) : IsIntegral ℤ (σ x) :=
  map_isIntegral_int _ x.2

/-- Restriction of `σ : K →ₐ[ℚ] K` to the ring of integers. -/
def intGal (σ : K →ₐ[ℚ] K) : RR →ₐ[ℤ] RR :=
  ((σ.restrictScalars ℤ).restrictDomain RR).codRestrict (integralClosure ℤ K)
  (gal_map_mem_subtype σ)

@[simp]
theorem intGal_apply_coe (σ : K →ₐ[ℚ] K) (x : RR) : (intGal σ x : K) = σ x :=
  rfl

/-- Restriction of `σ : K →ₐ[ℚ] K` to the units of the ring of integers. -/
def unitsGal (σ : K →ₐ[ℚ] K) : RRˣ →* RRˣ :=
  Units.map <| intGal σ

variable (K)

/-- `unit_gal_conj` as a bundled hom. -/
def unitGalConj : RRˣ →* RRˣ :=
  unitsGal (galConj K p)

theorem unitGalConj_spec (u : RRˣ) : galConj K p u = unitGalConj K p u := rfl

variable {K}

theorem unit_lemma_val_one (u : RRˣ) (φ : K →+* ℂ) :
    ‖φ (u * (unitGalConj K p u)⁻¹)‖ = 1 := by
  rw [map_mul, norm_mul, ← zpow_neg_one, NumberField.Units.coe_zpow,
    zpow_neg_one, map_inv₀, ← unitGalConj_spec,
    ← embedding_conj <| zeta_spec p ℚ K]
  simp
