import FltRegular.NumberTheory.Cyclotomic.CyclotomicUnits
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Units.Basic

universe u

open FiniteDimensional

open scoped NumberField

theorem PowerBasis.rat_hom_ext {S S' : Type _} [CommRing S] [hS : Algebra ℚ S] [Ring S']
    [hS' : Algebra ℚ S'] (pb : PowerBasis ℚ S) ⦃f g : S →+* S'⦄ (h : f pb.gen = g pb.gen) : f = g :=
  let f' := f.toRatAlgHom
  let g' := g.toRatAlgHom
  DFunLike.ext f g <| by
    convert DFunLike.ext_iff.mp (pb.algHom_ext (show f' pb.gen = g' pb.gen from h))

variable (K : Type _) (p : ℕ+) [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation "RR" => 𝓞 K

-- @Chris: you mentioned "checking automorphisms agree only on a generator" -
-- what you want is `power_basis.alg_hom_ext`
open scoped NumberField Cyclotomic

open IsCyclotomicExtension Polynomial

noncomputable section

/-- complex conjugation as a Galois automorphism -/
def galConj : K ≃ₐ[ℚ] K :=
  (autEquivPow K (cyclotomic.irreducible_rat p.pos)).symm (-1)

variable {K p}

theorem ZMod.val_neg_one' : ∀ {n : ℕ}, 0 < n → (-1 : ZMod n).val = n - 1
  | _ + 1, _ => ZMod.val_neg_one _

theorem galConj_zeta : galConj K p (zeta p ℚ K) = (zeta p ℚ K)⁻¹ :=
  by
  let hζ := zeta_spec p ℚ K
  simp only [galConj, Units.coe_neg_one, autEquivPow_symm_apply, AlgEquiv.coe_algHom,
    PowerBasis.equivOfMinpoly_apply]
  convert (hζ.powerBasis ℚ).lift_gen (S' := K) _ _
  rw [IsPrimitiveRoot.powerBasis_gen, ZMod.val_neg_one' p.pos,
    pow_sub₀ _ (hζ.ne_zero p.ne_zero) p.pos, pow_one, hζ.pow_eq_one, one_mul]

@[simp]
theorem galConj_zeta_runity : galConj K p ζ = ζ⁻¹ :=
  by
  obtain ⟨t, _, rfl⟩ := (zeta_spec p ℚ K).eq_pow_of_pow_eq_one hζ.pow_eq_one p.pos
  rw [map_pow, galConj_zeta, inv_pow]

theorem galConj_zeta_runity_pow (n : ℕ) : galConj K p (ζ ^ n) = ζ⁻¹ ^ n := by
  rw [map_pow, galConj_zeta_runity hζ]

open scoped ComplexConjugate

theorem conj_norm_one (x : ℂ) (h : Complex.abs x = 1) : conj x = x⁻¹ := by
  rw [← Complex.abs_mul_exp_arg_mul_I x, h, Complex.ofReal_one, one_mul, ← Complex.exp_conj, ←
    Complex.exp_neg, map_mul, Complex.conj_I, mul_neg, Complex.conj_ofReal]

@[simp]
theorem embedding_conj (x : K) (φ : K →+* ℂ) : conj (φ x) = φ (galConj K p x) :=
  by
  -- dependent type theory is my favourite
  change RingHom.comp conj φ x = (φ.comp <| ↑(galConj K p)) x
  revert x
  suffices φ (galConj K p ζ) = conj (φ ζ)
    by
    rw [← Function.funext_iff]
    rw [DFunLike.coe_fn_eq]
    apply (hζ.powerBasis ℚ).rat_hom_ext
    exact this.symm
  rw [conj_norm_one, galConj_zeta_runity hζ, map_inv₀]
  refine' Complex.norm_eq_one_of_pow_eq_one _ p.ne_zero
  rw [← map_pow, hζ.pow_eq_one, map_one]

variable (p)

--generalize this
theorem gal_map_mem {x : K} (hx : IsIntegral ℤ x) (σ : K →ₐ[ℚ] K) : IsIntegral ℤ (σ x) :=
  map_isIntegral_int (σ.restrictScalars ℤ) hx

theorem gal_map_mem_subtype (σ : K →ₐ[ℚ] K) (x : RR) : IsIntegral ℤ (σ x) :=
  gal_map_mem x.2 _

/-- Restriction of `σ : K →ₐ[ℚ] K` to the ring of integers.  -/
def intGal (σ : K →ₐ[ℚ] K) : RR →ₐ[ℤ] RR :=
  ((σ.restrictScalars ℤ).restrictDomain RR).codRestrict (integralClosure ℤ K)
  (gal_map_mem_subtype σ)

@[simp]
theorem intGal_apply_coe (σ : K →ₐ[ℚ] K) (x : RR) : (intGal σ x : K) = σ x :=
  rfl

/-- Restriction of `σ : K →ₐ[ℚ] K` to the units of the ring of integers.  -/
def unitsGal (σ : K →ₐ[ℚ] K) : RRˣ →* RRˣ :=
  Units.map <| intGal σ

variable (K)

/-- `unit_gal_conj` as a bundled hom. -/
def unitGalConj : RRˣ →* RRˣ :=
  unitsGal (galConj K p)

theorem unitGalConj_spec (u : RRˣ) : galConj K p u = unitGalConj K p u := rfl

variable {K}

theorem unit_lemma_val_one (u : RRˣ) (φ : K →+* ℂ) :
    Complex.abs (φ (u * (unitGalConj K p u)⁻¹)) = 1 := by
  rw [map_mul, IsAbsoluteValue.abv_mul Complex.abs, ← zpow_neg_one, NumberField.Units.coe_zpow,
    zpow_neg_one, map_inv₀, ← unitGalConj_spec,
    ← embedding_conj <| zeta_spec p ℚ K]
  simp only [map_inv₀, Complex.abs_conj]
  rw [mul_inv_eq_one₀]
  intro h
  simp at h
