import number_theory.cyclotomic.cyclotomic_units

import number_theory.cyclotomic.gal

universes u

open finite_dimensional

open_locale number_field

theorem power_basis.rat_hom_ext {S S' : Type*} [comm_ring S] [hS : algebra ℚ S] [ring S']
  [hS' : algebra ℚ S'] (pb : power_basis ℚ S) ⦃f g : S →+* S'⦄ (h : f pb.gen = g pb.gen) :
f = g :=
let f' := f.to_rat_alg_hom, g' := g.to_rat_alg_hom in
fun_like.ext f g $
by convert fun_like.ext_iff.mp (pb.alg_hom_ext (show f' pb.gen = g' pb.gen, from h))

variables (K : Type*) (p : ℕ+) [field K] [char_zero K] [is_cyclotomic_extension {p} ℚ K]
variables {ζ : K} (hζ : is_primitive_root ζ p)

local notation `RR` := 𝓞 K

-- @Chris: you mentioned "checking automorphisms agree only on a generator" -
-- what you want is `power_basis.alg_hom_ext`

open_locale number_field cyclotomic

open is_cyclotomic_extension polynomial

noncomputable theory

/-- complex conjugation as a Galois automorphism -/
def gal_conj : K ≃ₐ[ℚ] K :=
((aut_equiv_pow K (cyclotomic.irreducible_rat p.pos)).symm (-1))

variables {K p}

lemma zmod.val_neg_one' : ∀ {n : ℕ}, 0 < n → (-1 : zmod n).val = n - 1
| (n + 1) _ := zmod.val_neg_one _

lemma gal_conj_zeta : gal_conj K p (zeta p ℚ K) = (zeta p ℚ K)⁻¹ :=
begin
  let hζ := zeta_spec p ℚ K,
  simp only [gal_conj, units.coe_neg_one, aut_equiv_pow_symm_apply, alg_equiv.coe_alg_hom,
             power_basis.equiv_of_minpoly_apply],
  convert (hζ.power_basis ℚ).lift_gen _ _,
  rw [is_primitive_root.power_basis_gen, zmod.val_neg_one' p.pos,
      pow_sub₀ _ (hζ.ne_zero p.ne_zero) p.pos, pow_one, hζ.pow_eq_one, one_mul]
end

include hζ

@[simp] lemma gal_conj_zeta_runity : gal_conj K p ζ = ζ⁻¹ :=
begin
  obtain ⟨t, ht, rfl⟩ := (zeta_spec p ℚ K).eq_pow_of_pow_eq_one hζ.pow_eq_one p.pos,
  rw [map_pow, gal_conj_zeta, inv_pow]
end

lemma gal_conj_zeta_runity_pow (n : ℕ) :  gal_conj K p (ζ^n) = (ζ⁻¹)^n :=
by rw [map_pow, gal_conj_zeta_runity hζ]

omit hζ

open_locale complex_conjugate

lemma conj_norm_one (x : ℂ) (h : complex.abs x = 1) : conj x = x⁻¹ :=
by rw [←complex.abs_mul_exp_arg_mul_I x, h, complex.of_real_one, one_mul, ←complex.exp_conj,
       ←complex.exp_neg, map_mul, complex.conj_I, mul_neg, complex.conj_of_real]

include hζ

@[simp]
lemma embedding_conj (x : K) (φ : K →+* ℂ) : conj (φ x) = φ (gal_conj K p x) :=
begin
  -- dependent type theory is my favourite
  change (ring_hom.comp conj φ x) = (φ.comp $ ↑(gal_conj K p)) x,
  revert x,
  suffices : φ (gal_conj K p ζ) = conj (φ ζ),
  { rw ←function.funext_iff,
    dsimp only,
    congr' 1,
    apply (hζ.power_basis ℚ).rat_hom_ext,
    { exact this.symm },
    { exact algebra_rat } },
  rw [conj_norm_one, gal_conj_zeta_runity hζ, map_inv₀],
  refine complex.norm_eq_one_of_pow_eq_one _ p.ne_zero,
  rw [←map_pow, hζ.pow_eq_one, map_one]
end

omit hζ

-- this proof makes me happy inside
lemma gal_conj_idempotent : (gal_conj K p).trans (gal_conj K p) = alg_equiv.refl :=
begin
  rw [←alg_equiv.aut_mul, gal_conj, ←map_mul, neg_one_mul, neg_neg, map_one],
  refl,
end

variable (p)

--generalize this
lemma gal_map_mem {x : K} (hx : x ∈ RR) (σ : K →ₐ[ℚ] K) : σ x ∈ RR :=
map_is_integral (σ.restrict_scalars ℤ) hx

lemma gal_map_mem_subtype (σ : K →ₐ[ℚ] K) (x : RR) : σ x ∈ RR :=
by simp [gal_map_mem]

/-- Restriction of `σ : K →ₐ[ℚ] K` to the ring of integers.  -/
def int_gal (σ : K →ₐ[ℚ] K) : RR →ₐ[ℤ] RR :=
((σ.restrict_scalars ℤ).restrict_domain RR).cod_restrict RR (gal_map_mem_subtype σ)

@[simp] lemma int_gal_apply_coe (σ : K →ₐ[ℚ] K) (x : RR) :
  (int_gal σ x : K) = σ x := rfl

/-- Restriction of `σ : K →ₐ[ℚ] K` to the units of the ring of integers.  -/
def units_gal (σ : K →ₐ[ℚ] K) : RRˣ →* RRˣ :=
units.map $ int_gal σ

@[simp] lemma units_gal_apply_coe (σ : K →ₐ[ℚ] K) (x : RRˣ) :
(units_gal σ x : K) = σ x := rfl

/-- `unit_gal_conj` as a bundled hom. -/
def unit_gal_conj : RRˣ →* RRˣ :=
units_gal (gal_conj K p)

lemma unit_gal_conj_spec (u : RRˣ) : gal_conj K p (u : 𝓞 K) = ↑(unit_gal_conj K p u : 𝓞 K) := rfl

lemma uni_gal_conj_inv (u : RRˣ) : (unit_gal_conj K p u)⁻¹ = (unit_gal_conj K p u⁻¹) := rfl

lemma unit_lemma_val_one (u : RRˣ) (φ : K →+* ℂ) :
  complex.abs (φ (u * (unit_gal_conj K p u)⁻¹)) = 1 :=
begin
  rw [map_mul, complex.abs.is_absolute_value.abv_mul, map_inv₀,
      coe_coe (unit_gal_conj K p u), ←unit_gal_conj_spec, ←embedding_conj $ zeta_spec p ℚ K],
  simp only [coe_coe, map_inv₀, complex.abs_conj],
  rw [mul_inv_eq_one₀],
  intro h,
  simp only [_root_.map_eq_zero] at h,
  rw [← subalgebra.coe_zero (𝓞 K), subtype.coe_inj] at h,
  refine units.ne_zero _ h
end

lemma unit_gal_conj_idempotent (u : RRˣ) : (unit_gal_conj K p (unit_gal_conj K p u)) = u :=
units.ext $ subtype.ext $ by rw [←unit_gal_conj_spec, ←unit_gal_conj_spec, ←alg_equiv.trans_apply,
                                 gal_conj_idempotent, alg_equiv.coe_refl, id]
